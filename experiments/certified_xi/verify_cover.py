"""Validate a cover's rational partition and extract certified subintervals.

Checks artifact consistency, not FLINT's computations or source authenticity.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path


def verify_mean_value(cell):
    """Check the rational witness; quadrature and derivative bounds remain trusted."""
    a,b=Fraction(cell['lo']),Fraction(cell['hi'])
    radius=Fraction(cell['variation_radius'])
    d0,d1=Fraction(cell['derivative_G']['lo']),Fraction(cell['derivative_G']['hi'])
    m0,m1=Fraction(cell['midpoint_G']['lo']),Fraction(cell['midpoint_G']['hi'])
    g0,g1=Fraction(cell['G']['lo']),Fraction(cell['G']['hi'])
    if not d0<=d1 or not m0<=m1 or radius<(b-a)/2*max(abs(d0),abs(d1)):
        raise ValueError('invalid mean-value derivative radius')
    if not g0<=m0-radius<=m1+radius<=g1:
        raise ValueError('G does not contain the mean-value enclosure')


def summarize(data):
    lo,hi=map(Fraction,data['domain'])
    if not lo<hi:
        raise ValueError('empty or reversed domain')
    position=lo
    intervals=[]
    start=None
    counts={'positive':0,'negative':0,'unresolved':0}
    for cell in data['cells']:
        a,b=Fraction(cell['lo']),Fraction(cell['hi'])
        if a!=position or not a<b or b>hi:
            raise ValueError('invalid partition ordering or coverage')
        status=cell['status']
        if status not in counts:
            raise ValueError('unknown cell status')
        counts[status]+=1
        if data.get('method')=='coupled_G_derivative_mean_value' and (status!='unresolved' or 'G' in cell):
            verify_mean_value(cell)
        if status=='positive':
            g0,g1=Fraction(cell['G']['lo']),Fraction(cell['G']['hi'])
            c0,c1=Fraction(cell['log_epsilon_second']['lo']),Fraction(cell['log_epsilon_second']['hi'])
            if not 0<g0<=g1 or not c0<=c1<0:
                raise ValueError('positive label contradicts serialized bounds')
            if start is None:
                start=a
        else:
            if status=='negative':
                g0,g1=Fraction(cell['G']['lo']),Fraction(cell['G']['hi'])
                c0,c1=Fraction(cell['log_epsilon_second']['lo']),Fraction(cell['log_epsilon_second']['hi'])
                if not g0<=g1<0 or not 0<c0<=c1:
                    raise ValueError('negative label contradicts serialized bounds')
            if start is not None:
                intervals.append([str(start),str(a)])
                start=None
        position=b
    if position!=hi:
        raise ValueError('missing terminal coverage')
    if start is not None:
        intervals.append([str(start),str(hi)])
    complete=counts['negative']==counts['unresolved']==0
    expected='certified_finite_interval' if complete else 'incomplete_cover'
    if data['status']!=expected:
        raise ValueError('overall status contradicts cells')
    return {'domain':data['domain'],'overall_status':expected,'cell_counts':counts,
            'certified_subintervals':intervals,
            'boundary':'Consistency check only; the numerical derivation is trusted or must be replayed.'}


def summarize_union(inputs):
    """Join complete adjacent covers with the same numerical provenance."""
    if not inputs:
        raise ValueError('no covers supplied')
    covers=[]
    hashes={}
    for name,raw in inputs:
        if name in hashes:
            raise ValueError('duplicate cover name')
        cover=json.loads(raw)
        if summarize(cover)['overall_status']!='certified_finite_interval':
            raise ValueError('incomplete cover in union')
        covers.append(cover)
        hashes[name]=hashlib.sha256(raw).hexdigest()
    method=covers[0].get('method')
    sources=covers[0].get('source_hashes')
    settings=('bits','theta_terms','left_log_cutoff','upper_u_cutoff')
    if method!='coupled_G_derivative_mean_value' or not isinstance(sources,dict) or not sources:
        raise ValueError('union requires coupled covers with source hashes')
    if any(covers[0].get(key) is None for key in settings):
        raise ValueError('missing numerical cover settings')
    for previous,current in zip(covers,covers[1:]):
        if Fraction(previous['domain'][1])!=Fraction(current['domain'][0]):
            raise ValueError('nonadjacent cover domains')
    if any(cover.get('method')!=method or cover.get('source_hashes')!=sources
           or any(cover.get(key)!=covers[0].get(key) for key in settings)
           for cover in covers):
        raise ValueError('incompatible cover provenance')
    cells=[cell for cover in covers for cell in cover['cells']]
    combined={'domain':[covers[0]['domain'][0],covers[-1]['domain'][1]],
              'status':'certified_finite_interval','method':method,'cells':cells}
    result=summarize(combined)
    result['input_sha256']=hashes
    result['uniform_negative_log_curvature_margin']=str(min(
        -Fraction(cell['log_epsilon_second']['hi']) for cell in cells))
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='+')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    try:
        inputs=[(path.name,path.read_bytes()) for path in args.input]
        if len(inputs)==1:
            result=summarize(json.loads(inputs[0][1]))
            result['input_sha256']=hashlib.sha256(inputs[0][1]).hexdigest()
        else:
            result=summarize_union(inputs)
    except (ValueError,KeyError,OSError) as exc:
        parser.error(str(exc))
    rendered=json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(rendered)
    print(rendered,end='')

if __name__=='__main__':
    main()
