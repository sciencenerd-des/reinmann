"""Certified eigenvectors and finite, same-support mode comparison.

A comparison of two cutoffs is not a bound on the omitted infinite tail.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
from flint import arb, arb_mat, ctx
from certified_weil import endpoints, inertia


def box(record):
    return arb(record['lo']).union(arb(record['hi']))


def normalized_vector(certificate):
    if certificate.get('status')!='certified_finite_weil_gates':
        raise ValueError('certified finite gates required')
    N=certificate['modes']
    A=[[box(x) for x in row] for row in certificate['matrix']]
    if len(A)!=2*N+1 or any(len(row)!=2*N+1 for row in A):
        raise ValueError('matrix dimension mismatch')
    even=[[arb(0) for _ in range(N+1)] for _ in range(N+1)]
    even[0][0]=A[N][N]
    root2=arb(2).sqrt()
    for i in range(1,N+1):
        even[0][i]=even[i][0]=root2*A[N][N+i]
        for j in range(1,N+1):
            even[i][j]=A[N+i][N+j]+A[N+i][N-j]
    lam=box(certificate['smallest_even_eigenvalue'])
    shifted=[[even[i][j]-(lam if i==j else 0) for j in range(N+1)] for i in range(N+1)]
    kernel=[[shifted[i][j]-root2*(shifted[i][0]+shifted[0][j])+2*shifted[0][0]
             for j in range(1,N+1)] for i in range(1,N+1)]
    if inertia(kernel)[0]!=0:
        raise ArithmeticError('positive boundary kernel unresolved')
    rhs=arb_mat([[-shifted[i][0]+root2*shifted[0][0]] for i in range(1,N+1)])
    y=arb_mat(kernel).solve(rhs)
    vector=[1-root2*sum((y[i,0] for i in range(N)),arb(0))]+[y[i,0] for i in range(N)]
    if not all(x.is_finite() for x in vector):
        raise ArithmeticError('eigenvector enclosure unresolved')
    norm=sum((x*x for x in vector),arb(0)).sqrt()
    if not norm>0 or vector[0].contains(0):
        raise ArithmeticError('unit or Fourier-origin normalization unresolved')
    unit=[x/norm for x in vector]
    # Orthonormal even coordinates; divide by c0 for Fourier value at zero=1.
    origin=[arb(1)]+[x/vector[0] for x in vector[1:]]
    return vector,unit,origin


def compare(first,second,radius=1):
    if first['cutoff']!=second['cutoff'] or not first['modes']<second['modes']:
        raise ValueError('strictly nested mode spaces at the same support required')
    T=arb(radius)
    if not T.is_finite() or not T>=0:
        raise ValueError('finite nonnegative complex disk radius required')
    v1,u1,f1=normalized_vector(first)
    v2,u2,f2=normalized_vector(second)
    padding=[arb(0)]*(len(u2)-len(u1))
    u1=u1+padding
    f1=f1+padding
    inner=sum((x*y for x,y in zip(u1,u2)),arb(0))
    distance=sum(((x-y)**2 for x,y in zip(u1,u2)),arb(0)).sqrt()
    origin_distance=sum(((x-y)**2 for x,y in zip(f1,f2)),arb(0)).sqrt()
    L=arb(first['cutoff']).log()
    compact_bound=(T*L/2).exp()*origin_distance
    energy_ratio=(box(first['smallest_even_eigenvalue'])-box(second['smallest_even_eigenvalue']))/box(second['spectral_gap'])
    return {'schema_version':1,'status':'certified_finite_nested_mode_comparison_not_convergence',
            'cutoff':first['cutoff'],'mode_pair':[first['modes'],second['modes']],
            'boundary_normalized_even_vectors':[[endpoints(x) for x in v] for v in (v1,v2)],
            'unit_vector_inner_product':endpoints(inner),'unit_vector_distance':endpoints(distance),
            'origin_normalized_coefficient_distance':endpoints(origin_distance),
            'complex_disk_radius':str(T.fmpq()),
            'entire_profile_difference_upper':str(compact_bound.upper().fmpq()),
            'rayleigh_excess_over_certified_gap':endpoints(energy_ratio),
            'remaining':'No estimate for subsequent mode cutoffs or increasing support; no convergence to Xi is established.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--first',type=Path,required=True)
    parser.add_argument('--second',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    with ctx.workprec(512):
        sources=[]
        for path in (args.first,args.second):
            data=json.loads(path.read_text())
            for name,digest in data['source_hashes'].items():
                if hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()!=digest:
                    raise ValueError('stale source certificate')
            sources.append(data)
        result=compare(*sources)
        result['input_hashes']=[hashlib.sha256(p.read_bytes()).hexdigest() for p in (args.first,args.second)]
        result['source_hash']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n')
        print(result['status'])
        for key in ('unit_vector_distance','origin_normalized_coefficient_distance','rayleigh_excess_over_certified_gap'):
            print(key,box(result[key]))


if __name__=='__main__':
    main()
