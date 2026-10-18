"""Arb range-quadrature cost pilot for the hard centre; no Lean tile timing."""
import argparse,hashlib,json,time
from pathlib import Path
from flint import arb,ctx

def run(output):
    ctx.prec=160
    rows=[]
    for count in [128,512,2048,8192,32768]:
        start=time.monotonic();width=arb(3)/count;total=arb(0)
        for i in range(count):
            t=arb(arb(1)+(arb(i)+arb("1/2"))*width,width/2)
            log=t.log()
            f=2*(-arb.pi()*t).exp()*(log*arb("-3/4")).exp()*(7*log).cos()
            total+=f*width
        diameter=2*total.rad()
        target=arb("1/100000000")
        rows.append({'panels':count,'interval':str(total),'width':str(diameter),
                     'target_met':bool(diameter<target),'seconds':time.monotonic()-start,
                     'linear_count_projection':str(count*diameter/target)})
    result={'status':'external_range_quadrature_cost_pilot','domain':['1','4'],
            'centre':['1/2','14'],'theta_terms':1,'moment_component':0,
            'target_integral_width':'1/100000000','rows':rows,
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'scope':'Only the first theta term and central real Mellin component on [1,4]. Extrapolation is descriptive engineering evidence, not a lower bound on all methods, a certified Xi tile, or a Lean runtime.'}
    output.parent.mkdir(parents=True,exist_ok=True);output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);run(p.parse_args().output)
