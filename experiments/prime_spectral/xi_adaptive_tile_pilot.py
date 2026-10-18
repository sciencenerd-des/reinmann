"""Arb pilot for adaptive quarter-rectangle tiles; not a Lean certificate.

Derivative estimates use point Taylor jets plus a written Cauchy bound on the
unit disk. The global majorant is proved in XiLocalCauchy; the point-jet
coefficient/evaluator bridge and derivative-series tail still require Lean proofs. This does not discharge ZetaNoLowStripZero.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse,json,time,hashlib
from flint import arb,acb,acb_series,ctx

def ar(q):return arb(str(q))
def xi_jet(z):
 s=acb_series([z,1]);return s*(s/2).gamma()*(-s*arb.pi().log()/2).exp()*(1+(s-1)*s.zeta(deflate=True))/2

def run(output,mode,max_tiles):
 ctx.prec=192;ctx.cap=17;start=time.monotonic();stack=[(F(1,2),F(1),F(0),F(141,10),0)];accepted=[];attempts=0;worst_depth=0
 while stack:
  if attempts>=max_tiles:break
  x0,x1,y0,y1,depth=stack.pop();attempts+=1;worst_depth=max(worst_depth,depth)
  xc=(x0+x1)/2;yc=(y0+y1)/2;rx=(x1-x0)/2;ry=(y1-y0)/2;rho=(ar(rx)**2+ar(ry)**2).sqrt();c=acb(ar(xc),ar(yc));jet=xi_jet(c);value=abs(jet[0]);K=None
  if rho<1:
   if mode=='taylor':
    K=sum((n*abs(jet[n])*rho**(n-1) for n in range(1,17)),arb(0))
    # |a_n|<=1000: XiLocalCauchy.taylor_coefficient_bound.
    # This external Taylor-tail calculation is not yet connected to Lean jets.
    K+=1000*rho**16*(17-16*rho)/(1-rho)**2
   else:
    old=ctx.cap;ctx.cap=2
    try:K=abs(xi_jet(acb(arb(ar(xc),ar(rx)),arb(ar(yc),ar(ry))))[1])
    finally:ctx.cap=old
  # Reserve 1/8 of |Xi(c)| for a future Lean centre-evaluation error.
  if K is not None and K.is_finite() and 0<=K and K*rho < value*ar(F(7,8)):
   accepted.append({'box':[str(q) for q in [x0,x1,y0,y1]],'centre':[str(xc),str(yc)],'radius_upper':str(rho.upper()),'value_abs_lower':str(value.lower()),'derivative_upper':str(K.upper()),'remaining_margin_lower':str((value*ar(F(7,8))-K*rho).lower()),'depth':depth})
  elif depth>=24:raise RuntimeError('Depth limit reached; do not claim complete cover')
  elif x1-x0>=y1-y0:
   mid=(x0+x1)/2;stack.extend([(x0,mid,y0,y1,depth+1),(mid,x1,y0,y1,depth+1)])
  else:
   mid=(y0+y1)/2;stack.extend([(x0,x1,y0,mid,depth+1),(x0,x1,mid,y1,depth+1)])
  if attempts%200==0:print(mode,'attempts',attempts,'accepted',len(accepted),'pending',len(stack),flush=True)
 result={'status':'arb_adaptive_count_pilot_complete' if not stack else 'arb_adaptive_count_pilot_budget_exhausted','mode':mode,'quarter':['1/2','1','0','141/10'],'bits':ctx.prec,'jet_degree':16,'global_unit_disk_majorant':1000,'majorant_status':'Proved by XiLocalCauchy.unit_circle_bound and taylor_coefficient_bound; jet and derivative-tail bridge remains external.','centre_error_budget_relative':'1/8','tiles':len(accepted),'attempts':attempts,'pending':len(stack),'max_depth':worst_depth,'seconds':time.monotonic()-start,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'External Arb pilot for cost and geometry. No Lean centre enclosure, local derivative certificate, finite cover proof or zero-free rectangle theorem is supplied by this script.','accepted':accepted}
 output.parent.mkdir(parents=True,exist_ok=True);output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='accepted'},indent=2))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);p.add_argument('--mode',choices=['taylor','natural'],default='taylor');p.add_argument('--max-tiles',type=int,default=30000);a=p.parse_args();run(a.output,a.mode,a.max_tiles)
