"""Finite Taylor-model certificate generator; proposals are checked by Lean."""
from dataclasses import dataclass
from fractions import Fraction as Q
import math
from pathlib import Path
from degree8_scalar_certificates import Disk, exact, outward, lean_certificate, literal, pair, cmul, size

ZERO=exact(0)


def add(a,b): return [outward(x.add(y)) for x,y in zip(a,b)]
def scale(q,a): return [outward(exact(*q).mul(x)) for x in a]
def mul(a,b):
    return [outward(sum_disks(a[i].mul(b[n-i]) for i in range(n+1))) for n in range(9)]
def sum_disks(xs):
    result=ZERO
    for x in xs: result=result.add(x)
    return result

def inverse(a):
    assert not a[0].r
    x,y=a[0].c;den=x*x+y*y
    b=[exact(x/den,-y/den)]
    for n in range(8):
        r=exact(-1).mul(b[0].mul(sum_disks(a[i+1].mul(b[n-i]) for i in range(n+1))))
        b.append(outward(r))
    return b


def exponential(a,constant):
    b=[constant]
    for n in range(8):
        r=exact(Q(1,n+1)).mul(sum_disks(exact(i+1).mul(a[i+1].mul(b[n-i]))
                                       for i in range(n+1)))
        b.append(outward(r))
    return b


@dataclass
class Node:
    name: str
    jet: list


HEADER='''/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.CertifiedTaylorInputs
import Reinmann.HardTileGammaLogJet
import Reinmann.HardTileLogInputs
import Mathlib.Tactic.IntervalCases

/-! Generated rational Taylor proposals with kernel-checked soundness proofs. -/
noncomputable section
namespace Reinmann.HardTileFiniteJets
open CertifiedTaylorModel CertifiedTaylorComposition CertifiedTaylorInputs
open scoped Topology
set_option maxRecDepth 20000

def c : ℂ := HardTileGammaLogJet.centre

'''


class Builder:
    def __init__(self):
        self.source=HEADER
        self.nodes=[]
        self.unfold=['HardTileGammaLogJet.logJet','HardTileGammaLog.gammaLogDisk',
                     'HardTileGammaLogJet.affineJet','HardTileGammaLogJet.inverseJet',
                     'HardTileGammaLogJet.inverseTable']
        self.constants={}
        self.functions={}

    def start(self,name,jet,fn,analytic):
        assert name not in [x.name for x in self.nodes]
        self.functions[name]=fn
        self.source+=f'def F_{name} (s : ℂ) : ℂ := {fn}\n\n'
        self.source+=f'def J_{name} : Jet8 := fun k =>\n  match k.val with\n'
        for k,d in enumerate(jet): self.source+=f'  | {k} => {d.lean()}\n'
        self.source+='  | _ => zero\n\n'
        self.source+=f'theorem A_{name} : AnalyticAt ℂ F_{name} c := by\n  {analytic}\n\n'
        self.unfold.append('J_'+name)
        node=Node(name,jet);self.nodes.append(node)
        return node

    def arithmetic(self,name,a,b=None,q=None):
        if q is not None:
            jet=scale(q,a.jet);fn=f'value {pair(q)}*F_{a.name} s'
            analytic=f'exact analyticAt_const.mul A_{a.name}'
            sound=f'sound_scale A_{a.name} S_{a.name}'
            op='jetScale'
        elif b is not None:
            jet=mul(a.jet,b.jet);fn=f'F_{a.name} s*F_{b.name} s'
            analytic=f'exact A_{a.name}.mul A_{b.name}'
            sound=f'sound_mul A_{a.name} A_{b.name} S_{a.name} S_{b.name}'
            op='jetMul'
        else: raise ValueError(name)
        node=self.start(name,jet,fn,analytic)
        self.source+=f'''set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_{name} : Sound J_{name} F_{name} c := by
  apply sound_round ({sound})
  intro k
  fin_cases k <;> norm_num [{', '.join(self.unfold[-3:])},
    {', '.join('J_'+x.name for x in ([a,b] if b else [a]))}, {op}, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

'''
        return node

    def plus(self,name,a,b):
        node=self.start(name,add(a.jet,b.jet),f'F_{a.name} s+F_{b.name} s',f'exact A_{a.name}.add A_{b.name}')
        self.source+=f'''set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_{name} : Sound J_{name} F_{name} c := by
  apply sound_round (sound_add A_{a.name} A_{b.name} S_{a.name} S_{b.name})
  intro k
  fin_cases k <;> norm_num [J_{name}, J_{a.name}, J_{b.name}, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

'''
        return node

    def rational(self,re,im=0):
        q=(Q(re),Q(im))
        if q in self.constants: return self.constants[q]
        name='q'+str(len(self.constants))
        jet=[exact(*q)]+[ZERO]*8
        node=self.start(name,jet,f'value {pair(q)}','exact analyticAt_const')
        self.source+=f'''theorem S_{name} : Sound J_{name} F_{name} c := by
  have h := constant_sound (c := c) (contains_exact {pair(q)})
  convert h using 1
  funext k
  fin_cases k <;> rfl

'''
        self.constants[q]=node
        return node

    def logarithm_constant(self,n):
        name='log'+str(n)
        found=next((x for x in self.nodes if x.name==name),None)
        if found: return found
        if n=='pi': x='Real.pi';value=Q('1.144729885849400');e=Q(6,10**15);proof='log_pi'
        else: x=str(n);value=Q(round(math.log(n)*10**15),10**15);e=Q(1 if n==2 else 6,10**15);proof='log_'+str(n)
        jet=[Disk((value,Q(0)),e)]+[ZERO]*8
        node=self.start(name,jet,f'(Real.log ({x} : ℝ) : ℂ)','exact analyticAt_const')
        self.source+=f'''theorem S_{name} : Sound J_{name} F_{name} c := by
  have hlog : Contains {jet[0].lean()} (Real.log ({x} : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.{proof} using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

'''
        return node

    def variable(self):
        found=next((x for x in self.nodes if x.name=='variable'),None)
        if found: return found
        node=self.start('variable',[exact(Q(1,2),14),exact(1)]+[ZERO]*7,'s','exact analyticAt_id')
        self.source+='''theorem S_variable : Sound J_variable F_variable c := by
  have h := variable_sound ((1/2 : ℚ),14)
  convert h using 1
  · funext k
    fin_cases k <;> rfl
  · norm_num [c, HardTileGammaLogJet.centre, value]

'''
        return node

    def exp(self,name,a):
        text,constant=lean_certificate(name+'Value',a.jet[0]);self.source+=text
        jet=exponential(a.jet,constant)
        node=self.start(name,jet,f'Complex.exp (F_{a.name} s)',f'exact A_{a.name}.cexp\'')
        self.source+=f'''set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_{name} : Sound J_{name} F_{name} c := by
  apply exp_sound A_{a.name} S_{a.name} {name}Value {name}Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [{name}Value, J_{a.name}]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [J_{name}, J_{a.name}, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

'''
        return node

    def inv(self,name,a):
        jet=inverse(a.jet)
        q=a.jet[0].c;qinv=jet[0].c
        assert q[1]
        self.source+=f'''theorem V_{name} : F_{a.name} c = value {pair(q)} := by
  have h := centre_contains S_{a.name}
  have he : J_{a.name} ⟨0,by omega⟩ = exact {pair(q)} := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_{a.name}, exact]
  rw [he] at h
  exact value_eq_of_exact h

theorem N_{name} : F_{a.name} c ≠ 0 := by
  rw [V_{name}]
  intro h
  have hi := congrArg Complex.im h
  norm_num [value] at hi

'''
        node=self.start(name,jet,f'(F_{a.name} s)⁻¹',f'exact A_{a.name}.inv N_{name}')
        self.source+=f'''set_option maxHeartbeats 5000000 in
-- One exact inverse and eight outward-rounded reciprocal recurrence checks.
theorem S_{name} : Sound J_{name} F_{name} c := by
  apply inv_coefficients_sound A_{a.name} N_{name} S_{a.name}
  · rw [V_{name}]
    have hv : (value {pair(q)})⁻¹ = value {pair(qinv)} := by
      apply Complex.ext <;> norm_num [value, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
    rw [hv]
    simpa [J_{name}] using contains_exact {pair(qinv)}
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [J_{name}, J_{a.name}, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

'''
        return node


def known_gamma_inputs(b):
    affine=[exact(Q(49,4),7),exact(Q(1,2))]+[ZERO]*7
    v0=exact(Q(196,3185),Q(-112,3185))
    inv=[v0]
    def fixed(a):
        step=Q(1,2**50)
        c=tuple(round(x/step)*step for x in a.c)
        e=a.r+size((a.c[0]-c[0],a.c[1]-c[1]))
        return Disk(c,-(-e//step)*step)
    for n in range(1,9):
        inv.append(fixed(exact(Q(-1,2)).mul(v0.mul(inv[-1]))))
    log=[Disk((Q(93126327582951,2**45),Q(18265830052121,2**45)),Q(1,2**45))]
    for n in range(1,9): log.append(fixed(exact(Q(1,2*n)).mul(inv[n-1])))
    items=[('shift',affine,'HardTileGammaLogJet.shifted s','HardTileGammaLogJet.affineJet',
            'HardTileGammaLogJet.shifted_analytic','HardTileGammaLogJet.affine_sound'),
           ('shiftinv',inv,'(HardTileGammaLogJet.shifted s)⁻¹','HardTileGammaLogJet.inverseJet',
            'HardTileGammaLogJet.shifted_analytic.inv HardTileGammaLogJet.shifted_nonzero',
            'HardTileGammaLogJet.inverse_sound'),
           ('shiftlog',log,'Complex.log (HardTileGammaLogJet.shifted s)','HardTileGammaLogJet.logJet',
            'HardTileGammaLogJet.shifted_analytic.clog HardTileGammaLogJet.shifted_slit',
            'HardTileGammaLogJet.log_sound')]
    result=[]
    for name,data,fn,jet,A,S in items:
        b.functions[name]=fn
        b.source+=f'def F_{name} (s : ℂ) : ℂ := {fn}\n'
        b.source+=f'def J_{name} : Jet8 := {jet}\n'
        b.source+=f'theorem A_{name} : AnalyticAt ℂ F_{name} c := {A}\n'
        b.source+=f'theorem S_{name} : Sound J_{name} F_{name} c := {S}\n\n'
        node=Node(name,data);b.nodes.append(node);b.unfold.append('J_'+name);result.append(node)
    return result


def gamma_model(b):
    variable=b.variable();log2=b.logarithm_constant(2);logpi=b.logarithm_constant('pi')
    w,iw,lw=known_gamma_inputs(b)
    wm=b.plus('wmhalf',w,b.rational(Q(-1,2)))
    term=b.arithmetic('wlog',wm,lw)
    negw=b.arithmetic('negw',w,q=(Q(-1),Q(0)))
    main=b.plus('mainbase',term,negw)
    logs=b.plus('log2pi',log2,logpi)
    const=b.arithmetic('halfLog2pi',logs,q=(Q(1,2),Q(0)))
    main=b.plus('mainconstant',main,const)
    B={1:Q(1,6),2:Q(-1,30),3:Q(1,42),4:Q(-1,30),5:Q(5,66),6:Q(-691,2730)}
    powers={1:iw}
    for n in range(2,12): powers[n]=b.arithmetic('iw'+str(n),powers[n-1],iw)
    for k in range(1,7):
        corr=b.arithmetic('gcorr'+str(k),powers[2*k-1],q=(B[k]/(2*k*(2*k-1)),Q(0)))
        main=b.plus('maincorr'+str(k),main,corr)
    eg=b.exp('expGammaMain',main)
    half=b.arithmetic('halfVariable',variable,q=(Q(1,2),Q(0)))
    invprod=None
    for j in range(12):
        term=half if j==0 else b.plus('shift'+str(j),half,b.rational(j))
        it=b.inv('gammaInv'+str(j),term)
        invprod=it if invprod is None else b.arithmetic('gammaInvProd'+str(j),invprod,it)
    b.gammaMain=main
    b.gammaDen=invprod
    b.gammaExp=eg
    return b.arithmetic('gammaFinite',eg,invprod)


def zeta_model(b):
    variable=b.variable();terms={1:b.rational(1)}
    for n in range(2,22):
        log=b.logarithm_constant(n)
        neg=b.arithmetic('negLog'+str(n),log,q=(Q(-1),Q(0)))
        arg=b.arithmetic('arg'+str(n),neg,variable)
        terms[n]=b.exp('term'+str(n),arg)
    initial=terms[1]
    for n in range(2,21): initial=b.plus('initial'+str(n),initial,terms[n])
    sm=b.plus('sminusone',variable,b.rational(-1))
    iv=b.inv('sminusoneInv',sm)
    integral=b.arithmetic('emIntegralProduct',terms[21],iv)
    integral=b.arithmetic('emIntegral',integral,q=(Q(21),Q(0)))
    half=b.arithmetic('emHalf',terms[21],q=(Q(1,2),Q(0)))
    model=b.plus('emInitialIntegral',initial,integral)
    model=b.plus('emInitialHalf',model,half)
    powers={1:variable};factors={}
    for j in range(1,11):
        factors[j]=b.plus('factor'+str(j),variable,b.rational(j))
        powers[j+1]=b.arithmetic('rising'+str(j+1),powers[j],factors[j])
    B={1:Q(1,6),2:Q(-1,30),3:Q(1,42),4:Q(-1,30),5:Q(5,66),6:Q(-691,2730)}
    corr=[]
    for k in range(1,7):
        product=b.arithmetic('emCorrProduct'+str(k),powers[2*k-1],terms[21])
        coefficient=B[k]/math.factorial(2*k)/(21**(2*k-1))
        term=b.arithmetic('emCorr'+str(k),product,q=(coefficient,Q(0)))
        corr.append(term)
        model=b.plus('emAfterCorr'+str(k),model,term)
    b.zetaTerms=terms;b.zetaRising=powers;b.zetaFactors=factors
    b.zetaParts=[initial,integral,half]+corr
    return model


def zeta_identities(b,model):
    for n,node in b.zetaTerms.items():
        definitions=', '.join(reachable(b,node.name))
        if n==1:
            proof='simp [HardTileFiniteIdentities.dirichletTerm, '+definitions+', value]'
        else:
            proof=f'''unfold HardTileFiniteIdentities.dirichletTerm
  simp only [{definitions}, value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero]
  congr 1
  ring'''
        b.source+=f'''theorem term{n}_identity (s : ℂ) :
    F_{node.name} s = HardTileFiniteIdentities.dirichletTerm s {n} := by
  {proof}

'''
    for n,node in b.zetaRising.items():
        if n==1:
            proof='simp [F_variable, HardTileFiniteIdentities.rising, Finset.prod_range_succ]'
        else:
            previous=b.zetaRising[n-1].name
            factor=b.zetaFactors[n-1].name
            factor_defs=', '.join(reachable(b,factor))
            proof=f'''simp only [F_{node.name}, rising{n-1}_identity,
    {factor_defs}, HardTileFiniteIdentities.rising, Finset.prod_range_succ,
    value, Rat.cast_zero, zero_mul, add_zero, Rat.cast_ofNat]
  first | rfl | (simp only [Finset.prod_range_zero, Nat.cast_zero, add_zero, one_mul] <;> rfl)'''
        b.source+=f'''theorem rising{n}_identity (s : ℂ) :
    F_{node.name} s = HardTileFiniteIdentities.rising s {n} := by
  {proof}

'''
    # Unfold the final arithmetic but preserve the exp/rising functions for their identities.
    stop={x.name for x in b.zetaTerms.values()}|{x.name for x in b.zetaRising.values()}
    import re
    seen=[]
    def visit(n):
        if n in stop or n in seen: return
        seen.append(n)
        for dep in re.findall(r'F_(\w+)',b.functions[n]): visit(dep)
    visit(model.name)
    defs=', '.join('F_'+n for n in seen)
    terms=', '.join('term'+str(n)+'_identity' for n in b.zetaTerms)
    rising=', '.join('rising'+str(n)+'_identity' for n in b.zetaRising)
    b.source+=f'''theorem zetaFinite_identity (s : ℂ) :
    F_{model.name} s = EulerMaclaurinZeta.finiteModel s 21 := by
  rw [HardTileFiniteIdentities.emFinite_eq]
  simp only [{defs}, {terms}, {rising},
    HardTileFiniteIdentities.emFinite, Finset.sum_range_succ, Finset.sum_range_zero,
    value, Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero, Rat.cast_ofNat, Nat.cast_ofNat]
  simp only [show HardTileFiniteIdentities.rising s 1 = s by
    simp [HardTileFiniteIdentities.rising], show s+(-1 : ℂ) = s-1 by ring]
  ring

'''


def render_both():
    b=Builder();g=gamma_model(b);z=zeta_model(b)
    b.source=b.source.replace('import Reinmann.CertifiedTaylorInputs',
        'import Reinmann.StirlingAnalytic\nimport Reinmann.HardTileFiniteIdentities\nimport Reinmann.CertifiedTaylorInputs')
    gamma_identities(b);zeta_identities(b,z)
    import sys
    import xi_evaluator_comparison as previous
    from flint import ctx,acb_series,arb,acb
    ctx.prec=192;ctx.cap=9
    s=acb_series([previous.CENTRE,1])
    for node,truth in [(g,previous.gamma_stirling(s,12,7)),(z,previous.zeta_em(s,20,6))]:
        for k,d in enumerate(node.jet):
            c=acb(arb(str(d.c[0])),arb(str(d.c[1])))
            assert abs(truth[k]-c) < arb(str(d.r)), (node.name,k,truth[k],d)
        print(node.name,'maximum proposed radius',max(float(d.r) for d in node.jet),file=sys.stderr)
    return finalize(b.source)+'end Reinmann.HardTileFiniteJets\n'


def reachable(b,name):
    import re
    seen=[]
    def visit(n):
        if n in seen: return
        seen.append(n)
        for dep in re.findall(r'F_(\w+)',b.functions[n]): visit(dep)
    visit(name)
    return ['F_'+x for x in seen]


def gamma_identities(b):
    main=b.gammaMain.name
    main_defs=', '.join(reachable(b,main))
    den_defs=', '.join(reachable(b,b.gammaDen.name))
    b.source+=f'''theorem gammaMain_identity (s : ℂ) :
    F_{main} s = StirlingGamma.mainTerm (s/2+12) := by
  rw [HardTileFiniteIdentities.stirlingMain_eq]
  simp only [{main_defs}, HardTileFiniteIdentities.stirlingMain,
    HardTileGammaLogJet.shifted, value, Rat.cast_zero, zero_mul, add_zero,
    Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Complex.ofReal_add]
  simp only [show (12 : ℂ)+(1/2)*s = s/2+12 by ring]
  ring

theorem gammaFinite_identity (s : ℂ) :
    F_gammaFinite s = StirlingAnalytic.gammaApprox s := by
  simp only [F_gammaFinite, F_{b.gammaExp.name}, gammaMain_identity,
    StirlingAnalytic.gammaApprox, div_eq_mul_inv, ← Finset.prod_inv_distrib]
  simp only [{den_defs}, value, Rat.cast_zero, zero_mul, add_zero,
    Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Nat.cast_ofNat,
    Finset.prod_range_succ, Finset.prod_range_zero, mul_one, one_mul]
  simp only [show (1/2 : ℂ)*s = s/2 by ring]
  ring

'''


def render_gamma():
    b=Builder();result=gamma_model(b)
    b.source=b.source.replace('import Reinmann.CertifiedTaylorInputs', 'import Reinmann.StirlingAnalytic\nimport Reinmann.HardTileFiniteIdentities\nimport Reinmann.CertifiedTaylorInputs')
    gamma_identities(b)
    # Numeric checks below are independent development probes, never Lean inputs.
    import sys
    import xi_evaluator_comparison as previous
    from flint import ctx,acb_series,arb,acb
    ctx.prec=192;ctx.cap=9
    truth=previous.gamma_stirling(acb_series([previous.CENTRE,1]),12,7)
    for k,d in enumerate(result.jet):
        c=acb(arb(str(d.c[0])),arb(str(d.c[1])))
        assert abs(truth[k]-c) < arb(str(d.r)), (k,truth[k],d)
    print('Gamma finite maximum proposed radius',max(float(d.r) for d in result.jet),file=sys.stderr)
    return finalize(b.source)+'end Reinmann.HardTileFiniteJets\n'


def finalize(source):
    old=['HardTileGammaLogJet.logJet','HardTileGammaLog.gammaLogDisk',
         'HardTileGammaLogJet.affineJet','HardTileGammaLogJet.inverseJet',
         'HardTileGammaLogJet.inverseTable']
    return source.replace('norm_num [J_', 'norm_num ['+', '.join(old)+', J_')


def render_probe():
    b=Builder();v=b.variable();l=b.logarithm_constant(2)
    a=b.arithmetic('minuslog',l,q=(Q(-1),Q(0)))
    a=b.arithmetic('exponent',a,v)
    e=b.exp('power2',a)
    return finalize(b.source)+'end Reinmann.HardTileFiniteJets\n'


if __name__=='__main__':
    target=Path(__file__).resolve().parents[2]/'Reinmann/HardTileFiniteJets.lean'
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gamma',action='store_true')
    parser.add_argument('--both',action='store_true')
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    source=render_both() if args.both else render_gamma() if args.gamma else render_probe()
    if args.check:
        assert target.read_text()==source, 'Generated finite jets differ'
    else:
        target.write_text(source)
    print(target)
