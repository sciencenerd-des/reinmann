"""Generate rational certificate proposals; Lean independently checks all arithmetic."""
from fractions import Fraction as Q
from pathlib import Path
import argparse, json, math
from rectangle_model import build_graph, evaluate, log_constant, ZERO
from degree8_scalar_certificates import exact, lean_certificate, literal as q, pair

ROOT = Path(__file__).resolve().parents[2]
HEADER = '''/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
'''


def logs():
    # Reuse the already checked logs; only six larger integers need new proofs.
    s = HEADER + '''import Reinmann.HardTileLogInputs
import Reinmann.CertifiedScalarExp

noncomputable section
namespace Reinmann.RectangleLogInputs
open CertifiedComplexInputs CertifiedTaylorModel
set_option maxRecDepth 10000
'''
    a2 = log_constant(2).c[0]
    for n in range(22,28):
        k=n.bit_length()-1; small=Q(n,2**k)
        b=Q(round(math.log(float(small))*10**15),10**15); a=log_constant(n).c[0]
        s+=f'''set_option maxHeartbeats 2000000 in
theorem log_{n} : |Real.log ({n}:ℝ)-({q(a)}:ℝ)| ≤ (8/10^15:ℝ) := by
  have h := log_scaled_enclosure (q := {q(small)}) (a := {q(a2)}) (b := {q(b)}) {k}
    (by norm_num) (by convert HardTileLogInputs.log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show ({k}*(1/10^15)+1/10^15:ℚ)+
    |({k}*{q(a2)}+{q(b)}:ℚ)-{q(a)}| ≤ (8/10^15:ℚ) by norm_num) using 1 <;> norm_num

'''
    for n in list(range(2,28))+['pi']:
        arg='Real.pi' if n=='pi' else str(n)
        proof=('HardTileLogInputs.' if n=='pi' or n<22 else '')+'log_'+str(n)
        s+=f'''def log{n}Disk : Disk := {log_constant(n).lean()}
theorem log{n}_contains : Contains log{n}Disk (Real.log ({arg}:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert {proof} using 1 <;> norm_num [log{n}Disk]

'''
    s+='end Reinmann.RectangleLogInputs\n'
    (ROOT/'Reinmann/RectangleLogInputs.lean').write_text(s)


def model(g):
    s=HEADER+'''import Reinmann.RectangleTaylor
import Reinmann.RectangleLogInputs
import Reinmann.RectangleFiniteFormulas
import Reinmann.UniformXiRemainders
import Reinmann.CertifiedHorner
import Mathlib.Tactic.IntervalCases

/-! Shared analytic and finite-expression proofs; independent of tile centres. -/
noncomputable section
namespace Reinmann.RectangleModel
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor Filter
open scoped Topology
set_option maxRecDepth 20000
set_option linter.style.longLine false
set_option linter.style.whitespace false
'''
    for node in g.nodes:
        name=node.name;args=node.inputs
        if node.op=='const': f=f'value {pair(node.q)}'; a='exact analyticAt_const'
        elif node.op=='var': f='s'; a='exact analyticAt_id'
        elif node.op=='logconst':
            f=f'(Real.log ({"Real.pi" if node.n=="pi" else node.n}:ℝ):ℂ)'; a='exact analyticAt_const'
        elif node.op in ('add','mul'):
            op='+' if node.op=='add' else '*'; f=f'F_{args[0]} s {op} F_{args[1]} s'
            a=f'exact (A_{args[0]} hc).{node.op} (A_{args[1]} hc)'
        elif node.op=='scale': f=f'value {pair(node.q)} * F_{args[0]} s';a=f'exact analyticAt_const.mul (A_{args[0]} hc)'
        elif node.op=='inv':
            f=f'(F_{args[0]} s)⁻¹'; a=f'exact (A_{args[0]} hc).inv (N_{name} hc)'
            defs=', '.join('F_'+x for x in g.reachable(args[0]))
            s+=f'''theorem P_{name} {{c:ℂ}} (hc:-2<c.re) : 0 < (F_{args[0]} c).re := by
  norm_num [{defs}, value, Complex.mul_re] at *
  linarith

theorem N_{name} {{c:ℂ}} (hc:-2<c.re) : F_{args[0]} c ≠ 0 :=
  Complex.ne_zero_of_re_pos (P_{name} hc)

'''
        elif node.op=='log':
            f=f'Complex.log (F_{args[0]} s)';a=f'exact (A_{args[0]} hc).clog (L_{name} hc)'
            s+=f'''theorem L_{name} {{c:ℂ}} (hc:-2<c.re) : F_{args[0]} c ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (P_shiftInv hc))

'''
        elif node.op=='exp': f=f'Complex.exp (F_{args[0]} s)';a=f"exact (A_{args[0]} hc).cexp'"
        elif node.op=='gamma_actual':
            f='RegularizedEulerMaclaurin.gammaFactor s'
            a='''apply DifferentiableOn.analyticAt (s := {z : ℂ | -2<z.re})
    (fun z hz => (RegularizedEulerMaclaurin.gammaFactor_differentiableAt hz).differentiableWithinAt)
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hc)'''
        elif node.op=='zeta_actual': f='RegularizedEulerMaclaurin.regularZeta s';a='exact RegularizedEulerMaclaurin.regularZeta_differentiable.analyticAt c'
        else: raise ValueError(node.op)
        s+=f'''def F_{name} (s:ℂ) : ℂ := {f}
theorem A_{name} {{c:ℂ}} (hc:-2<c.re) : AnalyticAt ℂ F_{name} c := by
  {a}

'''
    defs=', '.join('F_'+x for x in g.reachable(g.gamma_main.name, stop=('shift',)))
    s+=f'''theorem gammaMain_identity (s:ℂ) : F_{g.gamma_main.name} s =
    StirlingGamma.mainTerm (1+s/2+12) := by
  rw [HardTileFiniteIdentities.stirlingMain_eq]
  simp only [{defs}, F_shift,F_base,F_halfVariable,F_variable,F_q0,F_q1, HardTileFiniteIdentities.stirlingMain]
  norm_num [value, div_eq_mul_inv, ← inv_pow]
  ring

'''
    # A normalization lemma avoids expanding the large Stirling expression twice.
    s+='''theorem shift_identity (s:ℂ) : F_shift s=1+s/2+12 := by
  norm_num [F_shift,F_base,F_halfVariable,F_variable,F_q0,F_q1,value]
  ring

'''
    den_defs=', '.join('F_'+x for x in g.reachable(g.gamma_denominator.name))
    s+=f'''theorem gammaFinite_identity (s:ℂ) : F_gammaFinite s = UniformXiRemainders.gammaApprox s := by
  unfold F_gammaFinite F_gammaExp
  rw [gammaMain_identity]
  unfold UniformXiRemainders.gammaApprox
  simp only [div_eq_mul_inv, ← Finset.prod_inv_distrib]
  congr 1
  norm_num [{den_defs}, Finset.prod_range_succ, value]
  ring

'''
    for n,node in g.zeta_terms.items():
        defs=', '.join('F_'+x for x in g.reachable(node.name))
        s+=f'''theorem term_{n}_identity (s:ℂ) : F_{node.name} s=HardTileFiniteIdentities.dirichletTerm s {n} := by
  norm_num [{defs}, HardTileFiniteIdentities.dirichletTerm, value]
  {'skip' if n==1 else 'congr 1\n  ring'}

'''
    for n,node in g.zeta_rising.items():
        defs=', '.join('F_'+x for x in g.reachable(node.name))
        s+=f'''theorem rising_{n}_identity (s:ℂ) : F_{node.name} s=HardTileFiniteIdentities.rising s {n} := by
  norm_num [{defs}, HardTileFiniteIdentities.rising, Finset.prod_range_succ, value] <;> ring

'''
    stop=tuple(x.name for x in g.zeta_terms.values())+tuple(x.name for n,x in g.zeta_rising.items() if n>1)
    defs=' '.join('F_'+x for x in g.reachable(g.zeta_finite.name, stop=stop))
    ids=', '.join([f'term_{n}_identity' for n in range(1,28)]+[f'rising_{n}_identity' for n in range(2,12)])
    s+=f'''set_option maxHeartbeats 2000000 in
theorem zetaFinite_identity (s:ℂ) : F_zetaFinite s=RegularizedEulerMaclaurin.regularModel s 27 := by
  rw [← RectangleFiniteFormulas.regularExpr_eq]
  simp only [{defs.replace(" ",", ")}]
  simp only [{ids}]
  norm_num [RectangleFiniteFormulas.regularExpr,RectangleFiniteFormulas.finitePart,
    Finset.sum_range_succ,HardTileFiniteIdentities.rising,value,F_variable]
  ring

'''
    defs=' '.join('F_'+x for x in g.reachable(g.pi.name))
    s+=f'''theorem piPower_identity (s:ℂ) : F_piPower s=RegularizedEulerMaclaurin.piFactor s := by
  unfold {defs} RegularizedEulerMaclaurin.piFactor
  norm_num [value]
  congr 1
  ring

theorem xiProduct_identity {{s:ℂ}} (hs:0<s.re) : F_xiProduct s=xiCompleted s := by
  rw [RegularizedEulerMaclaurin.xi_eq_regular_product hs]
  unfold F_xiProduct F_piGamma F_gammaActual F_zetaActual
  rw [piPower_identity]

 theorem gamma_sound {{d:ℕ}} {{a:Jet d}} {{c:ℂ}}
    (hc:c ∈ XiAdaptiveTiles.quarter (141/10)) (ha:Sound a F_gammaFinite c) :
    Sound (fun k => inflate (a k) (4/10^14) (by norm_num)) F_gammaActual c := by
  apply sound_perturb (by norm_num) (sound_congr ha (Eventually.of_forall gammaFinite_identity))
  intro k
  simpa only [coefficient,F_gammaActual,Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow] using
    UniformXiRemainders.gamma_coefficient_error_le hc.1 (by linarith [hc.2.1]) k.val

theorem zeta_sound {{d:ℕ}} {{a:Jet d}} {{c:ℂ}}
    (hc:c ∈ XiAdaptiveTiles.quarter (141/10)) (ha:Sound a F_zetaFinite c) :
    Sound (fun k => inflate (a k) (6/10^8) (by norm_num)) F_zetaActual c := by
  apply sound_perturb (by norm_num) (sound_congr ha (Eventually.of_forall zetaFinite_identity))
  intro k
  simpa only [coefficient,F_zetaActual,Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow] using
    UniformXiRemainders.zeta_coefficient_error_le hc k.val

theorem xi_sound {{d:ℕ}} {{a:Jet d}} {{c:ℂ}}
    (hc:c ∈ XiAdaptiveTiles.quarter (141/10)) (ha:Sound a F_xiProduct c) :
    Sound a xiCompleted c := by
  apply sound_congr ha
  have hc0 : 0<c.re := by linarith [hc.1]
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hc0] with s hs
  exact xiProduct_identity hs

theorem log_scaled16_contains {{w z:QComplex}} {{a:Disk}}
    (hscale:value w=(16:ℂ)*(1+value z)) (hz0:1+value z≠0)
    (hn:‖value z‖≤1/2) (ha:Contains a (Complex.logTaylor 48 (value z))) :
    Contains (add (mul (exact (4,0)) RectangleLogInputs.log2Disk)
      (inflate a (1/10^15) (by norm_num))) (Complex.log (value w)) := by
  have h := contains_add (contains_mul (contains_exact ((4:ℚ),0))
    RectangleLogInputs.log2_contains) (CertifiedComplexInputs.log_series_contains hn ha)
  have h16 : Real.log (16:ℝ)=4*Real.log 2 := by
    have h := Real.log_pow (2:ℝ) 4
    norm_num only at h
    exact h
  have he : value ((4:ℚ),0)*(Real.log (2:ℝ):ℂ)+Complex.log (1+value z)=
      Complex.log (value w) := by
    rw [hscale]
    change _=Complex.log (((16:ℝ):ℂ)*(1+value z))
    rw [Complex.log_ofReal_mul (by norm_num : (0:ℝ)<16) hz0,h16]
    simp [value]
  rw [he] at h
  exact h

end Reinmann.RectangleModel
'''
    (ROOT/'Reinmann/RectangleModel.lean').write_text(s)



def data_file(plan):
    tiles=plan['tiles']; count=len(tiles)
    s=HEADER+'''import Reinmann.RectangleTileRules

noncomputable section
namespace Reinmann.XiRectangle.Data
open CertifiedTaylorModel
'''
    s+=f'def count : ℕ := {count}\ndef degree : ℕ := {plan["degree"]}\n\n'
    for name,key,typ,fmt in [('coordinate','centre','QComplex',lambda x:pair(tuple(map(Q,x)))),
                             ('radius','radius','ℚ',lambda x:q(Q(x)))]:
        s+=f'def {name} (i:Fin count) : {typ} :=\n  match i.val with\n'
        for tile in tiles:s+=f'  | {tile["index"]} => {fmt(tile[key])}\n'
        s+='  | _ => '+('(0,0)' if typ=='QComplex' else '0')+'\n\n'
    s+='''def centre (i:Fin count) : ℂ := value (coordinate i)
theorem centre_mem_quarter (i:Fin count) : centre i ∈ XiAdaptiveTiles.quarter (141/10) := by
  fin_cases i <;> norm_num [centre,coordinate,count,value,XiAdaptiveTiles.quarter]
end Reinmann.XiRectangle.Data
'''
    (ROOT/'XiRectangle/Data.lean').write_text(s)


ARITH='sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size'


def tile_file(g,tile):
    d=tile['degree']; idx=tile['index']; centre=tuple(map(Q,tile['centre']))
    data,extras=evaluate(g,centre,d)
    s=HEADER+'''import Reinmann.RectangleModel
import XiRectangle.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
'''+f'namespace Reinmann.XiRectangle.Tile{idx:03}\n'+'''open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

'''
    s+=f'''private def c : ℂ := Data.centre ⟨{idx},by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

'''
    for node in g.nodes:
        name=node.name; args=node.inputs; jet=data[name]
        s+=f'private def J_{name} : Jet {d} := fun k =>\n  match k.val with\n'
        for k,a in enumerate(jet):s+=f'  | {k} => {a.lean()}\n'
        s+='  | _ => zero\n\n'
        title=f'private theorem S_{name} : Sound J_{name} F_{name} c := by\n'
        if node.op=='const':
            s+=title+f'''  have h := constant_sound (d:={d}) (c:=c) (contains_exact {pair(node.q)})
  convert h using 1
  funext k
  fin_cases k <;> rfl

'''
        elif node.op=='var':
            s+=title+f'''  have h := variable_sound {d} {pair(centre)}
  have he : value {pair(centre)}=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

'''
        elif node.op=='logconst':
            s+=title+f'''  have h := constant_sound (d:={d}) (c:=c) RectangleLogInputs.log{node.n}_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

'''
        elif node.op in ('add','mul','scale'):
            if node.op=='add': sound=f'sound_add (A_{args[0]} hcre) (A_{args[1]} hcre) S_{args[0]} S_{args[1]}'; op='jetAdd'
            elif node.op=='mul': sound=f'sound_mul (A_{args[0]} hcre) (A_{args[1]} hcre) S_{args[0]} S_{args[1]}';op='jetMul'
            else:sound=f'sound_scale (A_{args[0]} hcre) S_{args[0]}';op='jetScale'
            s+='set_option maxHeartbeats 5000000 in\n'+title+f'''  apply sound_round ({sound})
  intro k
  fin_cases k <;> norm_num [J_{name}, {', '.join('J_'+x for x in args)}, {op}, {ARITH}]

'''
        elif node.op=='inv':
            a=args[0]; w=data[a][0].c;winv=jet[0].c
            s+=f'''private theorem V_{name} : F_{a} c=value {pair(w)} := by
  have h := centre_contains S_{a}
  have he : J_{a} ⟨0,by omega⟩=exact {pair(w)} := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_{a},exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
'''+title+f'''  apply inv_coefficients_sound (A_{a} hcre) (N_{name} hcre) S_{a}
  · rw [V_{name}]
    have hv : (value {pair(w)})⁻¹=value {pair(winv)} := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_{name}] using contains_exact {pair(winv)}
  · intro n hn
    have hlt : n < {d} := by omega
    interval_cases n <;> norm_num [J_{name},J_{a},{ARITH}]

'''
        elif node.op=='exp':
            text,result=lean_certificate(name+'Value',data[args[0]][0])
            text=text.replace('\ndef ','\nprivate def ').replace('\ntheorem ','\nprivate theorem ')
            if text.startswith('def '):text='private '+text
            s+=text+'set_option maxHeartbeats 5000000 in\n'+title+f'''  apply exp_sound (A_{args[0]} hcre) S_{args[0]} {name}Value {name}Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [{name}Value,J_{args[0]}]
  · rfl
  · intro n hn
    have hlt : n < {d} := by omega
    interval_cases n <;> norm_num [J_{name},J_{args[0]},{ARITH}]

'''
        elif node.op=='log':
            ex=extras[name];z=ex['input']; w=data[args[0]][0].c
            s+='private def logTable : ℕ → Disk\n'
            for k,a in ex['table'].items():s+=f'  | {k} => {a.lean()}\n'
            s+='  | _ => zero\n\n'
            s+=f'''set_option maxHeartbeats 5000000 in
private theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value {pair(z)})) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact {pair(z)})
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

private theorem logNorm : ‖value {pair(z)}‖≤(1/2:ℝ) := by
  have h := Complex.sq_norm (value {pair(z)})
  norm_num [Complex.normSq_apply,value] at h
  nlinarith [norm_nonneg (value {pair(z)})]

set_option maxHeartbeats 5000000 in
private theorem logValue : Contains (J_{name} ⟨0,by omega⟩) (Complex.log (F_{args[0]} c)) := by
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:={pair(w)})
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (J_{name} ⟨0,by omega⟩).radius_nonneg ?_ hs
  norm_num [J_{name},RectangleLogInputs.log2Disk,logTable,inflate,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

set_option maxHeartbeats 5000000 in
'''+title+f'''  apply log_coefficients_sound (A_{args[0]} hcre) (L_{name} hcre) S_{args[0]} S_{args[1]}
  · exact logValue
  · intro n hn
    have hlt : n < {d} := by omega
    interval_cases n <;> norm_num [J_{name},J_{args[0]},J_{args[1]},{ARITH}]

'''
        elif node.op in ('gamma_actual','zeta_actual'):
            transfer='gamma_sound' if node.op=='gamma_actual' else 'zeta_sound'
            s+='set_option maxHeartbeats 5000000 in\n'+title+f'''  apply sound_round ({transfer} hc S_{args[0]})
  intro k
  fin_cases k <;> norm_num [J_{name},J_{args[0]},inflate,zero,size]

'''
        else:raise ValueError(node)
    # Proposed final simple centres/radii are checked against the full exact graph.
    proposed=[]
    from degree8_scalar_certificates import Disk,size
    for raw,cv,er in zip(data[g.xi.name],tile['coefficient_centres'],tile['coefficient_error_radii']):
        b=Disk(tuple(map(Q,cv)),Q(er))
        assert raw.r+size((raw.c[0]-b.c[0],raw.c[1]-b.c[1]))<=b.r,(idx,raw,b)
        proposed.append(b)
    s+=f'private def xiJet : Jet {d} := fun k =>\n  match k.val with\n'
    for k,a in enumerate(proposed):s+=f'  | {k} => {a.lean()}\n'
    s+='  | _ => zero\n\n'
    s+=f'''set_option maxHeartbeats 5000000 in
private theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (xi_sound hc S_{g.xi.name})
  intro k
  fin_cases k <;> norm_num [xiJet,J_{g.xi.name},size]

'''
    r=Q(tile['radius']); L=Q(tile['centre_norm_lower']);K=Q(tile['derivative_bound'])
    K=Q(-(-K.numerator*2**30//K.denominator),2**30)
    s+=f'''set_option maxHeartbeats 5000000 in
theorem nonzero {{z:ℂ}} (hz:‖z-Data.centre ⟨{idx},by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨{idx},by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:={q(r)}) (K:={q(K)}) (L:={q(L)}) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using hz

end Reinmann.XiRectangle.Tile{idx:03}
'''
    (ROOT/f'XiRectangle/Tile{idx:03}.lean').write_text(s)
    return len(s)


def cover_file(plan):
    s=HEADER+'''import Reinmann.RationalBallCover
import XiRectangle.Data

noncomputable section
namespace Reinmann.XiRectangle.Cover
open RationalBallCover

'''
    def visit(tree,box):
        nonlocal s
        name='cell'+str(len(names));names.append(name)
        if 'tile' in tree:
            idx=tree['tile']; coords=' '.join('('+q(Q(x))+')' for x in box)
            s+=f'''private theorem {name} : ∀ z ∈ rectangle {coords},
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := by
  intro z hz
  refine ⟨⟨{idx},by norm_num [Data.count]⟩,?_⟩
  apply rectangle_ball (c:=Data.centre ⟨{idx},by norm_num [Data.count]⟩) (r:=(Data.radius ⟨{idx},by norm_num [Data.count]⟩:ℝ))
    (by norm_num [Data.radius]) ?_ ?_ ?_ ?_ hz
  all_goals norm_num [Data.centre,Data.coordinate,Data.radius,CertifiedTaylorModel.value]

'''
        else:
            x0,x1,y0,y1=box;m=tree['at'];axis=tree['split']
            lo=(x0,m,y0,y1) if axis=='x' else (x0,x1,y0,m)
            hi=(m,x1,y0,y1) if axis=='x' else (x0,x1,m,y1)
            left=visit(tree['lower'],lo);right=visit(tree['upper'],hi)
            coords=' '.join('('+q(Q(x))+')' for x in box)
            s+=f'''private theorem {name} : ∀ z ∈ rectangle {coords},
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) :=
  split_{axis} {left} {right}

'''
        return name
    names=[]; root=visit(plan['coverage_tree'],plan['quarter'])
    s+=f'''theorem quarter_covered : ∀ z ∈ XiAdaptiveTiles.quarter (141/10),
    ∃ i:Fin Data.count, ‖z-Data.centre i‖≤(Data.radius i:ℝ) := {root}
end Reinmann.XiRectangle.Cover
'''
    (ROOT/'XiRectangle/Cover.lean').write_text(s)


def final_file(plan):
    count=plan['tile_count']
    s=HEADER+''.join(f'import XiRectangle.Tile{i:03}\n' for i in range(count))
    s+='''import XiRectangle.Cover
import Reinmann.QuasiRHInputs
import Reinmann.XiAnnihilator

/-! A finite certificate for actual Xi on a closed rectangle. This does not
assert the Riemann hypothesis, nor all-order Pólya-frequency positivity. -/
noncomputable section
namespace Reinmann.XiRectangle

'''
    s+='''theorem all_tiles_nonzero (i:Fin Data.count) {z:ℂ}
    (hz:‖z-Data.centre i‖≤(Data.radius i:ℝ)) : xiCompleted z≠0 := by
  fin_cases i
'''
    for i in range(count):s+=f'  · exact Tile{i:03}.nonzero hz\n'
    s+='''
theorem quarter_nonzero : ∀ z ∈ XiAdaptiveTiles.quarter (141/10), xiCompleted z≠0 := by
  intro z hz
  obtain ⟨i,hi⟩ := Cover.quarter_covered z hz
  exact all_tiles_nonzero i hi

theorem rectangle_nonzero {z:ℂ} (hx0:0≤z.re) (hx1:z.re≤1)
    (hy:|z.im|≤(141/10:ℝ)) : xiCompleted z≠0 :=
  XiAdaptiveTiles.xi_rectangle_nonzero_of_quarter quarter_nonzero hx0 hx1 hy

theorem zetaNoLowStripZero : ZetaNoLowStripZero (141/10) := by
  intro s hs
  by_contra h
  have hxi := rectangle_nonzero hs.2.1.le hs.2.2.le (not_le.mp h).le
  exact hxi (xi_zero_of_strip_zero hs.1 hs.2.1 hs.2.2)

/-- The sector bridge remains an explicit classical input. -/
theorem finitePF43 (hB:KatkovaSectorBridge 43) : FinitePF XiMomentCoeff 43 :=
  xi_finitePF43_of_classical zetaNoLowStripZero hB

end Reinmann.XiRectangle
'''
    (ROOT/'XiRectangle/Final.lean').write_text(s)
    (ROOT/'XiRectangle.lean').write_text(HEADER+'import XiRectangle.Final\n')


def generate(plan,indices):
    g=build_graph(); data_file(plan);cover_file(plan);final_file(plan)
    for i in indices: print('Tile',i,tile_file(g,plan['tiles'][i]))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--shared',action='store_true')
    parser.add_argument('--plan',type=Path,default=ROOT/'research/prime_spectral/verification_2026_10_19_rectangle/cover_plan.json')
    parser.add_argument('--tiles',help='comma separated indices or all')
    parser.add_argument('--check',action='store_true',help='compare generated text without modifying files')
    args=parser.parse_args()
    if args.check:
        original_write=Path.write_text
        def check_text(path,text,*a,**kw):
            assert path.read_text()==text, f'Generated source differs: {path}'
            return len(text)
        Path.write_text=check_text
    if args.shared: logs();model(build_graph())
    if args.tiles is not None:
        plan=json.loads(args.plan.read_text())
        indices=range(plan['tile_count']) if args.tiles=='all' else map(int,args.tiles.split(','))
        generate(plan,indices)
    if not args.shared and args.tiles is None: parser.error('choose --shared or --tiles')

if __name__=='__main__': main()
