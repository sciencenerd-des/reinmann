from fractions import Fraction as Q
from pathlib import Path

def q(x):
 f=Q(x);return str(f.numerator) if f.denominator==1 else f'({f.numerator}/{f.denominator})'
def cm(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def cs(a):return abs(a[0])+abs(a[1])
def rn(x):return Q(round(x*2**50),2**50)
def up(x):return Q(-(-x.numerator*2**50//x.denominator),2**50)
def rounding(c,e):
 r=tuple(rn(x) for x in c);return r,up(e+cs((c[0]-r[0],c[1]-r[1])))

def render():
    v0=(Q(196,3185),Q(-112,3185));v={0:(v0,Q(0))}
    for n in range(1,9):
     c,e=v[n-1];raw=cm(v0,tuple(-x/2 for x in c));v[n]=rounding(raw,cs(v0)*e/2)
    l={}
    for n in range(1,9):
     c,e=v[n-1];l[n]=rounding(tuple(x/(2*n) for x in c),e/(2*n))
    s='''/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.HardTileGammaLog
import Reinmann.CertifiedTaylorComposition
import Mathlib.Tactic.FinCases

/-! All nine coefficients of the actual shifted principal logarithm at the hard
centre. Reciprocal and Log recurrences are rounded outward at every order. -/
noncomputable section
namespace Reinmann.HardTileGammaLogJet
open CertifiedTaylorModel CertifiedTaylorComposition
set_option maxRecDepth 10000

def centre : ℂ := (1/2 : ℂ)+14*Complex.I
def shifted (s : ℂ) : ℂ := 12+(1/2)*s

def affineJet : Jet8 := fun k =>
  match k.val with
  | 0 => exact (49/4,7)
  | 1 => exact (1/2,0)
  | _ => zero

'''
    s+='def inverseTable : ℕ → Disk\n'
    for k,(c,e) in v.items():s+=f'  | {k} => ⟨({q(c[0])}, {q(c[1])}), {q(e)}, by norm_num⟩\n'
    s+='  | _ => zero\n\ndef inverseJet : Jet8 := fun k => inverseTable k.val\n\n'
    s+='def logJet : Jet8 := fun k =>\n  match k.val with\n  | 0 => HardTileGammaLog.gammaLogDisk\n'
    for k,(c,e) in l.items():s+=f'  | {k} => ⟨({q(c[0])}, {q(c[1])}), {q(e)}, by norm_num⟩\n'
    s+='  | _ => zero\n\n'
    s += r'''theorem shifted_analytic : AnalyticAt ℂ shifted centre := by
  unfold shifted
  exact analyticAt_const.add (analyticAt_const.mul analyticAt_id)

theorem shifted_value : shifted centre = (49/4 : ℂ)+7*Complex.I := by
  unfold shifted centre
  ring

theorem shifted_nonzero : shifted centre ≠ 0 := by
  rw [shifted_value]
  intro h
  have hr := congrArg Complex.re h
  norm_num at hr

theorem shifted_slit : shifted centre ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  rw [shifted_value]
  norm_num

theorem shifted_coefficient (n : ℕ) :
    coefficient shifted centre n =
      if n = 0 then (49/4 : ℂ)+7*Complex.I else if n = 1 then 1/2 else 0 := by
  unfold coefficient
  rw [show shifted = (fun s : ℂ => 12+(1/2)*s) from rfl]
  by_cases h0 : n = 0
  · subst n
    norm_num [centre]
    ring
  · rw [iteratedDeriv_const_add (Nat.pos_of_ne_zero h0), iteratedDeriv_const_mul_field,
      iteratedDeriv_fun_id]
    by_cases h1 : n = 1
    · subst n
      norm_num
    · simp [h0, h1]

theorem affine_sound : Sound affineJet shifted centre := by
  intro k
  rw [shifted_coefficient]
  fin_cases k <;> norm_num [affineJet, Contains, exact, zero, value]

theorem inverse_sound : Sound inverseJet (fun s => (shifted s)⁻¹) centre := by
  apply inv_coefficients_sound shifted_analytic shifted_nonzero affine_sound
  · rw [shifted_value]
    norm_num [inverseJet, inverseTable, Contains, value, Complex.norm_def,
      Complex.normSq_apply, Complex.inv_re, Complex.inv_im]
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;>
      norm_num [inverseJet, inverseTable, affineJet, CertifiedTaylorModel.get, sum,
        CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qadd, qmul, size]

theorem log_sound : Sound logJet (fun s => Complex.log (shifted s)) centre := by
  apply log_coefficients_sound shifted_analytic shifted_slit affine_sound inverse_sound
  · rw [shifted_value]
    exact HardTileGammaLog.gamma_log_contains
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;>
      norm_num [logJet, inverseJet, inverseTable, affineJet, CertifiedTaylorModel.get, sum,
        CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qadd, qmul, size]

theorem log_radius (k : Fin 9) : ((logJet k).radius : ℝ) ≤ (1/10^12 : ℝ) := by
  fin_cases k <;> norm_num [logJet, HardTileGammaLog.gammaLogDisk]

end Reinmann.HardTileGammaLogJet
'''
    return s


def format_lean(source):
    import re
    source = source.replace('set_option maxHeartbeats 2000000\n', '')
    if 'namespace Reinmann.HardTileLogInputs' in source:
        pattern = r'^(?=(?:private )?theorem )'
    elif 'namespace Reinmann.HardTileGammaLog\n' in source:
        pattern = r'^(?=theorem log_polynomial)'
    else:
        pattern = None
    if pattern:
        source = re.sub(pattern, 'set_option maxHeartbeats 2000000 in\n'
                        '-- Bounded rational series/table arithmetic needs extra elaboration steps.\n',
                        source, flags=re.M)
    # Whitespace in generated arithmetic; preserve prose comments.
    result = []
    comment = False
    for line in source.splitlines():
        if '/-' in line: comment = True
        if not comment:
            for _ in range(2):
                line = re.sub(r'(?<=[\w)\]])([+*/^\-])(?=[\w(\[])', r' \1 ', line)
            line = re.sub(r',(?=[\w(])', ', ', line)
        result.append(line)
        if '-/' in line: comment = False
    return '\n'.join(result)+'\n'


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description='Generate rational proposals; Lean checks every bound.')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    target = Path(__file__).resolve().parents[2]/'Reinmann/HardTileGammaLogJet.lean'
    source = format_lean(render())
    if args.check:
        assert target.read_text() == source, f'Generated source differs: {target}'
    else:
        target.write_text(source)
    print(target.name, 'reproduced' if args.check else 'generated')
