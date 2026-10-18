from fractions import Fraction as Q
from pathlib import Path
from generate_hard_tile_log_inputs import q, a2


def render():
    def rnd(x, bits=50): return Q(round(x*2**bits),2**bits)
    def ceilgrid(x, bits=50): return Q(-(-x.numerator*2**bits//x.denominator),2**bits)
    def cmul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
    def cs(a): return abs(a[0])+abs(a[1])
    z=(Q(-15,64),Q(7,16));table={48:((Q(0),Q(0)),Q(0))}
    for k in reversed(range(48)):
        prev,r=table[k+1];p=cmul(z,prev);coef=Q((-1)**(k+1),k) if k else Q(0)
        raw=(p[0]+coef,p[1]);c=tuple(rnd(x) for x in raw)
        e=ceilgrid(cs(z)*r+cs((raw[0]-c[0],raw[1]-c[1])))
        table[k]=(c,e)
    poly,ep=table[0];raw=(4*a2+poly[0],poly[1]);err=4*Q(1,10**15)+ep+Q(1,10**15)
    final=tuple(rnd(x,45) for x in raw);ef=ceilgrid(err+cs((raw[0]-final[0],raw[1]-final[1])),45)

    template = r'''/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.CertifiedHorner
import Reinmann.CertifiedComplexInputs
import Reinmann.HardTileLogInputs
import Mathlib.Tactic.IntervalCases

/-! A kernel-checked principal logarithm at Gamma's actual shifted hard centre.
Every Horner step is rounded outward onto a 50-bit rational grid. -/
noncomputable section
namespace Reinmann.HardTileGammaLog
open CertifiedTaylorModel CertifiedComplexInputs CertifiedHorner
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

__LOG_TABLE__

theorem log_polynomial :
    Contains (logTable 0) (Complex.logTaylor 48 ((-15/64 : ℂ)+(7/16)*Complex.I)) := by
  rw [← log_horner_eq]
  apply horner_contains (input := exact (-15/64,7/16))
  · simpa [value] using contains_exact ((-15/64 : ℚ),7/16)
  · simp [logTable, Contains, value]
  · intro k hk
    interval_cases k <;>
      norm_num [logTable, CertifiedTaylorModel.add, CertifiedTaylorModel.mul,
        exact, qadd, qmul, size]

def logTwoDisk : Disk := ⟨((138629436111989/200000000000000), 0), 1/10^15, by norm_num⟩
def gammaLogDisk : Disk := ⟨((93126327582951/35184372088832), (18265830052121/35184372088832)), (1/35184372088832), by norm_num⟩

theorem log_two_contains : Contains logTwoDisk (Real.log (2:ℝ) : ℂ) := by
  unfold Contains logTwoDisk
  have hv : value ((138629436111989/200000000000000 : ℚ),0) =
      ((138629436111989/200000000000000 : ℝ) : ℂ) := by
    norm_num [value]
  rw [hv, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  convert HardTileLogInputs.log_2 using 1 <;> norm_num

theorem gamma_log_contains :
    Contains gammaLogDisk (Complex.log ((49/4 : ℂ)+7*Complex.I)) := by
  have hs := log_series_contains gamma_log_centre_norm log_polynomial
  have h4 := contains_mul (contains_exact ((4 : ℚ),0)) log_two_contains
  have hh := contains_add h4 hs
  have h16 : Real.log (16:ℝ) = 4*Real.log 2 := by
    have h := Real.log_pow (2:ℝ) 4
    norm_num only at h
    exact h
  have he : value ((4:ℚ),0)*(Real.log (2:ℝ) : ℂ) +
      Complex.log (1+((-15/64:ℂ)+(7/16)*Complex.I)) =
      Complex.log ((49/4:ℂ)+7*Complex.I) := by
    rw [gamma_log_centre_reduce, h16]
    simp [value]
  rw [he] at hh
  apply contains_round gammaLogDisk.radius_nonneg ?_ hh
  norm_num [gammaLogDisk, logTwoDisk, logTable, inflate,
    CertifiedTaylorModel.add, CertifiedTaylorModel.mul, exact, qadd, qmul, size]

theorem gamma_log_radius : (gammaLogDisk.radius : ℝ) ≤ (1/10^12 : ℝ) := by
  norm_num [gammaLogDisk]

end Reinmann.HardTileGammaLog
'''
    table_source='def logTable : ℕ → Disk\n'
    for k,(c,e) in table.items():
        table_source+=f'  | {k} => ⟨({q(c[0])}, {q(c[1])}), {q(e)}, by norm_num⟩\n'
    table_source+='  | _ => zero\n'
    return template.replace('__LOG_TABLE__',table_source)


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
    target = Path(__file__).resolve().parents[2]/'Reinmann/HardTileGammaLog.lean'
    source = format_lean(render())
    if args.check:
        assert target.read_text() == source, f'Generated source differs: {target}'
    else:
        target.write_text(source)
    print(target.name, 'reproduced' if args.check else 'generated')
