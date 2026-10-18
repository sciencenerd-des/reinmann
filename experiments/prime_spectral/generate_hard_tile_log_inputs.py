from fractions import Fraction
import math
from pathlib import Path

def q(x):
    f=Fraction(x)
    return str(f.numerator) if f.denominator==1 else f'({f.numerator}/{f.denominator})'

def rounded(x): return Fraction(round(x*10**15),10**15)
a2=rounded(math.log(2))

def render():
    s='''/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.CertifiedComplexInputs
import Mathlib.Tactic.IntervalCases

/-! Explicit logarithms for the degree-eight hard-tile finite model.
Every decimal centre is a rational, checked against a Mathlib series bound. -/
noncomputable section
namespace Reinmann.HardTileLogInputs
open CertifiedComplexInputs
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

'''
    s+=f'''theorem log_2 : |Real.log (2:ℝ)-({q(a2)}:ℝ)| ≤ (1/10^15:ℝ) := by
  convert log_enclosure (q := 2) (a := {q(a2)}) (e := 1/10^15) (by norm_num) 20
    (by norm_num [logError, logPartial, Finset.sum_range_succ]) using 1 <;> norm_num

'''
    for n in range(3,22):
        k=n.bit_length()-1
        small=Fraction(n,2**k)
        b=rounded(math.log(float(small)))
        a=rounded(math.log(n))
        s+=f'''theorem log_{n} : |Real.log ({n}:ℝ)-({q(a)}:ℝ)| ≤ (6/10^15:ℝ) := by
  have h := log_scaled_enclosure (q := {q(small)}) (a := {q(a2)}) (b := {q(b)}) {k}
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show ({k}*(1/10^15)+1/10^15:ℚ)+
    |({k}*{q(a2)}+{q(b)}:ℚ)-{q(a)}| ≤ (6/10^15:ℚ) by norm_num) using 1 <;> norm_num

'''
    # pi bound endpoints both scaled by 2
    for name,endpoint in [('lo',Fraction('3.14159265358979323846')),('hi',Fraction('3.14159265358979323847'))]:
        small=endpoint/2;b=rounded(math.log(float(small)));a=rounded(math.log(math.pi))
        s+=f'''private theorem log_pi_{name} :
    |Real.log ({q(endpoint)}:ℝ)-({q(a)}:ℝ)| ≤ (6/10^15:ℝ) := by
  have h := log_scaled_enclosure (q := {q(small)}) (a := {q(a2)}) (b := {q(b)}) 1
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (1*(1/10^15)+1/10^15:ℚ)+
    |(1*{q(a2)}+{q(b)}:ℚ)-{q(a)}| ≤ (6/10^15:ℚ) by norm_num) using 1 <;> norm_num

'''
    s+=f'''theorem log_pi : |Real.log Real.pi-({q(rounded(math.log(math.pi)))}:ℝ)| ≤ (6/10^15:ℝ) := by
  have hlo := abs_le.mp log_pi_lo
  have hhi := abs_le.mp log_pi_hi
  have hl := Real.log_le_log (by norm_num : (0:ℝ)<3.14159265358979323846)
    Real.pi_gt_d20.le
  have hh := Real.log_le_log Real.pi_pos Real.pi_lt_d20.le
  rw [abs_le]
  constructor <;> linarith

end Reinmann.HardTileLogInputs
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
    target = Path(__file__).resolve().parents[2]/'Reinmann/HardTileLogInputs.lean'
    source = format_lean(render())
    if args.check:
        assert target.read_text() == source, f'Generated source differs: {target}'
    else:
        target.write_text(source)
    print(target.name, 'reproduced' if args.check else 'generated')
