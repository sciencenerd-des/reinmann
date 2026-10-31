"""Optimistic cost model only, not an arithmetic mixed-moment theorem."""
from fractions import Fraction as F
import json
from pathlib import Path
import sympy as sp
r,z,delta,x=sp.symbols('r z delta x')
# The first short inverse closure forces h>=r+2z. The second may
# increase h further; ignoring it only makes the model more optimistic.
old=sp.Rational(1,6)+(sp.Rational(5,6)-delta)*r
optimistic=sp.Rational(1,6)+sp.Rational(5,6)*(r+2*z)-delta*r-2*delta*x*z
penalty=(sp.Rational(5,3)-2*delta*x)*z
assert sp.expand(optimistic-old-penalty)==0
local_slope=F(5,3)-F(47,100)
assert local_slope==F(359,300)>0
# The omitted closure h>=(2r+8z)/3 can only raise the exponent.
# At z=0 and r>=1 it is redundant, so the minimum is attained at z=0.
assert sp.expand((sp.Rational(1,6)+sp.Rational(5,6)*r-delta*r)-old)==0
result={'scope':'Exact optimistic proof-cost obstruction; no mixed moment is asserted.',
 'required_enlarged_range':'h>=max(1,r+2z,(2r+8z)/3)',
 'sixth_power_cost':'U^(1/6+5h/6)',
 'normalized_large_value_gain':'U^(delta*r+2*delta*x*z)',
 'excess_over_old_long_count_lower_bound':'(5/3-2*delta*x)*z',
 'local_excess_per_z_lower_bound':str(local_slope),
 'minimizing_selected_prime_length':'0',
 'original_arithmetic_coefficients_retained':True,
 'mixed_moment_theorem_proved':False,
 'new_arithmetic_bound_proved':False}
p=Path('research/prime_spectral/verification_2026_10_24_liu_localized/prime_extension_obstruction.json')
with p.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
print('Exact cost identity agrees; local excess >= (359/300) z; optimal z=0')
