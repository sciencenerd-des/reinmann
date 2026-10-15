"""Complete atlases for the principal Epstein forms x^2+5y^2 and x^2+6y^2.

The contour target is F(s)=(s-1) E(s,Q)/2, not the meromorphic Epstein series.
Class-number-two genus decompositions are checked against representation counts.
"""
import argparse
import json
from pathlib import Path

from flint import acb, acb_series, arb, ctx, dirichlet_char
from character_zero_atlas import OUT, run_control
from certified_weil import endpoints
from full_ground_fourier import sha256


class EpsteinControl:
    def __init__(self, d):
        if d not in [5, 6]:
            raise ValueError('only the two stated class-number-two forms are implemented')
        self.q, self.label, self.d = d, 0, d
        data = {5: [(20, 19), (4, 3), (5, 4)],
                6: [(24, 5), (3, 2), (8, 5)]}[d]
        self.characters = [(q, dirichlet_char(q, label)) for q, label in data]
        self.one_cache = {}
        if any(not chi.is_primitive() for _, chi in self.characters):
            raise ArithmeticError('fundamental discriminant character must be primitive')

    def metadata(self):
        return {'kind': 'epstein_principal_form', 'form_parameter_d': self.d,
                'gamma_degree': 2, 'entire_contour_target': '(s-1) E(s,x^2+d*y^2)/2',
                'normalization': 's*(s-1)*(sqrt(d)/pi)^s*Gamma(s)*E(s,Q)/2',
                'genus_factorization': {5: '(zeta*L(-20)+L(-4)*L(5))/2',
                                        6: '(zeta*L(-24)+L(-3)*L(8))/2'}[self.d]}

    def parameters(self):
        return acb(1), arb(0), []

    def near_one_bound(self):
        # |(s-1)zeta(s)|<=3 on |s-1|<=1/2 follows from fractional-part
        # partial summation. Each primitive L is <=3*sum_period|chi| there.
        M = [sum((abs(chi(n)) for n in range(q)), arb(0)) for q, chi in self.characters]
        return (9*M[0]+arb('9/2')*M[1]*M[2])/2

    def raw_jet(self, s, degree=2):
        old = ctx.cap
        try:
            ctx.cap = degree+1
            z = acb_series([s, 1])
            L = [z.dirichlet_l(chi) for _, chi in self.characters]
            # Deflation works at the exact center 1. Nonzero-radius cells
            # containing 1 are handled by the shared Cauchy Taylor image.
            regular_zeta = 1+(z-1)*z.zeta(deflate=True)
            return (regular_zeta*L[0]+(z-1)*L[1]*L[2])/2
        finally:
            ctx.cap = old

    def one_polynomial(self, z, degree):
        radius = abs(z[0]-1).upper()
        if not radius < arb('1/4'):
            raise ValueError('Taylor image around 1 needs radius <1/4')
        cap = degree+24
        key = ctx.prec, cap
        if key not in self.one_cache:
            self.one_cache[key] = self.raw_jet(acb(1), cap)
        coefficients = self.one_cache[key]
        w, value = z-1, acb_series([coefficients[cap]])
        for n in range(cap-1, -1, -1):
            value = value*w+coefficients[n]
        outer = (radius+arb('1/2'))/2
        remainder = self.near_one_bound()*(2*outer)**(cap+1)/(1-2*outer)
        distance = outer-radius
        for j in range(degree+1):
            error = remainder/distance**j
            if j == 0:
                error = self.near_one_bound()*(2*radius)**(cap+1)/(1-2*radius)
            value[j] += acb(arb(0, error.upper()), arb(0, error.upper()))
        return value

    def jet(self, s, degree=2):
        old = ctx.cap
        try:
            ctx.cap = degree+1
            z = acb_series([s, 1])
            if abs(acb(s)-1).upper() < arb('1/4') and not acb(s) == 1:
                return self.one_polynomial(z, degree)
            if abs(acb(s)).upper() < arb('1/4'):
                # xi(s)=Gamma(1+s)*(sqrt(d)/pi)^s F(s) is symmetric.
                # This gamma ratio is regular at 0, unlike the even L
                # factor's internal functional-equation evaluation there.
                scale = arb(self.d).sqrt()/arb.pi()
                return ((2-z).gamma()/(1+z).gamma()
                        *((1-2*z)*scale.log()).exp()*self.one_polynomial(1-z, degree))
            return self.raw_jet(s, degree)
        finally:
            ctx.cap = old

    def value(self, s):
        return self.jet(s, 0)[0]

    def completed(self, s):
        return s*s.gamma()*(s*(arb(self.d).sqrt()/arb.pi()).log()).exp()*self.value(s)

    def strip(self):
        for sigma in ['3/2', '7/4', '15/8', '31/16']:
            x = arb(sigma)
            tail = (self.value(acb(x))/(x-1)).real-1
            if tail < 1:
                return {'sigma_right': sigma, 'sigma_left': str(1-arb(sigma).mid().fmpq()),
                        'absolute_tail': endpoints(tail),
                        'argument': 'Nonnegative representation coefficients and a_1=1 exclude Epstein zeros to the right. The entire completed functional equation reflects this exclusion. F=(s-1)E/2 cancels the pole at 1; no negative integral gamma pole lies in this strip.'}
        raise ArithmeticError('no pole-free leading-term strip found below sigma=2')

    def disk(self, seed, radius='1e-50', on_line=False):
        # The same Rouche gate applies to this analytic contour target.
        from character_zero_atlas import CharacterControl
        return CharacterControl.disk(self, seed, radius, on_line)


def run(d, height, action):
    out = OUT/f'epstein{d}_H{height}'
    run_control(EpsteinControl(d), height, out, action)
    if action in ['all', 'assemble']:
        path = out/'atlas.json'
        data = json.loads(path.read_text())
        for key in ['kappa', 'root_number_real', 'root_number_imag']:
            data.pop(key, None)
        data['source_sha256']['epstein_zero_atlas.py'] = sha256(Path(__file__))
        path.write_text(json.dumps(data, indent=2)+'\n')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--d', type=int, choices=[5, 6], required=True)
    p.add_argument('--height', type=int, default=160)
    p.add_argument('--action', choices=['all', 'discover', 'line', 'winding', 'assemble'], default='all')
    args = p.parse_args()
    if not 1 <= args.height <= 500:
        p.error('bounded height required')
    run(args.d, args.height, args.action)
