"""Complete finite zero atlases for real root-number-one character combinations.

Discovery is only a selector. Completeness requires a zero-excluding contour,
disjoint line brackets, and simple off-line disks whose counts exhaust it.
The bottom side is enclosed numerically, never borrowed from the DH theta proof.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import time

from flint import acb, acb_series, arb, ctx, dirichlet_char
from certified_weil import endpoints
from full_ground_fourier import sha256
from threshold_ground_gap import box

OUT = Path('research/prime_spectral/verification_2026_10_13_calibration')


class CharacterControl:
    def __init__(self, conductor, label):
        self.q, self.label = conductor, label
        self.chi = dirichlet_char(conductor, label)
        self.chibar = dirichlet_char(conductor, pow(label, -1, conductor))
        if not self.chi.is_primitive() or self.chi.parity() != 1:
            raise ValueError('primitive odd character required')
        self.cache = {}

    def metadata(self):
        return {'kind': 'character_combination', 'conductor': self.q,
                'Conrey_label': self.label, 'gamma_degree': 1,
                'normalization': '(q/pi)^(s/2) Gamma((s+1)/2) H(s), root number +1'}

    def near_one_bound(self):
        return 3*sum((abs(x) for x in self.parameters()[2]), arb(0))

    def parameters(self):
        if ctx.prec not in self.cache:
            q = self.q
            tau = sum((self.chi(n)*(acb(0, 2)*arb.pi()*n/q).exp()
                       for n in range(1, q)), acb(0))
            epsilon = tau/acb(0, arb(q).sqrt())
            k = epsilon.imag/(1+epsilon.real)
            if not k.is_finite():
                raise ArithmeticError('root-number normalization unresolved')
            period = [self.chi(n).real+k*self.chi(n).imag for n in range(q)]
            period[0], period[1] = arb(0), arb(1)
            self.cache[ctx.prec] = epsilon, k, period
        return self.cache[ctx.prec]

    def value(self, s):
        _, k, _ = self.parameters()
        return ((1-acb(0, 1)*k)*s.dirichlet_l(self.chi)
                +(1+acb(0, 1)*k)*s.dirichlet_l(self.chibar))/2

    def jet(self, s, degree=2):
        old = ctx.cap
        try:
            ctx.cap = degree+1
            _, k, _ = self.parameters()
            z = acb_series([s, 1])
            return ((1-acb(0, 1)*k)*z.dirichlet_l(self.chi)
                    +(1+acb(0, 1)*k)*z.dirichlet_l(self.chibar))/2
        finally:
            ctx.cap = old

    def completed(self, s):
        return ((s*(arb(self.q)/arb.pi()).log()/2).exp()
                *((s+1)/2).gamma()*self.value(s))

    def strip(self):
        _, _, period = self.parameters()
        for sigma in ['3/2', '7/4', '15/8', '31/16']:
            x = arb(sigma)
            tail = sum((abs(period[n])*acb(x).zeta(arb(n)/self.q).real
                        for n in range(1, self.q)), arb(0))*arb(self.q)**(-x)-1
            if tail < 1:
                return {'sigma_right': sigma, 'sigma_left': str(1-Fraction(sigma)),
                        'absolute_tail': endpoints(tail),
                        'argument': 'Leading coefficient is one. Absolute Dirichlet tail excludes zeros to the right; completed functional equation excludes them to the left. Both strip endpoints lie above the first odd gamma pole at -1.'}
        raise ArithmeticError('no pole-free absolute strip found below sigma=2')

    def disk(self, seed, radius='1e-50', on_line=False):
        with ctx.workprec(512):
            s = acb(seed)
            for _ in range(12):
                f = self.jet(s, 1)
                if f[1].contains(0):
                    raise ArithmeticError('root refinement derivative unresolved')
                w = s-f[0]/f[1]
                s = acb(arb('1/2') if on_line else w.real.mid(), w.imag.mid())
            r = arb(radius)
            rect = acb(arb(s.real.mid(), r), arb(s.imag.mid(), r))
            f = self.jet(s, 1)
            d = acb(f[1].real.mid(), f[1].imag.mid())
            lhs = abs(f[0])+r*abs(self.jet(rect, 1)[1]-d)
            rhs = r*abs(d)
            if not lhs < rhs or (not on_line and not s.real-r > arb('1/2')):
                raise ArithmeticError('simple root disk unresolved')
            return {'real': endpoints(s.real), 'imag': endpoints(s.imag),
                    'radius': radius, 'rouche_left': endpoints(lhs),
                    'rouche_right': endpoints(rhs), 'on_critical_line': on_line}


def center(record):
    return acb(box(record['real']), box(record['imag']))


def discover(control, height, out):
    path = out/'offline_disks.json'
    roots = json.loads(path.read_text())['roots'] if path.exists() else []
    with ctx.workprec(128):
        for real in ['9/10', '13/10', '3/5']:
            for j in range(1, 2*height):
                s = acb(arb(real), arb(j)/2)
                for _ in range(18):
                    f = control.jet(s, 1)
                    if not f[1].is_finite() or f[1].contains(0):
                        break
                    w = s-f[0]/f[1]
                    if not w.is_finite() or not -2 < w.real < 4 or not 0 < w.imag < height+2:
                        break
                    change = abs(w-s)
                    s = acb(w.real.mid(), w.imag.mid())
                    if change < arb('1e-20'):
                        if (s.real > arb('500001/1000000') and s.imag < height
                                and not any(abs(s-center(r)) < arb('1e-7') for r in roots)):
                            roots.append(control.disk(s))
                            roots.sort(key=lambda r: float(box(r['imag']).mid()))
                            path.write_text(json.dumps({'status': 'individual_disks_only',
                                'conductor': control.q, 'label': control.label,
                                'height': height, 'roots': roots}, indent=2)+'\n')
                            print('q', control.q, 'off-line disk', len(roots), s, flush=True)
                        break
                if j % 100 == 0:
                    print('q', control.q, 'seeds', real, j, '/', 2*height, flush=True)
    path.write_text(json.dumps({'status': 'individual_disks_only',
        **control.metadata(), 'height': height, 'roots': roots}, indent=2)+'\n')
    return roots


def line_roots(control, height, out, subdivisions=32):
    records = []
    with ctx.workprec(192):
        previous = None
        for j in range(height*subdivisions+1):
            t = Fraction(j, subdivisions)
            s = acb('1/2', arb(str(t)))
            v = control.completed(s)*(arb.pi()*arb(str(t))/4).exp()
            if not v.imag.contains(0) or v.real.contains(0):
                raise ArithmeticError('line sign unresolved')
            sign = 1 if v.real > 0 else -1
            if previous is not None and sign != previous[1]:
                seed = acb('1/2', arb(str((t+previous[0])/2)))
                disk = control.disk(seed, on_line=True)
                gamma = box(disk['imag'])
                if not gamma-arb(disk['radius']) > arb(str(previous[0])) or not gamma+arb(disk['radius']) < arb(str(t)):
                    raise ArithmeticError('refined line disk left its sign bracket')
                records.append({'lo': str(previous[0]), 'hi': str(t),
                                'value_lo': endpoints(previous[2]), 'value_hi': endpoints(v.real),
                                'disk': disk})
            previous = t, sign, v.real
            if j and j % 1024 == 0:
                print('q', control.q, 'line height', j/subdivisions, 'count', len(records), flush=True)
    result = {'status': 'disjoint_line_sign_brackets_and_refined_disks',
              'height': height, 'subdivisions': subdivisions, 'count': len(records), 'brackets': records}
    (out/'line_roots.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


def image_segment(control, a, b):
    midpoint, delta = (a+b)/2, (b-a)/2
    rectangle = acb(a.real.union(b.real), a.imag.union(b.imag))
    radius = abs(rectangle-1).upper()
    if radius < arb('1/4'):
        # Direct L-series balls containing s=1 are indeterminate in FLINT.
        # On |s-1|<=1/2, partial summation and the zero period sum give
        # |H(s)| <= |s| sum|a_n|/Re(s) <= 3 sum|a_n|.
        # Cauchy's estimate bounds the Taylor remainder about the exact
        # center s=1. This encloses the whole cell without a pole division.
        cap = 12
        coefficients = control.jet(acb(1), cap)
        z, value = rectangle-1, coefficients[cap]
        for n in range(cap-1, -1, -1):
            value = value*z+coefficients[n]
        remainder = control.near_one_bound()*(2*radius)**(cap+1)/(1-2*radius)
        return value+acb(arb(0, remainder), arb(0, remainder))
    f = control.jet(midpoint, 1)
    error = abs(control.jet(rectangle, 2)[2])*abs(delta)**2
    return (f[0]+f[1]*acb(arb(0, abs(delta.real)), arb(0, abs(delta.imag)))
            +acb(arb(0, error), arb(0, error)))


def winding(control, height, strip, out):
    records, total, evaluations = [], arb(0), 0
    left, right = arb(strip['sigma_left']), arb(strip['sigma_right'])
    corners = [acb(left, 0), acb(right, 0), acb(right, height), acb(left, height), acb(left, 0)]
    with ctx.workprec(256):
        for side, (a, b) in enumerate(zip(corners, corners[1:])):
            def visit(lo, hi, depth=0):
                nonlocal total, evaluations
                x, y = a+(b-a)*arb(str(lo)), a+(b-a)*arb(str(hi))
                image = image_segment(control, x, y)
                evaluations += 1
                if not image.is_finite() or image.contains(0):
                    if depth >= 32:
                        raise ArithmeticError('contour subdivision exhausted, including real bottom')
                    mid = (lo+hi)/2
                    visit(lo, mid, depth+1)
                    visit(mid, hi, depth+1)
                    return
                increment = (control.value(y)/control.value(x)).arg()
                if not abs(increment) < arb.pi():
                    raise ArithmeticError('argument branch unresolved')
                total += increment
                records.append({'side': side, 'lo': str(lo), 'hi': str(hi),
                                'image_real': endpoints(image.real), 'image_imag': endpoints(image.imag),
                                'increment': endpoints(increment)})
            visit(Fraction(0), Fraction(1))
            print('q', control.q, 'contour side', side, 'leaves', len(records), flush=True)
        value = total/(2*arb.pi())
        count = round(float(value.mid()))
        if not abs(value-count) < arb('1/100'):
            raise ArithmeticError('integer contour count unresolved')
    result = {'status': 'zero_excluding_all_four_sides', 'count': count,
              'winding_ball': endpoints(value), 'evaluations': evaluations, 'segments': records}
    (out/'winding.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


def run(q, label, height, action='all'):
    out = OUT/f'q{q}_label{label}_H{height}'
    control = CharacterControl(q, label)
    return run_control(control, height, out, action)


def run_control(control, height, out, action='all'):
    out.mkdir(parents=True, exist_ok=True)
    if action in ['all', 'discover']:
        discover(control, height, out)
    if action in ['all', 'line']:
        line_roots(control, height, out)
    with ctx.workprec(384):
        strip = control.strip()
    if action in ['all', 'winding']:
        winding(control, height, strip, out)
    if action not in ['all', 'assemble']:
        return
    roots = json.loads((out/'offline_disks.json').read_text())['roots']
    line = json.loads((out/'line_roots.json').read_text())
    contour = json.loads((out/'winding.json').read_text())
    with ctx.workprec(384):
        left, right = arb(strip['sigma_left']), arb(strip['sigma_right'])
        all_disks = roots+[r['disk'] for r in line['brackets']]
        for i, record in enumerate(all_disks):
            s, r = center(record), arb(record['radius'])
            if not (left < s.real-r and s.real+r < right and 0 < s.imag-r and s.imag+r < height):
                raise ArithmeticError('root disk not inside contour')
            if not box(record['rouche_left']) < box(record['rouche_right']):
                raise ArithmeticError('invalid root inequality')
            if any(not abs(s-center(other)) > r+arb(other['radius']) for other in all_disks[:i]):
                raise ArithmeticError('root disks overlap')
        accounted = line['count']+2*len(roots)
        if accounted != contour['count']:
            raise ArithmeticError(f'incomplete atlas: {accounted} accounted, {contour["count"]} counted')
        epsilon, k, _ = control.parameters()
        checks = []
        for s in [acb('.7', '12'), acb('.3', '40'), acb('1.3', '23')]:
            defect = control.completed(s)-control.completed(1-s)
            if not defect.contains(0):
                raise ArithmeticError('functional equation normalization check failed')
            checks.append({'real': endpoints(defect.real), 'imag': endpoints(defect.imag)})
        result = {'status': 'complete_certified_control_zero_atlas', **control.metadata(),
                  'height': height, 'strip': strip,
                  'global_count': contour['count'], 'critical_line_count': line['count'],
                  'right_off_line_count': len(roots), 'remaining_count': 0,
                  'lowest_right_off_line_zero': roots[0] if roots else None,
                  'right_off_line_zeros': roots,
                  'critical_line_disks': [r['disk'] for r in line['brackets']],
                  'kappa': endpoints(k), 'root_number_real': endpoints(epsilon.real),
                  'root_number_imag': endpoints(epsilon.imag), 'functional_equation_checks': checks,
                  'input_sha256': {str(out/name): sha256(out/name) for name in
                                   ['offline_disks.json', 'line_roots.json', 'winding.json']},
                  'source_sha256': {'character_zero_atlas.py': sha256(Path(__file__))},
                  'scope': 'Complete only below the stated height; no global steepest-zero claim. Uses classical primitive-character functional equations and Arb, not a Lean analytic formalization.'}
    (out/'atlas.json').write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'], control.q, 'count', accounted, 'off-line pairs', len(roots), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--conductor', type=int, required=True)
    p.add_argument('--label', type=int, required=True)
    p.add_argument('--height', type=int, default=160)
    p.add_argument('--action', choices=['all', 'discover', 'line', 'winding', 'assemble'], default='all')
    args = p.parse_args()
    if not 2 < args.conductor <= 101 or not 1 <= args.height <= 500:
        p.error('bounded conductor and height required')
    run(args.conductor, args.label, args.height, args.action)
