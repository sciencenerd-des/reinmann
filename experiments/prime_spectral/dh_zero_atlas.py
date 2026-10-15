"""Complete DH zero atlas: contour winding + line roots + off-line disks.

Completeness is claimed ONLY when the global count equals the disjoint
critical-line sign brackets plus twice the certified right-hand disks.
The latter factor uses the completed functional equation and conjugation.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path

from flint import acb, acb_series, arb, ctx, dirichlet_char

from certified_weil import endpoints
from davenport_heilbronn_control import kappa
from full_ground_fourier import sha256
from threshold_ground_gap import box

OUT = Path('research/prime_spectral/verification_2026_10_12_sector')
CHI, CHIBAR = dirichlet_char(5, 2), dirichlet_char(5, 3)


def H(s):
    k, I = kappa(), acb(0, 1)
    return ((1-I*k)*s.dirichlet_l(CHI)+(1+I*k)*s.dirichlet_l(CHIBAR))/2


def jet(s, degree=2):
    old = ctx.cap
    try:
        ctx.cap = degree+1
        z = acb_series([s, 1])
        k = kappa()
        return sum((a*z.zeta(arb(r)/5) for r, a in
                    [(1, 1), (2, k), (3, -k), (4, -1)]),
                   acb_series([0]))*(-z*arb(5).log()).exp()
    finally:
        ctx.cap = old


def tail_strip():
    with ctx.workprec(256):
        s, k = arb('3/2'), kappa()
        tail = 5**(-s)*(acb(s).zeta(arb(1)/5).real
                        +k*acb(s).zeta(arb(2)/5).real
                        +k*acb(s).zeta(arb(3)/5).real
                        +acb(s).zeta(arb(4)/5).real)-1
        if not tail < 1:
            raise ArithmeticError('absolute Dirichlet-tail zero-free gate failed')
        return {'sigma_right': '3/2', 'absolute_tail': endpoints(tail),
                'centered_horizontal_bound': '1',
                'argument': 'Absolute tail decreases in sigma. H is nonzero for Re(s)>=3/2; the entire completed functional equation excludes Re(s)<=-1/2.'}


def certify_disk(seed, radius='1e-20'):
    with ctx.workprec(384):
        s = acb(seed)
        for _ in range(12):
            f = jet(s, 1)
            if f[1].contains(0):
                raise ArithmeticError('Newton selector derivative unresolved')
            w = s-f[0]/f[1]
            s = acb(w.real.mid(), w.imag.mid())
        r = arb(radius)
        rectangle = acb(arb(s.real.mid(), r), arb(s.imag.mid(), r))
        f = jet(s, 1)
        d = acb(f[1].real.mid(), f[1].imag.mid())
        err = abs(jet(rectangle, 1)[1]-d)
        left, right = abs(f[0])+r*err, r*abs(d)
        if not left < right or not s.real-r > arb('1/2'):
            raise ArithmeticError('right off-line Rouché disk gate failed')
        delta = arb(s.real.mid(), r)-arb('1/2')
        gamma = arb(s.imag.mid(), r)
        phi = 2*(delta/gamma).atan()
        return {'real': endpoints(s.real), 'imag': endpoints(s.imag),
                'radius': radius, 'rouche_left': endpoints(left),
                'rouche_right': endpoints(right),
                'folded_deviation_angle': endpoints(phi)}


def root_center(record):
    return acb(box(record['real']), box(record['imag']))


def discover(height=340):
    OUT.mkdir(parents=True, exist_ok=True)
    path = OUT/f'offline_disks_H{height}.json'
    roots = json.loads(path.read_text())['roots'] if path.exists() else []
    with ctx.workprec(192):
        for real in ['9/10', '13/10']:
            for j in range(1, 2*height):
                s = acb(arb(real), arb(j)/2)
                for _ in range(18):
                    try:
                        f = jet(s, 1)
                        if f[1].contains(0):
                            break
                        w = s-f[0]/f[1]
                        if not w.is_finite() or not -2 < w.real < 3 or not -2 < w.imag < height+5:
                            break
                        change = abs(w-s)
                        s = acb(w.real.mid(), w.imag.mid())
                        if change < arb('1e-25'):
                            if (s.real > arb('500001/1000000') and 0 < s.imag < height
                                    and not any(abs(s-root_center(r)) < arb('1e-8') for r in roots)):
                                try:
                                    record = certify_disk(s)
                                except ArithmeticError:
                                    break
                                roots.append(record)
                                roots.sort(key=lambda r: float(box(r['imag']).mid()))
                                path.write_text(json.dumps({'status': 'certified_individual_disks_not_yet_complete',
                                    'height': height, 'roots': roots}, indent=2)+'\n')
                                print('new right disk', len(roots), s, flush=True)
                            break
                    except (ValueError, ZeroDivisionError):
                        break
                if j % 100 == 0:
                    print('search', real, j, '/', 2*height, flush=True)
    return roots


def line_brackets(height=340, subdivisions=16):
    brackets = []
    with ctx.workprec(192):
        old_t, old_sign, old_value = None, None, None
        for j in range(height*subdivisions+1):
            t = arb(j)/subdivisions
            s = acb(arb('1/2'), t)
            value = (s*(5/arb.pi()).log()/2).exp()*((s+1)/2).gamma()*H(s)*(arb.pi()*t/4).exp()
            if not value.imag.contains(0) or value.real.contains(0):
                raise ArithmeticError('critical-line sign unresolved')
            sign = 1 if value.real > 0 else -1
            if old_sign is not None and sign != old_sign:
                brackets.append({'lo': str(old_t), 'hi': str(Fraction(j, subdivisions)),
                                 'value_lo': endpoints(old_value), 'value_hi': endpoints(value.real)})
            old_t, old_sign, old_value = Fraction(j, subdivisions), sign, value.real
            if j and j % 1024 == 0:
                print('line signs height', j/subdivisions, 'brackets', len(brackets), flush=True)
    result = {'status': 'disjoint_certified_critical_line_sign_brackets',
              'height': height, 'subdivisions': subdivisions,
              'count_at_least': len(brackets), 'brackets': brackets}
    (OUT/f'line_brackets_H{height}.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


def segment_image(a, b):
    center, delta = (a+b)/2, (b-a)/2
    f = jet(center, 1)
    rectangle = acb(a.real.union(b.real), a.imag.union(b.imag))
    second = jet(rectangle, 2)[2]
    err = abs(second)*abs(delta)**2
    return f[0]+f[1]*acb(arb(0, abs(delta.real)), arb(0, abs(delta.imag)))+acb(arb(0, err), arb(0, err))


def winding(height=340):
    # Counterclockwise rectangle. The bottom H(x)>0, -1/2<=x<=3/2,
    # follows from the positive theta integral and Gamma((x+1)/2)>0.
    # Its argument increment is exactly zero (written analytic dependency).
    records, evaluations = [], 0
    with ctx.workprec(256):
        corners = [acb('3/2', 0), acb('3/2', height),
                   acb('-1/2', height), acb('-1/2', 0)]
        total = arb(0)
        for side, (a, b) in enumerate(zip(corners, corners[1:])):
            def visit(lo, hi, depth=0):
                nonlocal total, evaluations
                left = a+(b-a)*arb(str(lo))
                right = a+(b-a)*arb(str(hi))
                image = segment_image(left, right)
                evaluations += 1
                if not image.is_finite() or image.contains(0):
                    if depth >= 30:
                        raise ArithmeticError('boundary image unresolved at subdivision limit')
                    mid = (lo+hi)/2
                    visit(lo, mid, depth+1)
                    visit(mid, hi, depth+1)
                    return
                inc = (H(right)/H(left)).arg()
                if not inc.is_finite() or not abs(inc) < arb.pi():
                    raise ArithmeticError('boundary increment branch unresolved')
                total += inc
                records.append({'side': side, 'lo': str(lo), 'hi': str(hi),
                                'image_real': endpoints(image.real),
                                'image_imag': endpoints(image.imag),
                                'argument_increment': endpoints(inc)})
            visit(Fraction(0), Fraction(1))
            print('contour side', side, 'leaves', len(records), flush=True)
        count = total/(2*arb.pi())
        candidate = round(float(count.mid()))
        if not count.contains(candidate) or not abs(count-candidate) < arb('1/10'):
            raise ArithmeticError('integer winding count unresolved')
        result = {'status': 'certified_DH_rectangle_winding',
                  'height': height, 'sigma_left': '-1/2', 'sigma_right': '3/2',
                  'count': candidate, 'winding_ball': endpoints(count),
                  'evaluations': evaluations, 'segments': records,
                  'bottom_dependency': 'H(x)>0 on [-1/2,3/2] by the positive theta integral in DH_FALSIFICATION_2026_10_12.md; hence bottom argument increment is zero.'}
    (OUT/f'winding_H{height}.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


def assemble_atlas(height=340):
    roots_path = OUT/f'offline_disks_H{height}.json'
    line_path = OUT/f'line_brackets_H{height}.json'
    winding_path = OUT/f'winding_H{height}.json'
    roots = json.loads(roots_path.read_text())['roots']
    line = json.loads(line_path.read_text())
    contour = json.loads(winding_path.read_text())
    with ctx.workprec(384):
        for i, r in enumerate(roots):
            s, radius = root_center(r), arb(r['radius'])
            if not (s.real-radius > arb('1/2') and s.real+radius < arb('3/2')
                    and s.imag-radius > 0 and s.imag+radius < height
                    and box(r['rouche_left']) < box(r['rouche_right'])):
                raise ArithmeticError('disk containment or Rouche certificate invalid')
            if any(not abs(s-root_center(t)) > radius+arb(t['radius']) for t in roots[:i]):
                raise ArithmeticError('overlapping root disks')
        accounted = line['count_at_least']+2*len(roots)
        complete = accounted == contour['count']
        steepest = max(roots, key=lambda r: float(box(r['folded_deviation_angle']).mid()))
        phi = box(steepest['folded_deviation_angle'])
        high_phi = 2*(arb(1)/height).atan()
        comparison = (all(phi > box(r['folded_deviation_angle'])
                          for r in roots if r is not steepest) and phi > high_phi)
        ratio = arb.pi()/phi
        rank = int(ratio.floor().fmpq())-1
        if not rank+1 < ratio < rank+2:
            raise ArithmeticError('sector rank threshold unresolved')
        result = {'status': 'certified_complete_DH_zero_atlas_and_steepest'
                  if complete and comparison else 'incomplete_DH_zero_atlas',
                  'height': height, 'global_rectangle_count': contour['count'],
                  'critical_line_bracket_count': line['count_at_least'],
                  'right_off_line_disks': len(roots), 'accounted_count': accounted,
                  'remaining_count': contour['count']-accounted,
                  'strip_certificate': tail_strip(), 'steepest_candidate': steepest,
                  'maximum_high_zero_deviation': endpoints(high_phi),
                  'pi_over_steepest_deviation': endpoints(ratio),
                  'conditional_sector_guaranteed_PF_rank': rank,
                  'quadratic_first_negative_rank': rank+1,
                  'roots': roots,
                  'input_sha256': {str(p): sha256(p) for p in [roots_path, line_path, winding_path]},
                  'source_sha256': {n: sha256(Path(__file__).with_name(n))
                                    for n in ['dh_zero_atlas.py', 'davenport_heilbronn_control.py']},
                  'scope': 'PF rank follows from the Schoenberg sufficient sector theorem, genus-zero factorization and the completed functional equation, only if atlas status is complete. No necessity or first full-function minor failure is claimed.'}
    (OUT/f'atlas_H{height}.json').write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'], 'count', contour['count'], 'accounted', accounted,
          'sector rank', rank, flush=True)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['discover', 'line', 'winding', 'assemble'])
    parser.add_argument('--height', type=int, default=340)
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    {'discover': discover, 'line': line_brackets, 'winding': winding,
     'assemble': assemble_atlas}[args.action](args.height)
