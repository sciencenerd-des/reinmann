"""Replay all new control contours at 320 bits and root gates at 640 bits.

This is a second evaluation using the same Arb/FLINT backend, not an
independent analytic implementation. It never discovers or adds zeros.
"""
from fractions import Fraction
import json
from pathlib import Path

from flint import acb, arb, ctx
from character_zero_atlas import OUT, CharacterControl, center, image_segment
from epstein_zero_atlas import EpsteinControl
from certified_weil import endpoints
from full_ground_fourier import sha256
from threshold_ground_gap import box


def root_gate(control, record):
    with ctx.workprec(640):
        old = center(record)
        c = acb(old.real.mid(), old.imag.mid())
        radius = arb(record['radius'])*arb('99/100')
        if not abs(c-old)+radius < arb(record['radius']):
            raise ArithmeticError('replayed disk not contained in parent disk')
        rectangle = acb(arb(c.real, radius), arb(c.imag, radius))
        jet = control.jet(c, 1)
        derivative = acb(jet[1].real.mid(), jet[1].imag.mid())
        lhs = abs(jet[0])+radius*abs(control.jet(rectangle, 1)[1]-derivative)
        rhs = radius*abs(derivative)
        if not lhs < rhs:
            raise ArithmeticError('fresh Rouche inequality failed')
        if record['on_critical_line']:
            if not c.real == arb('1/2'):
                raise ArithmeticError('line disk is not symmetric about the line')
        elif not c.real-radius > arb('1/2'):
            raise ArithmeticError('off-line disk touches the line')
        return c, radius


def replay(folder, control):
    atlas_path = folder/'atlas.json'
    atlas = json.loads(atlas_path.read_text())
    contour = json.loads((folder/'winding.json').read_text())
    line = json.loads((folder/'line_roots.json').read_text())
    off = json.loads((folder/'offline_disks.json').read_text())['roots']
    height = atlas['height']
    total, leaves = arb(0), 0
    with ctx.workprec(320):
        strip = control.strip()
        if any(strip[k] != atlas['strip'][k] for k in ['sigma_left', 'sigma_right']):
            raise ArithmeticError('strip convention changed')
        left, right = arb(strip['sigma_left']), arb(strip['sigma_right'])
        corners = [acb(left), acb(right), acb(right, height), acb(left, height), acb(left)]
        for side in range(4):
            cells = [r for r in contour['segments'] if r['side'] == side]
            previous = Fraction(0)
            a, b = corners[side:side+2]
            for cell in cells:
                lo, hi = Fraction(cell['lo']), Fraction(cell['hi'])
                if not lo == previous or not lo < hi <= 1:
                    raise ArithmeticError('contour coverage is not contiguous')
                previous = hi

                def visit(u, v, depth=0):
                    nonlocal total, leaves
                    x, y = a+(b-a)*arb(str(u)), a+(b-a)*arb(str(v))
                    enclosure = image_segment(control, x, y)
                    if not enclosure.is_finite() or enclosure.contains(0):
                        if depth >= 20:
                            raise ArithmeticError('replay subdivision exhausted')
                        mid = (u+v)/2
                        visit(u, mid, depth+1)
                        visit(mid, v, depth+1)
                        return
                    increment = (control.value(y)/control.value(x)).arg()
                    if not increment.is_finite() or not abs(increment) < arb.pi():
                        raise ArithmeticError('argument increment unresolved')
                    total += increment
                    leaves += 1

                visit(lo, hi)
            if previous != 1:
                raise ArithmeticError('contour side incomplete')
        winding = total/(2*arb.pi())
        if not abs(winding-atlas['global_count']) < arb('1/100'):
            raise ArithmeticError('replayed winding disagrees')
        previous = Fraction(-1)
        for bracket in line['brackets']:
            lo, hi = Fraction(bracket['lo']), Fraction(bracket['hi'])
            if not previous < lo < hi <= height:
                raise ArithmeticError('line brackets not disjoint')
            previous = hi
            values = []
            for t in [lo, hi]:
                v = control.completed(acb('1/2', arb(str(t))))
                if not v.is_finite() or not v.imag.contains(0) or v.real.contains(0):
                    raise ArithmeticError('line sign or functional equation failed')
                values.append(v.real)
            if not values[0]*values[1] < 0:
                raise ArithmeticError('no line sign change')
            disk = bracket['disk']
            if not arb(str(lo)) < box(disk['imag'])-arb(disk['radius']) or not box(disk['imag'])+arb(disk['radius']) < arb(str(hi)):
                raise ArithmeticError('line disk leaves bracket')
    disks = off+[r['disk'] for r in line['brackets']]
    checked = []
    for record in disks:
        c, radius = root_gate(control, record)
        with ctx.workprec(640):
            if not left < c.real-radius or not c.real+radius < right or not 0 < c.imag-radius or not c.imag+radius < height:
                raise ArithmeticError('disk outside contour')
            if any(not abs(c-d) > radius+r for d, r in checked):
                raise ArithmeticError('replayed disks overlap')
            checked.append((c, radius))
    accounted = len(line['brackets'])+2*len(off)
    if not accounted == atlas['global_count'] == contour['count'] or not len(line['brackets']) == line['count']:
        raise ArithmeticError('root counts do not exhaust contour')
    result = {'folder': str(folder), 'status': 'all_contours_and_root_gates_replayed',
              'height': height, 'global_count': accounted,
              'critical_line_count': len(line['brackets']), 'right_off_line_count': len(off),
              'contour_bits': 320, 'root_gate_bits': 640,
              'original_segments': len(contour['segments']), 'replayed_segments': leaves,
              'winding_ball': endpoints(winding),
              'input_sha256': {str(p): sha256(p) for p in
                               [atlas_path, folder/'winding.json', folder/'line_roots.json', folder/'offline_disks.json']}}
    print(folder.name, accounted, 'zeros;', leaves, 'segments;', len(disks), 'root gates', flush=True)
    return result


def run():
    records = []
    for q, label in [(7, 3), (11, 2), (13, 2), (13, 6), (17, 3)]:
        records.append(replay(OUT/f'q{q}_label{label}_H160', CharacterControl(q, label)))
    for d in [5, 6]:
        records.append(replay(OUT/f'epstein{d}_H120', EpsteinControl(d)))
    result = {'status': 'seven_new_atlases_replayed', 'controls': records,
              'source_sha256': {name: sha256(Path(__file__).with_name(name)) for name in
                               ['replay_control_atlases.py', 'character_zero_atlas.py', 'epstein_zero_atlas.py']},
              'scope': 'Fresh higher-precision evaluation on the same FLINT backend; classical functional equations, genus decompositions and argument principle remain written analytic dependencies.'}
    (OUT/'atlas_replays.json').write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    run()
