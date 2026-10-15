"""Replay all contour segments, line endpoints and root disks at higher precision."""
from fractions import Fraction
import json
from flint import acb, arb, ctx
from certified_weil import endpoints
from dh_zero_atlas import OUT, H, certify_disk, root_center, segment_image, tail_strip
from full_ground_fourier import sha256
from threshold_ground_gap import box


def replay():
    atlas_path = OUT/'atlas_H340.json'
    atlas = json.loads(atlas_path.read_text())
    for name, expected in atlas['input_sha256'].items():
        from pathlib import Path
        if sha256(Path(name)) != expected:
            raise ValueError('atlas input provenance mismatch')
    if atlas['status'] != 'certified_complete_DH_zero_atlas_and_steepest':
        raise ValueError('complete atlas required')
    contour = json.loads((OUT/'winding_H340.json').read_text())
    line = json.loads((OUT/'line_brackets_H340.json').read_text())
    with ctx.workprec(320):
        corners = [acb('3/2', 0), acb('3/2', 340), acb('-1/2', 340), acb('-1/2', 0)]
        total, last, replay_leaves = arb(0), [Fraction(0)]*3, 0
        def increment(left, right, depth=0):
            nonlocal replay_leaves
            image = segment_image(left, right)
            if not image.is_finite() or image.contains(0):
                if depth >= 16:
                    raise ArithmeticError('replayed boundary image unresolved')
                middle = (left+right)/2
                return increment(left, middle, depth+1)+increment(middle, right, depth+1)
            inc = (H(right)/H(left)).arg()
            if not abs(inc) < arb.pi():
                raise ArithmeticError('replayed boundary argument branch failed')
            replay_leaves += 1
            return inc
        for index, rec in enumerate(contour['segments']):
            side = rec['side']
            lo, hi = Fraction(rec['lo']), Fraction(rec['hi'])
            if lo != last[side] or not lo < hi <= 1:
                raise ValueError('contour does not tile side')
            a, b = corners[side:side+2]
            left, right = a+(b-a)*arb(str(lo)), a+(b-a)*arb(str(hi))
            inc = increment(left, right)
            if not abs(inc) < arb.pi() or not inc.overlaps(box(rec['argument_increment'])):
                raise ArithmeticError('replayed argument increment failed')
            total += inc
            last[side] = hi
            if index % 1000 == 999:
                print('replayed contour segments', index+1, flush=True)
        count = total/(2*arb.pi())
        if last != [Fraction(1)]*3 or not abs(count-atlas['global_rectangle_count']) < arb('1/100'):
            raise ArithmeticError('replayed winding count failed')
        previous_hi = Fraction(-1)
        for rec in line['brackets']:
            lo, hi = Fraction(rec['lo']), Fraction(rec['hi'])
            if not previous_hi <= lo < hi <= 340:
                raise ValueError('line brackets overlap or leave counting domain')
            values = []
            for t in [lo, hi]:
                s = acb('1/2', arb(str(t)))
                v = (s*(5/arb.pi()).log()/2).exp()*((s+1)/2).gamma()*H(s)*(arb.pi()*arb(str(t))/4).exp()
                if not v.imag.contains(0) or v.real.contains(0):
                    raise ArithmeticError('replayed critical-line endpoint failed')
                values.append(v.real)
            if not values[0]*values[1] < 0:
                raise ArithmeticError('replayed sign change failed')
            previous_hi = hi
        for rec in atlas['roots']:
            fresh = certify_disk(root_center(rec), rec['radius'])
            if not abs(root_center(fresh)-root_center(rec)) < arb(rec['radius'])/2:
                raise ArithmeticError('replayed root selected a different disk')
        result = {'status': 'all_atlas_segments_brackets_and_disks_replayed',
            'contour_segments': len(contour['segments']), 'line_brackets': len(line['brackets']),
            'higher_precision_subdivision_leaves': replay_leaves,
            'right_disks': len(atlas['roots']), 'winding_ball': endpoints(count),
            'tail_strip': tail_strip(), 'atlas_sha256': sha256(atlas_path),
            'trust_boundary': 'Higher-precision replay of Arb computation; same FLINT backend and analytic functional-equation/theta dependencies, not an independent implementation or Lean proof.'}
    (OUT/'atlas_replay.json').write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'], flush=True)


if __name__ == '__main__':
    replay()
