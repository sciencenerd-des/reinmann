"""Refine already complete atlases for finite explicit-formula attribution.

Each new disk must lie inside its parent disk or critical-line sign bracket.
No new zero count, RH assumption, or infinite-tail attribution is inferred.
"""
from fractions import Fraction
import json
from pathlib import Path

from flint import acb, arb, ctx
from certified_weil import endpoints
from character_zero_atlas import CharacterControl, OUT, center
from davenport_heilbronn_control import kappa
from epstein_zero_atlas import EpsteinControl
from full_ground_fourier import sha256
from threshold_ground_gap import box

OLD = Path('research/prime_spectral/verification_2026_10_12_sector')


class OriginalDH(CharacterControl):
    def __init__(self):
        super().__init__(5, 2)

    def parameters(self):
        epsilon, numeric_k, _ = super().parameters()
        k = kappa()
        if not numeric_k.overlaps(k):
            raise ArithmeticError('original DH and Gauss normalization disagree')
        return epsilon, k, [arb(0), arb(1), k, -k, arb(-1)]


def refine(name, control, parent_path, dh=False):
    data = json.loads(parent_path.read_text())
    if dh:
        if data['status'] != 'certified_complete_DH_zero_atlas_and_steepest':
            raise ValueError('complete DH parent required')
        off = data['roots']
        lines = json.loads((OLD/'line_brackets_H340.json').read_text())['brackets']
        count, height = data['global_rectangle_count'], 340
    else:
        if data['status'] != 'complete_certified_control_zero_atlas':
            raise ValueError('complete control parent required')
        off, lines = data['right_off_line_zeros'], data['critical_line_disks']
        count, height = data['global_count'], data['height']
    refined_off, refined_line = [], []
    with ctx.workprec(512):
        for record in off:
            fresh = control.disk(center(record), radius='1e-120')
            if not abs(center(fresh)-center(record))+arb(fresh['radius']) < arb(record['radius']):
                raise ArithmeticError('refined off-line disk is not contained in its parent')
            refined_off.append(fresh)
        for i, record in enumerate(lines):
            if dh:
                seed = acb('1/2', arb(str((Fraction(record['lo'])+Fraction(record['hi']))/2)))
            else:
                seed = center(record)
            fresh = control.disk(seed, radius='1e-120', on_line=True)
            if dh:
                if not (box(fresh['imag'])-arb(fresh['radius']) > arb(record['lo'])
                        and box(fresh['imag'])+arb(fresh['radius']) < arb(record['hi'])):
                    raise ArithmeticError('refined DH line disk left its unique-root bracket')
            elif not abs(center(fresh)-center(record))+arb(fresh['radius']) < arb(record['radius']):
                raise ArithmeticError('refined line disk is not contained in its parent')
            refined_line.append(fresh)
            if (i+1) % 50 == 0:
                print(name, 'refined line disks', i+1, flush=True)
    if len(refined_line)+2*len(refined_off) != count:
        raise ArithmeticError('parent count mismatch')
    payload = {'status': 'complete_parent_atlas_with_refined_disks', 'name': name,
               **control.metadata(), 'height': height, 'global_count': count,
               'critical_line_disks': refined_line, 'right_off_line_zeros': refined_off,
               'radius': '1e-120', 'input_sha256': {str(parent_path): sha256(parent_path)},
               'source_sha256': {n: sha256(Path(__file__).with_name(n)) for n in
                   ['refine_calibration_atlases.py', 'character_zero_atlas.py',
                    'epstein_zero_atlas.py', 'davenport_heilbronn_control.py']},
               'scope': 'Parent completeness plus contained refined disks; finite zero sums only, no infinite-tail error bound.'}
    if dh:
        payload['input_sha256'][str(OLD/'line_brackets_H340.json')] = sha256(OLD/'line_brackets_H340.json')
    path = OUT/f'{name}_refined_atlas.json'
    path.write_text(json.dumps(payload, indent=2)+'\n')
    print(name, 'complete refined atlas', count, flush=True)


if __name__ == '__main__':
    refine('dh5', OriginalDH(), OLD/'atlas_H340.json', dh=True)
    for q, label in [(7, 3), (13, 2), (13, 6), (17, 3)]:
        refine(f'q{q}_label{label}', CharacterControl(q, label),
               OUT/f'q{q}_label{label}_H160/atlas.json')
    for d in [5, 6]:
        refine(f'epstein{d}', EpsteinControl(d), OUT/f'epstein{d}_H120/atlas.json')
