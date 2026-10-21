"""Generate new optional band certificates without rewriting historical tiles.

The old rational graph and source renderer are reused as proposal code. Only
explicit output templates are adapted; all mathematical transfers use the new
Lean-proved height-32 bounds. Every output path is checked before writing.
"""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
from unittest.mock import patch

import generate_rectangle_certificates as base
import rectangle_model as model
from degree8_scalar_certificates import Disk, exact

ROOT = Path(__file__).resolve().parents[2]


def logarithm(a, inv):
    assert not a[0].r
    w = a[0].c
    z = (w[0]/32-1, w[1]/32)
    assert z[0]**2+z[1]**2 <= Q(16, 25)
    table = {160: model.ZERO}
    for k in reversed(range(160)):
        coef = Q((-1)**(k+1), k) if k else Q(0)
        table[k] = model.rounded(exact(coef).add(exact(*z).mul(table[k+1])))
    raw = exact(5).mul(model.log_constant(2)).add(
        Disk(table[0].c, table[0].r+Q(1, 10**15)))
    constant = model.rounded(raw)
    result = [constant]
    for n in range(len(a)-1):
        result.append(model.rounded(exact(Q(1, n+1)).mul(model.sum_disks(
            exact(i+1).mul(a[i+1].mul(inv[n-i])) for i in range(n+1)))))
    return result, {'input': z, 'table': table, 'raw': raw, 'constant': constant}


def final_source(plan):
    rank, count = plan['rank'], plan['tile_count']
    prefix = f'XiBand{rank}'
    sigma, width, height = ('7/8', '3/8', '19') if rank == 58 else ('29/40', '9/40', '32')
    text = base.HEADER + ''.join(f'import {prefix}.Tile{i:03}\n' for i in range(count))
    text += f'''import {prefix}.Cover
import XiRectangle
import Reinmann.FiniteBandGeometry

/-! A finite-width certificate for actual Xi, assembled with the historical
low rectangle. No external quasi-RH theorem is an input. -/
noncomputable section
namespace Reinmann.{prefix}

theorem all_tiles_nonzero (i : Fin Data.count) {{z : ℂ}}
    (hz : ‖z - Data.centre i‖ ≤ (Data.radius i : ℝ)) : xiCompleted z ≠ 0 := by
  fin_cases i
'''
    text += ''.join(f'  · exact Tile{i:03}.nonzero hz\n' for i in range(count))
    text += f'''
theorem upper_box_nonzero : ∀ z ∈ RationalBallCover.rectangle ({sigma}) 1 (141/10) {height},
    xiCompleted z ≠ 0 := by
  intro z hz
  obtain ⟨i, hi⟩ := Cover.box_covered z hz
  exact all_tiles_nonzero i hi

theorem box_nonzero {{z : ℂ}} (hx0 : ({sigma} : ℝ) ≤ z.re) (hx1 : z.re ≤ 1)
    (hy : |z.im| ≤ ({height} : ℝ)) : xiCompleted z ≠ 0 :=
  FiniteBandGeometry.box_nonzero_of_upper_box (by norm_num)
    (fun z hx0 hx1 hy => XiRectangle.rectangle_nonzero hx0 hx1 hy)
    upper_box_nonzero hx0 hx1 hy

theorem lowHeightWidth : FiniteHeightPFCalibration.LowHeightWidth ({width}) {height} := by
  have h := FiniteBandGeometry.lowHeightWidth_of_box (σ := {sigma}) (H := {height})
    (fun z hx0 hx1 hy => box_nonzero hx0 hx1 hy)
  convert h using 1 <;> norm_num

theorem finitePF{rank} : FinitePF XiMomentCoeff {rank} :=
  FiniteHeightPFCalibration.{'finitePF58_of_two_bands' if rank == 58 else 'finitePF97_of_low_height_width'}
    XiRectangle.zetaNoLowStripZero lowHeightWidth

end Reinmann.{prefix}
'''
    return text


def generate(plan, indices, check=False):
    assert plan['rank'] in (58, 97) and Q(plan['zeta_error']) == Q(1, 5000)
    assert plan['degree'] in (8, 12, 16) and plan['log_scale'] == 32 and plan['log_terms'] == 160
    rank = plan['rank']
    prefix = f'XiBand{rank}'
    output = ROOT / prefix
    if not check:
        output.mkdir(exist_ok=True)
    original_write = Path.write_text

    def write(path, text, *args, **kwargs):
        rel = path.relative_to(ROOT)
        assert rel.parts[0] == 'XiRectangle', rel
        destination = ROOT / prefix / rel.name
        if rel.name == 'Cover.lean':
            box = ' '.join('('+base.q(Q(x))+')' for x in plan['quarter'])
            text = text.replace('∀ z ∈ XiAdaptiveTiles.quarter (141/10)',
                                '∀ z ∈ rectangle '+box)
            text = text.replace('quarter_covered', 'box_covered')
        text = text.replace('XiRectangle', prefix)
        text = text.replace('XiAdaptiveTiles.quarter (141/10)', 'XiAdaptiveTiles.quarter 32')
        if rel.name.startswith('Tile'):
            text = text.replace('import Reinmann.RectangleModel\n',
                                'import Reinmann.FiniteBandModel\nimport Reinmann.FiniteBandTileRules\n')
            for name in ['gamma_sound', 'zeta_sound', 'xi_sound']:
                text = text.replace('('+name+' hc', '(FiniteBandModel.'+name+' hc')
            text = text.replace('Complex.logTaylor 48', 'Complex.logTaylor 160')
            text = text.replace('‖≤(1/2:ℝ)', '‖≤(4/5:ℝ)')
            text = text.replace('(0:ℝ)≤1/2', '(0:ℝ)≤4/5')
            text = text.replace('log_scaled16_contains', 'FiniteBandModel.log_scaled32_contains')
            text = text.replace('RectangleTileRules.certified_tile_nonzero',
                                'FiniteBandTileRules.certified_tile_nonzero')
        if check:
            assert destination.read_text() == text, destination
        else:
            original_write(destination, text, *args, **kwargs)
        return len(text)

    model.ZETA_ERROR = Q(1, 5000)
    model.logarithm = logarithm
    graph = model.build_graph()
    with patch.object(Path, 'write_text', write):
        base.data_file(plan)
        base.cover_file(plan)
        for i in indices:
            print('Generated', prefix, 'tile', i, base.tile_file(graph, plan['tiles'][i]), flush=True)
    final = final_source(plan)
    root = base.HEADER + f'import {prefix}.Final\n'
    if check:
        assert (output / 'Final.lean').read_text() == final
        assert (ROOT / (prefix+'.lean')).read_text() == root
    else:
        original_write(output / 'Final.lean', final)
        original_write(ROOT / (prefix+'.lean'), root)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plan', type=Path, required=True)
    parser.add_argument('--tiles', default='all')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    plan = json.loads(args.plan.read_text())
    indices = range(plan['tile_count']) if args.tiles == 'all' else list(map(int, args.tiles.split(',')))
    generate(plan, indices, args.check)
