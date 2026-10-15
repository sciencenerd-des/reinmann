"""Plot the isolated factor and the certified finite DH grid, without PF extrapolation."""
import json
import math
from fractions import Fraction
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


def main():
    out = Path('research/prime_spectral/verification_2026_10_12_sector')
    atlas = json.loads((out/'atlas_H340.json').read_text())
    scan = json.loads((out/'dh_rank430-520_shift0-200_32768bits.json').read_text())
    angle = atlas['steepest_candidate']['folded_deviation_angle']
    phi = float((Fraction(angle['lo'])+Fraction(angle['hi']))/2)
    rows = scan['per_rank']
    if len(rows) != 91 or any(r['positive'] != 201 or r['negative'] or r['unresolved'] for r in rows):
        raise ValueError('The requested grid is not certified fully positive')
    ranks = [r['rank'] for r in rows]
    fig, axes = plt.subplots(2, 1, figsize=(8.5, 5.4), sharex=True,
                             gridspec_kw={'height_ratios': [2, 1]}, layout='constrained')
    ax = axes[0]
    ax.plot(ranks, [math.sin((r+1)*phi) for r in ranks], color='#ae3036', lw=2)
    ax.axhline(0, color='black', lw=.7)
    ax.axvline(436, color='#555555', ls=':', lw=1)
    ax.set_ylabel(r'$U_r(\cos\phi)\,\sin\phi$')
    ax.set_title('Isolated quadratic factor: first negative determinant at rank 436', fontsize=11)
    ax.grid(alpha=.15)
    ax = axes[1]
    ax.plot(ranks, [r['positive'] for r in rows], color='#176c55', lw=3)
    ax.set_ylim(0, 225)
    ax.set_yticks([0, 201])
    ax.set_ylabel('Positive minors')
    ax.set_xlabel('Rank r')
    ax.set_title('Full DH function: all 201 tested shifts pass at every rank', fontsize=11)
    ax.grid(alpha=.15)
    fig.suptitle('A sufficient sector bound does not predict failure in this DH grid', fontsize=13)
    fig.text(.5, -.015, '32,768-bit Arb enclosures; shifts 0–200 only. Arbitrary minors remain untested.',
             ha='center', fontsize=9)
    for suffix in ['pdf', 'png']:
        fig.savefig(out/f'dh_sector_grid.{suffix}', dpi=180, bbox_inches='tight')
    plt.close(fig)


if __name__ == '__main__':
    main()
