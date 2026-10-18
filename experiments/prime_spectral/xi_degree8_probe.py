"""Degree-eight, low-precision hard-tile calibration; external Arb evidence only."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import statistics
import time

from flint import acb, acb_series, arb, ctx
import xi_evaluator_comparison as previous


def run(output):
    rows = []
    for bits in (64, 80, 96):
        ctx.prec, ctx.cap = bits, 9
        truth = previous.reference()
        timings = []
        for _ in range(7):
            start = time.monotonic()
            s = acb_series([previous.CENTRE, 1])
            zet = previous.zeta_em(s, 20, 6)
            gam = previous.gamma_stirling(s, 12, 7)
            zet = acb_series([previous.ball(zet[j], arb('1e-7')) for j in range(9)])
            gam = acb_series([previous.ball(gam[j], arb('4e-14')) for j in range(9)])
            jet = previous.prefactor(s) * gam * zet
            timings.append(time.monotonic() - start)
        # Round to modest dyadic centres and use one rational disk radius per coefficient.
        centres, rounded = [], []
        for j in range(9):
            pair = [Fraction(round(float(x.mid()) * 2**28), 2**28)
                    for x in (jet[j].real, jet[j].imag)]
            centre = acb(*(arb(str(x)) for x in pair))
            assert abs(jet[j]-centre) < arb('1e-7')
            centres.append([str(x) for x in pair])
            rounded.append(centre)
        r = arb('1/16')
        # A disk of radius e is enclosed by the component-wise square used below.
        bounded = acb_series([previous.ball(x, arb('1e-7')) for x in rounded])
        K = sum((j*abs(bounded[j])*r**(j-1) for j in range(1,9)), arb(0))
        K += 1000*r**8*(9-8*r)/(1-r)**2
        # Explicit centre-enclosure error, rather than abs(bounded[0]).lower().
        margin = abs(rounded[0]).lower()-arb('1e-7')-K.upper()*r
        radii = [(jet[j].real.rad()**2+jet[j].imag.rad()**2).sqrt().upper()
                 for j in range(9)]
        assert all(jet[j].overlaps(truth[j]) for j in range(9)) and margin > 0
        rows.append({'precision_bits': bits, 'median_seconds': statistics.median(timings),
                     'all_nine_overlap_independent_reference': True,
                     'maximum_complex_radius_before_rounding': str(max(radii)),
                     'dyadic_centres': centres, 'each_disk_error_after_rounding': '1e-7',
                     'derivative_upper': str(K.upper()), 'tile_margin_lower': str(margin.lower())})
    root = Path(__file__).resolve().parents[2]
    sources = [Path(__file__).resolve(), Path(previous.__file__).resolve()]
    result = {'status': 'external_Arb_calibration_only', 'centre': ['1/2','14'],
              'degree': 8, 'tile_radius': '1/16', 'unit_circle_majorant': 1000,
              'zeta_coefficient_error': '1e-7', 'Gamma_coefficient_error': '4e-14',
              'Lean_complete_tile_certified': False, 'rows': rows,
              'source_sha256': {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in sources}}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2)+'\n')
    for row in rows:
        print(row['precision_bits'], row['median_seconds'], row['tile_margin_lower'])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    run(parser.parse_args().output)
