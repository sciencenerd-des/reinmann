"""Exact rational audit of the manuscript's displayed certified Table 2.

This checks presentation against the saved certificate; it does not verify
the Arb inclusion property or the underlying analytic theorem.
"""
from fractions import Fraction
import hashlib
import json
from pathlib import Path


def audit():
    root = Path(__file__).resolve().parents[1]
    source = root / 'paper/weil_infinite_rank_tail_paper.tex'
    certificate = root / 'research/prime_spectral/weil_rank_tail_cell_17_19_8_degree64.json'
    text = source.read_text()
    data = json.loads(certificate.read_text())
    cell = data['cells'][0]
    F = Fraction
    intervals = [
        ('S', cell['signed_boundary_interval'], '6.3167e-12', '6.5920e-12'),
        ('m1', cell['signed_even_moment_intervals'][0], '-6.317e-8', '-5.976e-8'),
        ('m2', cell['signed_even_moment_intervals'][1], '1.1354e-4', '1.1920e-4'),
        ('m3', cell['signed_even_moment_intervals'][2], '-7.691e-2', '-7.419e-2'),
        ('nu0', cell['signed_arithmetic_moment_intervals'][0], '-5.406e-10', '-4.750e-10'),
        ('nu1', cell['signed_arithmetic_moment_intervals'][1], '1.5495e-6', '1.7150e-6'),
        ('nu2', cell['signed_arithmetic_moment_intervals'][2], '-1.5124e-3', '-1.3961e-3'),
    ]
    # Guard the transcription against later manuscript changes.
    for literal in ('[-6.317,-5.976]', '[-7.691,-7.419]', '[-5.406,-4.750]',
                    '[-1.5124,-1.3961]', '9.4900\\times10^{-12}',
                    '(9.49005\\times10^{-12})^2<9.0061\\times10^{-23}'):
        if literal not in text:
            raise ValueError('manuscript changed; re-audit the transcription: ' + literal)
    rows = []
    for name, box, lo, hi in intervals:
        rows.append({'name': name, 'printed_lower': lo, 'printed_upper': hi,
                     'lower_is_outward': F(lo) <= F(box['lo']),
                     'upper_is_outward': F(hi) >= F(box['hi']),
                     'certificate_lower_approx': float(F(box['lo'])),
                     'certificate_upper_approx': float(F(box['hi']))})
    terms = [F(x) for x in cell['individual_power_tail_l2_upper']]
    entries = [('boundary', terms[0], '2.465e-12'), ('m1', terms[1], '3.648e-12'),
               ('m2', terms[2], '1.252e-12'), ('m3', terms[3], '1.642e-13'),
               ('m4_to_m8', sum(terms[4:9]), '9.5e-15'),
               ('nu0', terms[9], '1.219e-12'), ('nu1', terms[10], '6.182e-13'),
               ('nu2', terms[11], '1.062e-13'),
               ('nu3_to_nu7', sum(terms[12:17]), '7.9e-15'),
               ('remainder', F(cell['geometric_expansion_remainder_l2_upper']), '1.001e-22'),
               ('total', F(cell['infinite_even_tail_forcing_l2_upper']), '9.4900e-12')]
    return {'status': 'manuscript_rounding_requires_revision',
            'scope': 'exact comparison with saved certificate, not a Lean or Arb replay',
            'sha256': {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                       for p in (source, certificate)},
            'interval_rows': rows,
            'upper_bound_rows': [{'name': n, 'printed_upper': v, 'is_outward': F(v) >= x,
                                  'certificate_upper_approx': float(x)} for n, x, v in entries],
            'coarse_squared_inequality_is_true': F('9.49005e-12') ** 2 < F('9.0061e-23'),
            'corrected_squared_inequality_is_true': F('9.4900466e-12') ** 2 < F('9.0061e-23')}


if __name__ == '__main__':
    print(json.dumps(audit(), indent=2))
