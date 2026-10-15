"""Independent normalization, removable-point, witness, and symbol replay checks."""
import ast
from fractions import Fraction
import json
from pathlib import Path
import unittest

from flint import acb, arb, ctx
from certified_weil import correlation_ball, entry
from character_zero_atlas import CharacterControl, OUT, image_segment
from control_window_calibration import matrices, representation_coefficients
from control_zero_attribution import CONTROLS, transform
from davenport_heilbronn_control import log_derivative_coefficients
from dh_weil_certificate import geometric_entry
from epstein_zero_atlas import EpsteinControl
from certified_symbol_comparison import analytic_global, envelope
from compact_window_certificate import symbol
from threshold_ground_gap import box


class CalibrationChecks(unittest.TestCase):
    def test_shifted_fourier_transform_against_direct_integration(self):
        with ctx.workprec(512):
            length, coefficients = arb(5).log(), [arb(1), -arb(2)/3, arb(1)/5]
            for parity in ['even', 'odd']:
                for z in [acb('.23', '2.1'), acb(0), acb(0, 2*arb.pi()/length)]:
                    def integrand(x, _):
                        f = coefficients[0]/length.sqrt() if parity == 'even' else acb(0)
                        for j in range(1 if parity == 'even' else 0, len(coefficients)):
                            n = j if parity == 'even' else j+1
                            phase = 2*arb.pi()*n*x/length
                            value = phase.cos() if parity == 'even' else phase.sin()
                            f += (2/length).sqrt()*(-1)**n*coefficients[j]*value
                        return f*(z*x).exp()
                    direct = acb.integral(integrand, -length/2, length/2,
                                          rel_tol=arb(2)**-280, abs_tol=arb(2)**-280)
                    self.assertTrue(direct.overlaps(transform(z, length, coefficients, parity)))

    def test_correlation_basis_phase(self):
        with ctx.workprec(512):
            length, shift = arb(7).log(), arb('1/5')
            m, n = 2, 1
            def integrand(x, _):
                fm = (acb(0, 2)*arb.pi()*m*(x+shift+length/2)/length).exp()
                fnbar = (-acb(0, 2)*arb.pi()*n*(x+length/2)/length).exp()
                return fm*fnbar/length
            direct = acb.integral(integrand, -length/2, length/2-shift,
                                  rel_tol=arb(2)**-280, abs_tol=arb(2)**-280)
            self.assertTrue((2*direct.real).overlaps(correlation_ball(m, n, acb(shift), length).real))

    def test_epstein_genus_coefficients(self):
        with ctx.workprec(256):
            for d in [5, 6]:
                chars = [chi for _, chi in EpsteinControl(d).characters]
                reps = representation_coefficients(d, 96)
                for n in range(1, 97):
                    divisors = [j for j in range(1, n+1) if n % j == 0]
                    value = (sum((chars[0](j).real for j in divisors), arb(0))
                             +sum(((chars[1](j)*chars[2](n//j)).real for j in divisors), arb(0)))/2
                    self.assertTrue(value.overlaps(reps[n]), (d, n))

    def test_removable_point_images(self):
        with ctx.workprec(384):
            for c in [CharacterControl(17, 3), EpsteinControl(5), EpsteinControl(6)]:
                for left, right in [('999/1000', '1001/1000'), ('-1/1000', '1/1000')]:
                    a, b = acb(left), acb(right)
                    image = image_segment(c, a, b)
                    self.assertTrue(image.is_finite() and not image.contains(0))
                    exact_center = acb(str((Fraction(left)+Fraction(right))/2))
                    for s in [a, exact_center, b]:
                        # Exact-point raw evaluations provide a separate path
                        # at Epstein s=0, where nonzero-radius L balls fail.
                        value = c.raw_jet(s, 0)[0] if isinstance(c, EpsteinControl) else c.value(s)
                        self.assertTrue(value.is_finite())
                        self.assertTrue(image.contains(value))

    def test_closed_entries_against_original_integrals(self):
        with ctx.workprec(768):
            C, length = '13/2', arb('13/2').log()
            for kind, parameter, label in [('character', 17, 3), ('epstein', 5, 0), ('epstein', 6, 0)]:
                _, _, cell = matrices(kind, parameter, label, C, 4, 160)
                top = 7
                if kind == 'character':
                    period = CharacterControl(parameter, label).parameters()[2]
                    a = [arb(0)]+[period[n % parameter] for n in range(1, top+1)]
                else:
                    a = representation_coefficients(parameter, top)
                coef = log_derivative_coefficients(a)
                for m, n in [(0, 0), (2, 0), (2, 2), (2, -2)]:
                    direct = geometric_entry(m, n, length, coef, top)
                    if kind == 'character':
                        direct += (arb(parameter)/5).log()*(m == n)
                    else:
                        direct += entry(m, n, length, [], arb(C))+(arb(4*parameter)/5).log()*(m == n)
                    self.assertTrue(direct.overlaps(cell(m, n)), (kind, parameter, m, n))

    def test_final_negative_witnesses_reassembled(self):
        for name, folder in CONTROLS:
            search = json.loads((OUT/folder/'search_N192_2048bits.json').read_text())
            high = search['negative_certificate_C']
            rec = next(r for r in reversed(search['records']) if r['C'] == high)
            data = json.loads(Path(rec['file']).read_text())
            negative = [s for s in data['sectors'] if 'normalized_full_form' in s]
            self.assertTrue(negative, name)
            modes = max(len(s['exact_trial_coefficients'])-(s['parity'] == 'even') for s in negative)
            with ctx.workprec(data['bits']+128):
                E, O, _ = matrices(data['kind'], data['parameter'], data['Conrey_label'],
                                   data['C'], modes, data['archimedean_tail_terms'])
                for sector in negative:
                    A = E if sector['parity'] == 'even' else O
                    v = [arb(x) for x in sector['exact_trial_coefficients']]
                    value = sum((v[i]*A[i][j]*v[j] for i in range(len(v)) for j in range(len(v))), arb(0))/sum((x*x for x in v), arb(0))
                    self.assertTrue(value < 0 and value.overlaps(box(sector['normalized_full_form'])), name)

    def test_complete_symbol_panel_replay(self):
        data = json.loads((OUT/'symbol_comparison.json').read_text())
        with ctx.workprec(256):
            for record in data['windows']:
                pp, beta = record['active_prime_powers'], arb(record['beta'])
                previous = Fraction(record['certified_tail_start'])
                for panel in record['panels']:
                    lo, hi = Fraction(panel['lo']), Fraction(panel['hi'])
                    self.assertEqual(lo, previous)
                    x = arb(str((lo+hi)/2), str((hi-lo)/2))
                    self.assertTrue(envelope(x, pp) >= beta)
                    previous = hi
                self.assertEqual(previous, record['analytic_takeover'])
                self.assertTrue(analytic_global(arb(record['analytic_takeover']), pp) >= beta)
                self.assertTrue(symbol(arb(record['negative_actual_symbol_point']), pp) < 0)
                self.assertTrue(symbol(arb(record['late_dip_point']), pp) < beta)

    def test_snapshot_mathematical_functions_unchanged(self):
        paths = [Path('experiments/prime_spectral/control_window_calibration.py'),
                 OUT/'source_snapshots/control_window_calibration_initial.py']
        trees = [ast.parse(p.read_text()) for p in paths]
        for name in ['arch_tail', 'arch_cell', 'pole_cell', 'representation_coefficients', 'matrices']:
            definitions = [next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == name) for tree in trees]
            self.assertEqual(ast.dump(definitions[0]), ast.dump(definitions[1]), name)

    def test_attribution_phase_and_dominance(self):
        data = json.loads((OUT/'zero_attribution.json').read_text())
        with ctx.workprec(256):
            for control in data['controls']:
                for witness in control['witnesses']:
                    self.assertTrue(witness['finite_total_negative_certified'])
                    self.assertTrue(witness['dominance_over_other_enclosed_quartets_certified'])
                    self.assertEqual(witness['dominant_negative_quartet_index'], 0)
                    # Omitted terms are numerically material in every case.
                    self.assertTrue(abs(box(witness['finite_total'])) > 100*abs(box(witness['geometric_full_quotient'])))


if __name__ == '__main__':
    unittest.main()
