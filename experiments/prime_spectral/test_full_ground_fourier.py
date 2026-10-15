"""Full-complement provenance and analytic two-mode transfer regressions."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

from flint import acb, arb, ctx

from full_ground_fourier import OUTPUT, comparison_spectrum, energy_distance, require_replay
from strip_transfer import normalized_profile_upper, strip_functional_norm
from threshold_ground_gap import box


class FullGroundFourierTests(unittest.TestCase):
    def test_exact_unit_trial_saturates_sharp_phase_distance(self):
        # diag(1,3) on the exactly unit vector (12/13,5/13).
        with ctx.workprec(256):
            x, y = arb(12)/13, arb(5)/13
            self.assertTrue((x*x+y*y).contains(1))
            mu = x*x+3*y*y
            mass, distance = energy_distance(mu, 1, 3)
            actual_distance = ((1-x)**2+y*y).sqrt()
            # The API deliberately uses the outward upper Rayleigh endpoint;
            # its result bounds the exact answer rather than enclosing it.
            self.assertTrue(mass.upper() >= (y*y).lower())
            self.assertTrue(abs(mass-y*y) < arb(2)**-200)
            self.assertTrue(distance.upper() >= actual_distance.lower())
            self.assertTrue(abs(distance-actual_distance) < arb(2)**-200)
            _, loose = energy_distance(mu, -2, 3)
            self.assertTrue(loose > distance)
            _, exact = energy_distance(1, 1, 3)
            self.assertTrue(exact.is_zero())

    def test_lower_bound_monotonicity_and_negative_ground_allowed(self):
        with ctx.workprec(256):
            _, old = energy_distance('1.1', 0, 3)
            _, new = energy_distance('1.1', 1, 3)
            self.assertTrue(new < old)
            t, d = energy_distance('-0.9', -1, 2)
            self.assertTrue(0 < t < 1)
            self.assertTrue(0 < d < 1)

    def test_full_strip_functional_and_normalized_profile(self):
        with ctx.workprec(256):
            length, height = arb(2), arb(2)/5
            x, y = arb(12)/13, arb(5)/13
            _, d = energy_distance(x*x+3*y*y, 1, 3)
            W = strip_functional_norm(length, height)
            integral = acb.integral(lambda t, analytic: (2*height*t).exp(), -1, 1)
            self.assertTrue((length*W*W).overlaps(integral.real))
            bound = arb(normalized_profile_upper(length, height, x, d))
            for z in [acb(0), acb(1), acb(2*arb.pi()), acb(1,height), acb(-2,-height)]:
                a = z*length/2
                constant = a.sinc()
                cosine = ((a-arb.pi()).sinc()+(a+arb.pi()).sinc())/arb(2).sqrt()
                trial = x*constant+y*cosine
                self.assertTrue(abs(constant-trial/x) < bound)
                self.assertTrue(abs(length.sqrt()*(constant-trial)) < length.sqrt()*W*d)

    def test_invalid_energy_inputs_rejected(self):
        for values in [(3,1,3), (0,1,3), (1,1,1), ('nan',0,1)]:
            with self.assertRaises((ValueError, ArithmeticError)):
                energy_distance(*values)
        with self.assertRaises(ValueError):
            strip_functional_norm(2,-1)

    def test_both_full_comparison_sectors_replay(self):
        with ctx.workprec(512):
            for prime, name, floor, shift in [
                (2,'two','11/10000','57/1000'),
                (3,'three','1/100000000','103/25000000')]:
                data = comparison_spectrum(OUTPUT/f'near_{name}_lower_operator.json', prime, floor, shift)
                self.assertTrue(data['second_lower'] > data['ground_lower'])
                self.assertEqual(sum(x['second_shift_negative_count'] for x in data['sectors']),1)

    def test_complement_and_provenance_tampering_rejected(self):
        raw = json.loads((OUTPUT/'near_two_lower_operator.json').read_text())
        variants = []
        data = copy.deepcopy(raw)
        data['infinite_coupling_bound'] = {'lo':'0','hi':'0'}
        variants.append(data)
        data = copy.deepcopy(raw)
        data['sectors'] = data['sectors'][:1]
        variants.append(data)
        data = copy.deepcopy(raw)
        data['source_hashes'] = {}
        variants.append(data)
        data = copy.deepcopy(raw)
        data['active_prime_powers'] = []
        variants.append(data)
        with ctx.workprec(512), tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'changed.json'
            for data in variants:
                path.write_text(json.dumps(data))
                with self.assertRaises((ValueError, ArithmeticError)):
                    comparison_spectrum(path,2,'11/10000','57/1000')

    def test_saved_genuine_ground_bounds_and_origin_protection(self):
        data = json.loads((OUTPUT/'full_ground_fourier.json').read_text())
        with ctx.workprec(512):
            for row, limit in zip(data['results'], ['0.056','0.125'], strict=True):
                self.assertTrue(box(row['full_gap_lower']) > 0)
                self.assertTrue(box(row['ground_mean_lower']) > 0)
                self.assertTrue(box(row['oriented_unit_ground_distance_upper']) < arb(limit))
                self.assertEqual([s['height'] for s in row['strips']], ['0','2/5','49/100'])

    def test_wider_frequency_band_improves_full_state_error(self):
        old = json.loads((OUTPUT/'full_ground_fourier_band64.json').read_text())
        new = json.loads((OUTPUT/'full_ground_fourier_band128.json').read_text())
        with ctx.workprec(512):
            for before, after in zip(old['results'], new['results'], strict=True):
                self.assertTrue(box(after['full_ground_lower']) > box(before['full_ground_lower']))
                self.assertTrue(box(after['oriented_unit_ground_distance_upper'])
                                < box(before['oriented_unit_ground_distance_upper']))
                for a, b in zip(before['strips'], after['strips'], strict=True):
                    self.assertTrue(box(b['origin_normalized_profile_error_upper'])
                                    < box(a['origin_normalized_profile_error_upper']))

    def test_missing_independent_integral_replay_rejected(self):
        data = json.loads((OUTPUT/'baseline_replay.json').read_text())
        data['independent_adaptive_integral_entries'] = []
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'replay.json'
            path.write_text(json.dumps(data))
            with self.assertRaises(ValueError):
                require_replay(path, 'research/prime_spectral/window_positivity_exp_1p2.json')


if __name__ == '__main__':
    unittest.main()
