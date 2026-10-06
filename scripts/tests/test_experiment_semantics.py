"""Small adversarial checks; these do not validate Xi coefficients."""
import sys
from pathlib import Path
import unittest
import mpmath as mp
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from uniformity_gap_experiment import classical_jensen_coefficients, numerical_root_status, compute_jensen_discriminant
from jensen_discriminant_analysis import compute_discriminant_d2
from hef_theory_experiment import compute_deformed_coefficients, compute_entropy_d2
from de_bruijn_newman_simulation import simulate_flow
from simulate_rmt_crossings import run_simulation

class ExperimentSemanticsTests(unittest.TestCase):
    def test_quartic_discriminant_does_not_imply_real_roots(self):
        p = [1, 0, 0, 0, 1]
        self.assertAlmostEqual(float(compute_jensen_discriminant(p)), 256)
        self.assertEqual(numerical_root_status(p)['status'], 'numerically nonreal')

    def test_jensen_factorial_changes_quadratic(self):
        self.assertEqual(classical_jensen_coefficients([1, 2, 2], 0, 2), [1, 4, 4])
        self.assertEqual(compute_discriminant_d2([1, 2, 2], 0), 0)
        self.assertEqual(numerical_root_status([])['status'], 'inconclusive')
        self.assertEqual(numerical_root_status([0])['status'], 'degenerate')

    def test_backward_heat_sign_and_factorials(self):
        b = [mp.mpf(1), mp.mpf(2), mp.mpf(3)]
        self.assertEqual(compute_deformed_coefficients(b, mp.mpf('0.5'), 2), [8])
        for m in (0, 1):
            derivative = mp.diff(lambda t: compute_deformed_coefficients(b, t, 1)[m], 0)
            self.assertEqual(derivative, -(2*m+2)*(2*m+1)*b[m+1])
        with self.assertRaises(ValueError):
            compute_entropy_d2([1, 2])

    def test_mirror_perturbation(self):
        h = simulate_flow([mp.mpc('.5', 14)], mp.mpf('0.000001'), 2, perturbed=True)
        for row in h:
            self.assertAlmostEqual(sum(z[0] for z in row['zeros']), 1)

    def test_seed_replays(self):
        self.assertEqual(run_simulation(2, 100, 42), run_simulation(2, 100, 42))
        with self.assertRaises(ValueError):
            run_simulation(0)

if __name__ == '__main__':
    unittest.main()
