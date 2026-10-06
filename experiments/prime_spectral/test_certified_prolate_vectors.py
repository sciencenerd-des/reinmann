"""Replay the prolate eigenvector certificate without trusting mpmath."""
import json
from fractions import Fraction
from pathlib import Path
import unittest

from certified_prolate_vectors import certify_trials


ROOT = Path(__file__).resolve().parents[2]


class CertifiedProlateVectorTests(unittest.TestCase):
    def test_saved_trial_vectors_replay_in_arb(self):
        jacobi = json.loads((ROOT / 'research/prime_spectral/prolate_jacobi_13_80.json').read_text())
        saved = json.loads((ROOT / 'research/prime_spectral/prolate_vectors_13_80.json').read_text())
        trials = {key: {'trial_eigenvalue': mode['trial_eigenvalue'],
                        'trial_vector': mode['trial_vector']}
                  for key, mode in saved['modes'].items()}
        replay = certify_trials(jacobi, trials)
        self.assertEqual(replay['modes'], saved['modes'])
        for mode in replay['modes'].values():
            self.assertLess(Fraction(mode['oriented_unit_eigenvector_l2_error_upper']),
                            Fraction('1e-20'))

    def test_dimension_mismatch_fails_closed(self):
        jacobi = json.loads((ROOT / 'research/prime_spectral/prolate_jacobi_13_80.json').read_text())
        saved = json.loads((ROOT / 'research/prime_spectral/prolate_vectors_13_80.json').read_text())
        trials = {key: {'trial_eigenvalue': mode['trial_eigenvalue'],
                        'trial_vector': mode['trial_vector'][:]} for key, mode in saved['modes'].items()}
        trials['0']['trial_vector'].pop()
        with self.assertRaises(ValueError):
            certify_trials(jacobi, trials)


if __name__ == '__main__':
    unittest.main()
