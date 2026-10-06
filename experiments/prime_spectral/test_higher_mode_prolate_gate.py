"""Replay the exact prolate exclusion against higher-mode Weil matrices."""
import json
from fractions import Fraction
from pathlib import Path
import unittest

from higher_mode_prolate_gate import certify, run


ROOT = Path(__file__).resolve().parents[2]


class HigherModeProlateGateTests(unittest.TestCase):
    def test_saved_mode_12_and_16_gates_replay(self):
        for modes in (12, 16):
            with self.subTest(modes=modes):
                result = run(
                    ROOT / f'research/prime_spectral/isolated_kernel_13_{modes}.json',
                    ROOT / 'research/prime_spectral/prolate_jacobi_13_80.json',
                    ROOT / 'research/prime_spectral/prolate_vectors_13_80.json')
                saved = json.loads((ROOT / f'research/prime_spectral/exact_prolate_gate_13_{modes}.json').read_text())
                self.assertEqual(result, saved)
                self.assertGreater(Fraction(result['exact_rayleigh_excess_over_second_even_lower']), 0)

    def test_tampered_spectrum_fails_closed(self):
        isolated = json.loads((ROOT / 'research/prime_spectral/isolated_kernel_13_12.json').read_text())
        jacobi = json.loads((ROOT / 'research/prime_spectral/prolate_jacobi_13_80.json').read_text())
        vectors = json.loads((ROOT / 'research/prime_spectral/prolate_vectors_13_80.json').read_text())
        isolated['even_spectrum'][1]['lo'] = '0'
        with self.assertRaises(ValueError):
            certify(isolated, jacobi, vectors)


if __name__ == '__main__':
    unittest.main()
