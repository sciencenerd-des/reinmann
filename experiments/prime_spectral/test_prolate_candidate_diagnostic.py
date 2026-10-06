"""The exact rounded-vector gate must not mistake a high mode for the ground state."""
import unittest

from prolate_candidate_diagnostic import certified_rayleigh


class ProlateCandidateGateTests(unittest.TestCase):
    def test_exact_rayleigh_classifies_both_sides_of_second_eigenvalue(self):
        def box(value):
            return {'lo': str(value), 'hi': str(value)}

        matrix = [[box(4 if i == 0 else 2 if i == 1 else 1
                       if i == 2 else 2 if i == 3 else 4)
                   if i == j else box(0) for j in range(5)]
                  for i in range(5)]
        certificate = {'status': 'certified_finite_weil_gates', 'modes': 2,
                       'matrix': matrix, 'second_even_eigenvalue': box(2)}
        low = certified_rayleigh(certificate, ['1', '0', '0'])
        high = certified_rayleigh(certificate, ['0', '0', '1'])
        self.assertTrue(low['rayleigh_below_second'])
        self.assertFalse(low['rayleigh_above_second'])
        self.assertTrue(high['rayleigh_above_second'])
        self.assertFalse(high['rayleigh_below_second'])
        self.assertEqual(high['lower_excess_ratio'], '2')
        mixed = certified_rayleigh(certificate, ['1', '1', '0'])
        self.assertEqual(mixed['rayleigh_interval'], {'lo': '3/2', 'hi': '3/2'})
        self.assertEqual(mixed['residual_norm_squared_interval'],
                         {'lo': '1/4', 'hi': '1/4'})
        self.assertEqual(mixed['residual_over_clearance_squared_upper'], '1')
        self.assertIsNone(high['residual_over_clearance_squared_upper'])

    def test_malformed_inputs_fail_closed(self):
        certificate = {'status': 'certified_finite_weil_gates', 'modes': 1,
                       'matrix': [[{'lo': '0', 'hi': '0'}] * 3] * 3,
                       'second_even_eigenvalue': {'lo': '1', 'hi': '1'}}
        with self.assertRaises(ValueError):
            certified_rayleigh(certificate, ['0', '0'])
        with self.assertRaises(ValueError):
            certified_rayleigh(certificate, ['1'])
        certificate['matrix'][0][0] = {'lo': '1', 'hi': '0'}
        with self.assertRaises(ValueError):
            certified_rayleigh(certificate, ['1', '0'])


if __name__ == '__main__':
    unittest.main()
