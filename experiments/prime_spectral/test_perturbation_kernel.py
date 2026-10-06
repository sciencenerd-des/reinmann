import json
from pathlib import Path
import unittest
from flint import arb,ctx
from certified_mode_comparison import box
from perturbation_kernel import bernstein_from_raw,run,transfer_spectrum


class PerturbationKernelTests(unittest.TestCase):
    def setUp(self):
        ctx.prec=512

    def test_interval_transfer_encloses_known_diagonal_case(self):
        first=arb('1').union(arb('1.000001'))
        second=arb('3').union(arb('3.000001'))
        record=transfer_spectrum([[first,arb(0)],[arb(0),second]])
        self.assertTrue(record['first'].contains(arb('1.0000005')))
        self.assertGreater(record['second_lower']-record['first'],1)
        self.assertTrue(record['vector'][0].contains(1))
        self.assertTrue(record['vector'][1].contains(0))

    def test_cutoff_31_certifies_finite_kernel(self):
        record=run(31,16)
        self.assertEqual(record['status'],'certified_finite_perturbation_prime_kernel_not_uniform')
        self.assertGreater(box(record['lowest_even_gap']),0)
        self.assertLess(box(record['variance']),arb('0.065'))
        self.assertTrue(all(box(x)>0 for x in record['bernstein_coefficients']))

    def test_previous_cutoff_agrees_with_isolation(self):
        record=run(13,4)
        path=Path(__file__).resolve().parents[2]/'research/prime_spectral/positive_kernel_13_4.json'
        other=json.loads(path.read_text())
        self.assertGreater(box(record['even_first']),0)
        self.assertTrue(box(record['variance']).overlaps(box(other['variance'])))
        self.assertLess(box(record['variance']),arb('0.1'))

    def test_rejects_unresolved_perturbation_and_kernel(self):
        wide=arb(1).union(arb(4))
        with self.assertRaises(ArithmeticError):
            transfer_spectrum([[wide,arb(0)],[arb(0),wide]])
        with self.assertRaises(ArithmeticError):
            bernstein_from_raw([arb(1)/5,arb(2)/5*arb(2).sqrt()])


if __name__=='__main__':
    unittest.main()
