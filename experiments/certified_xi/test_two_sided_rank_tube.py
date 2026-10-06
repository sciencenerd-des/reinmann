from fractions import Fraction
import unittest

from two_sided_rank_tube import Envelope, correction_polynomial, head_conditions, local_tube, repeated_root_identity, run


class TwoSidedRankTubeTests(unittest.TestCase):
    def test_symbolic_control_and_all_interior_cells(self):
        self.assertTrue(all(repeated_root_identity().values()))
        for N in (4, 6, 10):
            result = run(N, 4)
            for row in result['rows']:
                self.assertEqual(row['status'], 'conditional_two_sided_tube_pass')
                self.assertTrue(all(row['head_conditions'].values()))
                self.assertEqual(row['lower_correction_shifted_coefficients'], [])
                self.assertEqual(row['upper_correction_shifted_coefficients'], [])

    def test_weakening_neighbor_lower_bound_breaks_certificate(self):
        upper = [Envelope(4, 4), Envelope(3, 3), Envelope(2, 2)]
        lower = [Envelope(Fraction(39, 10), 4), upper[1], upper[2]]
        result = local_tube(4, 3, lower, upper)
        self.assertEqual(result['status'], 'unresolved')
        self.assertFalse(result['conditions']['lower_correction_polynomial'])
        self.assertLess(correction_polynomial(3, upper[1], lower[0], lower[2])(4), 0)

    def test_polynomial_matches_exact_correction_inequality(self):
        center, left, right = Envelope(Fraction(5, 2), 3), Envelope(3, 4), Envelope(Fraction(3, 2), 2)
        poly = correction_polynomial(3, center, left, right)
        for r in (4, 10, 100):
            Bc = 1+Fraction(3, r)*(1-center.value(r))
            Bl = 1+Fraction(2, r)*(1-left.value(r))
            Br = 1+Fraction(4, r)*(1-right.value(r))
            q = r+center.offset
            difference = Bc*Bc/(Bl*Br)-(q*q-1)/(q*q)
            denominator = q*q*((r+2)*(r+left.offset)-2*left.amplitude)*((r+4)*(r+right.offset)-4*right.amplitude)
            self.assertEqual(Fraction(str(poly(r))), difference*denominator)

    def test_head_directions_and_domain_rejection(self):
        env = Envelope(3, 3)
        p, q = env.value(3), env.value(4)
        self.assertTrue(all(head_conditions(4, env, env, p, p, q, q).values()))
        self.assertFalse(head_conditions(4, env, env, p, p, q+Fraction(1, 100), q+Fraction(1, 100))['lower_curvature'])
        with self.assertRaises(ValueError):
            Envelope(0, 1)
        with self.assertRaises(ValueError):
            local_tube(1, 2, [Envelope(1, 0)]*3, [Envelope(1, 0)]*3)
        with self.assertRaises(ValueError):
            local_tube(4, 3, [env]*2, [env]*3)


if __name__ == '__main__':
    unittest.main()
