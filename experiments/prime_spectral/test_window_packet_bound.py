import unittest
from flint import acb, arb, ctx

from window_packet_bound import packet_bound, spline_transform, zeta_zero_tail


class WindowPacketTests(unittest.TestCase):
    def test_transform_box_convolution_and_removable_center(self):
        with ctx.workprec(256):
            self.assertTrue(spline_transform(0, 2, 4).contains(1))
            z = acb('1/3', '7/5')
            expected = ((z/2).sinh()/(z/2))**4
            self.assertTrue(spline_transform(z, 2, 4).overlaps(expected))

    def test_packet_bound_with_exact_exponential_samples(self):
        # An independent synthetic exponential sum, not actual zeta zeros.
        with ctx.workprec(256):
            nodes = [acb('1/4'), acb('-1/4')]
            weights = [acb(1), acb(2)]
            h, initial = arb('1/2'), 3
            samples = [sum((w*(z*h*j).exp() for w, z in zip(weights, nodes)),
                           acb(0)) for j in range(initial, initial+2)]
            Q = max(arb(abs(s).upper()) for s in samples)
            bounds = packet_bound(nodes, weights, h, initial, Q, 0)
            for z, b in zip(nodes, bounds):
                self.assertTrue(z.real <= b)

    def test_all_height_tail_dominates_known_integer_sequence(self):
        # Synthetic zeros gamma=+-n have 2floor(u)<=10u log(10u).
        with ctx.workprec(256):
            a, q, T, t = arb(2), 4, 10, arb(3)
            known = sum((2*abs(spline_transform(acb('1/2', n), a, q))**2
                         *(t/2).exp() for n in range(T+1, 200)), arb(0))
            self.assertTrue(known < zeta_zero_tail(a, q, T, t))

    def test_alias_and_zero_weights_fail_closed(self):
        with self.assertRaises(ArithmeticError):
            packet_bound([0, 0], [1, 1], 1, 1, 1, 0)
        with self.assertRaises(ArithmeticError):
            packet_bound([0], [0], 1, 1, 1, 0)

    def test_domain_rejections(self):
        with self.assertRaises(ValueError):
            zeta_zero_tail(1, 2, 2, 1)
        with self.assertRaises(ValueError):
            packet_bound([0], [1], 1, 0, 1, 0)


if __name__ == '__main__':
    unittest.main()
