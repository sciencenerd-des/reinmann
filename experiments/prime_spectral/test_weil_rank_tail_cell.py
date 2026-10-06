"""Uniform infinite tail replay and independent analytic/algebraic checks."""
from fractions import Fraction
import json
from pathlib import Path
import unittest
from flint import acb, arb, arb_mat, ctx
from certified_weil import certified_matrix, entry
from closed_weil import entry_closed
from weil_eigenfamily import ball, box, center_basis
from weil_matrix import prime_powers
from weil_rank_tail_cell import (global_constants, high_mode_lower, power_tail_l2,
                                 run, tail_bound)

RESEARCH = Path(__file__).resolve().parents[2] / 'research/prime_spectral'
TAYLOR = RESEARCH / 'weil_support_taylor_17_19_8_degree64.json'
EVEN = RESEARCH / 'weil_eigenfamily_17_19_8_degree64.json'
SPATIAL = RESEARCH / 'weil_spatial_cell_17_19_8_degree64.json'
TAIL = RESEARCH / 'weil_rank_tail_cell_17_19_8_degree64.json'


class WeilRankTailCellTests(unittest.TestCase):
    def test_saved_infinite_tail_cover_replays(self):
        saved = json.loads(TAIL.read_text())
        self.assertEqual(run(TAYLOR, EVEN, SPATIAL), saved)
        self.assertEqual(len(saved['cells']), 32)
        with ctx.workprec(256):
            bound = ball(saved['uniform_infinite_even_tail_forcing_l2_upper'])
            self.assertLess(bound, arb('9.491e-12'))
            self.assertGreater(ball(saved['uniform_uncoupled_displacement_tail_l2_upper']), arb('1e11') * bound)
            self.assertGreater(ball(saved['full_high_mode_lower_at_certified_start']), 1)
            self.assertGreater(ball(saved['even_high_mode_lower_at_certified_start']), 1)

    def test_digamma_and_trigamma_bounds_from_series(self):
        with ctx.workprec(512):
            for y in (arb('0.01'), arb('0.25'), arb(1), arb(10), arb(1000000)):
                z = acb(arb(1) / 4, y)
                psi = z.digamma()
                self.assertGreater(psi.real, y.log() - 1 / y)
                self.assertGreater(psi.imag, 0)
                self.assertLess(psi.imag, arb.pi() / 2 + arb(2).min(1 / y))
                self.assertLess(abs(z.polygamma(1)).upper(), 1 / (y * y) + arb.pi() / (2 * y))

    def test_uniform_displacement_bounds_at_large_indices_and_both_boundaries(self):
        with ctx.workprec(1024):
            powers = prime_powers(18)
            constants = global_constants(arb(17).log(), arb(19).log(), powers)
            for length in (arb(17).log(), (arb(17).log() + arb(19).log()) / 2, arb(19).log()):
                for index in (1, 8, 65, 1024, 100000000):
                    b = index * entry_closed(index, 0, length, powers, 80)
                    self.assertLess(abs(b).upper(), constants['b'])
                    self.assertLess(abs(b).upper(), constants['b0'] + constants['b1'] / index)
                for index in (16, 128, 100000000):
                    diagonal = entry_closed(index, index, length, powers, 80)
                    self.assertGreater(diagonal, high_mode_lower(constants, index))

    def test_signed_moments_match_original_integral_ground_at_endpoints(self):
        saved = json.loads(TAIL.read_text())
        with ctx.workprec(1024):
            for index, cutoff in ((0, 17), (31, 19)):
                _, even, _ = certified_matrix(cutoff, 8)
                _, basis = center_basis(arb_mat(even))
                unit = [basis[i, 0] for i in range(9)]
                b = [i * even[i][0] / arb(2).sqrt() for i in range(1, 9)]
                cell = saved['cells'][index]
                for r in range(saved['expansion_order']):
                    moment = sum((unit[i] * arb(i)**(2 * r + 2) for i in range(1, 9)), arb(0))
                    arithmetic = sum((unit[i] * b[i - 1] * arb(i)**(2 * r + 1) for i in range(1, 9)), arb(0))
                    self.assertTrue(box(cell['signed_even_moment_intervals'][r]).contains(moment))
                    self.assertTrue(box(cell['signed_arithmetic_moment_intervals'][r]).contains(arithmetic))
                # Direct original integrals for one newly omitted mode.
                j = 9
                length = arb(cutoff).log()
                powers = prime_powers(cutoff)
                direct = arb(2).sqrt() * entry(j, 0, length, powers, cutoff) * unit[0]
                direct += sum(((entry(j, i, length, powers, cutoff) + entry(j, -i, length, powers, cutoff)) * unit[i]
                               for i in range(1, 9)), arb(0))
                bj = j * entry(j, 0, length, powers, cutoff)
                boundary = unit[0] + arb(2).sqrt() * sum(unit[1:], arb(0))
                reconstructed = arb(2).sqrt() * bj * boundary / j
                reconstructed += sum((2 * bj / j * unit[i] * i * i / (j * j - i * i)
                                      - 2 * i * b[i - 1] * unit[i] / (j * j - i * i)
                                      for i in range(1, 9)), arb(0))
                self.assertTrue(direct.overlaps(reconstructed))
                # The original integral eigenvector enclosure has width
                # around 1e-53 after its small-gap solve. Retain that
                # uncertainty in this independent contraction check.
                self.assertLess(abs(direct - reconstructed).upper(), arb('1e-45'))

    def test_exact_rational_geometric_expansion_with_remainder(self):
        # No Weil numerical input: the displacement algebra is exact for
        # every odd b and every even vector, not just ground vectors.
        modes, order = 3, 4
        u = [Fraction(2), Fraction(-3), Fraction(1), Fraction(4)]
        b = [Fraction(0), Fraction(2), Fraction(-5), Fraction(7)]
        boundary = u[0] + 2 * sum(u[1:])  # full even coordinates here
        for j in (4, 17, 1001):
            bj = Fraction(j % 7 - 3)
            direct = bj * u[0] / j
            direct += sum((u[i] * ((bj - b[i]) / (j - i) + (bj + b[i]) / (j + i))
                           for i in range(1, modes + 1)), Fraction(0))
            expansion = bj * boundary / j
            expansion += sum((2 * bj * sum((u[i] * i**(2 * r) for i in range(1, modes + 1)), Fraction(0)) / j**(2 * r + 1)
                              for r in range(1, order + 1)), Fraction(0))
            expansion -= sum((2 * sum((u[i] * b[i] * i**(2 * r + 1) for i in range(1, modes + 1)), Fraction(0)) / j**(2 * r + 2)
                              for r in range(order)), Fraction(0))
            remainder = sum((2 * bj * u[i] * i**(2 * order + 2) / (j**(2 * order + 1) * (j * j - i * i))
                             - 2 * u[i] * b[i] * i**(2 * order + 1) / (j**(2 * order) * (j * j - i * i))
                             for i in range(1, modes + 1)), Fraction(0))
            self.assertEqual(direct, expansion + remainder)

    def test_integral_test_bounds_and_coercivity_monotonicity(self):
        with ctx.workprec(512):
            for cutoff, power in ((8, 1), (64, 2), (64, 5)):
                partial = sum((arb(j)**(-2 * power) for j in range(cutoff + 1, cutoff + 1001)), arb(0))
                bound = power_tail_l2(cutoff, power)
                self.assertLess(partial, bound * bound)
            constants = global_constants(arb(17).log(), arb(19).log(), prime_powers(18))
            values = [high_mode_lower(constants, n) for n in (1, 8, 64, 1000, 100000000)]
            self.assertTrue(all(a < b for a, b in zip(values, values[1:])))
            self.assertGreater(values[-1], 1)

    def test_invalid_tail_parameters_fail_closed(self):
        with ctx.workprec(256):
            with self.assertRaises(ValueError):
                tail_bound(8, 8, 0, arb(1), [], [], arb(1), arb(1), arb(1))
            with self.assertRaises(ValueError):
                tail_bound(8, 64, 1, arb(1), [], [], arb(1), arb(1), arb(1))
            with self.assertRaises(ValueError):
                global_constants(arb(-1), arb(1), [])


if __name__ == '__main__':
    unittest.main()
