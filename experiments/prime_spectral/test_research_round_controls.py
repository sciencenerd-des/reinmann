"""Independent arithmetic/gamma checks and saved negative-trial replay."""
from fractions import Fraction
import json
import unittest
from flint import acb, arb, ctx
from dh_analogue_controls import datum
from dh_zero_atlas import OUT
from epstein_control import CHARS, coefficients, jet
from localized_packet_bound import local_count_upper, localized_tail, turan_bound
from threshold_ground_gap import box


class RoundControls(unittest.TestCase):
    def test_epstein_representation_coefficients_against_L_products(self):
        with ctx.workprec(320):
            a = coefficients(64)
            for n in range(1, 65):
                first = sum((CHARS[0](d).real for d in range(1, n+1) if n % d == 0), arb(0))
                second = sum((CHARS[1](d).real*CHARS[2](n//d).real
                              for d in range(1, n+1) if n % d == 0), arb(0))
                self.assertTrue(((first+second)/2-a[n]).contains(0))

    def test_epstein_gamma_duplication_normalization(self):
        with ctx.workprec(320):
            for t in ['0', '7', '85.7']:
                zeta = acb('1/4', arb(t)/2).digamma().real-arb.pi().log()
                difference = acb('3/4', arb(t)/2).digamma().real-acb('1/4', arb(t)/2).digamma().real
                epstein = 2*acb('1/2', t).digamma().real+arb(5).log()-2*arb.pi().log()
                self.assertTrue((epstein-(2*zeta+difference+arb(20).log())).contains(0))

    def test_analogue_root_number_and_period(self):
        with ctx.workprec(320):
            for q in [13, 17]:
                _, epsilon, k, a = datum(q)
                self.assertTrue((abs(epsilon)**2-1).contains(0))
                self.assertTrue((epsilon-(acb(1, k)/acb(1, -k))).contains(0))
                for j in range(1, q):
                    self.assertTrue((a[q-j]+a[j]).contains(0))

    def test_saved_negative_witnesses(self):
        names = ['dh_original_C7873_256_N80.json', 'dh_absolute_C31_N60.json',
                 'dh_prime-powers_C31_N60.json', 'analogue_q13_C271_8.json',
                 'epstein5_C159_8.json']
        with ctx.workprec(1024):
            for name in names:
                d = json.loads((OUT/name).read_text())
                negatives = [s for s in d['sectors'] if 'normalized_full_form' in s]
                self.assertTrue(negatives, name)
                for s in negatives:
                    A = [[box(x) for x in row] for row in s['matrix']]
                    v = list(map(arb, s['exact_trial_coefficients']))
                    norm = sum((x*x for x in v), arb(0))
                    value = sum((v[i]*A[i][j]*v[j] for i in range(len(v))
                                 for j in range(len(v))), arb(0))/norm
                    self.assertLess(value, 0, name)
                    self.assertTrue(value.overlaps(box(s['normalized_full_form'])))

    def test_localized_tail_matches_direct_stieltjes_integration(self):
        with ctx.workprec(320):
            a, q, gamma, R, t = arb('1/2'), 3, arb(100), arb(2), arb(3)
            B = 10*(1+(gamma+2)/R)
            # Independent numerical integral of the envelope after u=R/v.
            value = acb.integral(lambda v, _: (v**(2*q-2))*(acb(B*R)/v).log(),
                                  arb('1e-12'), 1, abs_tol=arb('1e-60'), rel_tol=arb('1e-60'))
            closed = ((B*R).log()/(2*q-1)+1/arb(2*q-1)**2)
            self.assertLess(abs(value.real-closed), arb('1e-45'))
            expected = (q/a)**(2*q)*(a+t/2).exp()*100*(2*q)*R**(1-2*q)*closed
            self.assertTrue((localized_tail(a, q, gamma, R, t)-expected).contains(0))
            self.assertGreater(local_count_upper(gamma, 1), 0)

    def test_turan_hypotheses_fail_closed(self):
        with ctx.workprec(256):
            self.assertTrue(turan_bound(3, 3, 1, 2, 1, 1, 8, 1).is_finite())
            for A, span in [(0, 8), (-1, 8), (1, 7)]:
                with self.assertRaises(ValueError):
                    turan_bound(3, 3, 1, 2, 1, A, span, 1)


if __name__ == '__main__':
    unittest.main()
