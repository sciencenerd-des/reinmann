"""Independent DH off-line zero and finite ground-state gate certificates."""
import json
from pathlib import Path

from flint import acb, acb_series, arb, ctx

from certified_weil import eigen_interval, endpoints, inertia
from davenport_heilbronn_control import kappa
from dh_weil_certificate import assemble
from full_ground_fourier import sha256
from threshold_ground_gap import box

OUT = Path('research/prime_spectral/verification_2026_10_12_remaining')


def H_jet(s):
    old = ctx.cap
    try:
        ctx.cap = 2
        z = acb_series([s, 1])
        k = kappa()
        return sum((a*z.zeta(arb(r)/5) for r, a in
                    [(1, 1), (2, k), (3, -k), (4, -1)]),
                   acb_series([0]))*(-z*arb(5).log()).exp()
    finally:
        ctx.cap = old


def zero_certificate():
    with ctx.workprec(768):
        x = arb('0.80851718245663738555335196060684412785067026830502')
        y = arb('85.699348485377592171929267708941729037987829423408')
        r = arb('1e-30')
        center = acb(x, y)
        # This rectangle contains the complex disk of radius r.
        rectangle = acb(arb(x.mid(), r), arb(y.mid(), r))
        center = acb(x.mid(), y.mid())  # exact dyadic center
        c = H_jet(center)
        derivative = acb(c[1].real.mid(), c[1].imag.mid())
        derivative_error = abs(H_jet(rectangle)[1]-derivative)
        lhs = abs(c[0])+r*derivative_error
        rhs = r*abs(derivative)
        if not lhs < rhs or not center.real-r > arb('1/2'):
            raise ArithmeticError('off-line Rouché gate unresolved')
        return {'status': 'certified_one_simple_DH_zero_in_disk',
                'bits': 768, 'center_real': endpoints(center.real),
                'center_imag': endpoints(center.imag), 'radius': '1e-30',
                'residual_at_center': endpoints(abs(c[0])),
                'derivative_variation_upper': endpoints(derivative_error),
                'rouche_left': endpoints(lhs), 'rouche_right': endpoints(rhs),
                'real_part_above_half': endpoints(center.real-r-arb('1/2')),
                'argument': 'Derivative variation bounds the nonlinear remainder on the disk. Rouche against the exact nonzero linear derivative gives exactly one zero counted with multiplicity.'}


def finite_gates(cutoff=13, modes=16):
    with ctx.workprec(768):
        even, odd = assemble(cutoff, modes)
        ce, pe = inertia(even)
        co, po = inertia(odd)
        first = eigen_interval(even, 0, iterations=140)
        second = eigen_interval(even, 1, iterations=140)
        odd_first = eigen_interval(odd, 0, iterations=140)
        gap = second.min(odd_first)-first
        upper = arb(first.upper())
        shifted = [[even[i][j]-(upper if i == j else 0)
                    for j in range(modes+1)] for i in range(modes+1)]
        boundary = [[shifted[i][j]-arb(2).sqrt()*(shifted[i][0]+shifted[0][j])
                     +2*shifted[0][0] for j in range(1, modes+1)]
                    for i in range(1, modes+1)]
        cb, pb = inertia(boundary)
        if ce or co or cb or not first > 0 or not gap > 0:
            raise ArithmeticError('DH positive/simple/even/boundary finite gates failed')
        return {'status': 'certified_DH_finite_ground_gates',
                'C': cutoff, 'modes': modes, 'bits': 768,
                'lowest_even': endpoints(first), 'second_even': endpoints(second),
                'lowest_odd': endpoints(odd_first), 'ground_gap': endpoints(gap),
                'even_positive_pivots': [endpoints(p) for p in pe],
                'odd_positive_pivots': [endpoints(p) for p in po],
                'boundary_kernel_positive_pivots': [endpoints(p) for p in pb],
                'even_matrix': [[endpoints(x) for x in row] for row in even],
                'odd_matrix': [[endpoints(x) for x in row] for row in odd],
                'scope': 'Finite section only. Positive, simple, even ground state with nonzero boundary evaluation; not full-window positivity or global DH convergence.'}


def generate():
    return {'off_line_zero': zero_certificate(), 'finite_gates': finite_gates(),
            'source_sha256': {n: sha256(Path(__file__).with_name(n)) for n in
                             ['dh_zero_and_gates.py', 'dh_weil_certificate.py',
                              'davenport_heilbronn_control.py', 'certified_weil.py']},
            'prior_numeric_location_source': 'https://github.com/teal-sea/zeta-lab/issues/57'}


if __name__ == '__main__':
    OUT.mkdir(parents=True, exist_ok=True)
    result = generate()
    (OUT/'dh_zero_and_finite_gates.json').write_text(json.dumps(result, indent=2)+'\n')
    print(result['off_line_zero']['status'])
    print(result['finite_gates']['status'])
