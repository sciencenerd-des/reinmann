"""Certified eigenpair isolation for higher-mode prime kernels.

Uses FLINT's certified Rump algorithm, never approximate eigenpair output.
Avoids interval LDL dependency loss; changes no defining Weil matrix entries.
"""
import argparse
import hashlib
import json
from pathlib import Path
from flint import arb, acb_mat, ctx
from certified_weil import certified_matrix, endpoints
from positive_kernel import bernstein_coefficients
from eigenvector_coefficients import direct_coefficients


def isolated_spectrum(matrix):
    values, vectors = acb_mat(matrix).eig(right=True, algorithm='rump')
    if not all(x.is_finite() and x.imag.contains(0) for x in values):
        raise ArithmeticError('finite real spectrum unresolved')
    # Midpoints only propose an order; strict interval separation proves it.
    ordering = sorted(range(len(values)), key=lambda i: values[i].real.mid())
    ordered = [values[i].real for i in ordering]
    if not all(a < b for a, b in zip(ordered, ordered[1:])):
        raise ArithmeticError('simple ordered spectrum unresolved')
    return ordered, [vectors[i, ordering[0]].real for i in range(len(values))]


def run(cutoff=13, modes=12):
    with ctx.workprec(512):
        _, even, odd = certified_matrix(cutoff, modes)
        ev, v = isolated_spectrum(even)
        ov, _ = isolated_spectrum(odd)
        gap = ev[1].min(ov[0])-ev[0]
        if not ev[0] > 0 or not ov[0] > 0 or not gap > 0:
            raise ArithmeticError('positive simple even lowest eigenvalue unresolved')
        root2 = arb(2).sqrt()
        boundary = v[0]+root2*sum(v[1:], arb(0))
        if boundary.contains(0):
            raise ArithmeticError('nonzero boundary eigenvector normalization unresolved')
        half = [v[0]/boundary]+[x/(root2*boundary) for x in v[1:]]
        if not half[0] > 0:
            raise ArithmeticError('positive kernel mass unresolved')
        bernstein = bernstein_coefficients(half[1:])
        if not all(x > 0 for x in bernstein):
            raise ArithmeticError('whole-support kernel positivity unresolved')
        length = arb(cutoff).log()
        coefficients = direct_coefficients(half, length, min(3, modes))
        variance = length**2*(half[0]/12+sum((half[n]/n**2 for n in range(1,modes+1)),arb(0))/arb.pi()**2)/half[0]
        if not variance > 0 or not -coefficients[1] > 0:
            raise ArithmeticError('positive variance or spectral sum unresolved')
        return {'schema_version': 1, 'status': 'certified_finite_isolated_prime_kernel_not_uniform',
                'cutoff': cutoff, 'modes': modes, 'working_bits': 512,
                'eigenpair_algorithm': 'FLINT acb_mat.eig algorithm=rump; certified isolation',
                'even_spectrum': [endpoints(x) for x in ev],
                'odd_spectrum': [endpoints(x) for x in ov],
                'spectral_gap': endpoints(gap), 'raw_boundary_evaluation': endpoints(boundary),
                'boundary_normalized_positive_half': [endpoints(x) for x in half],
                'bernstein_coefficients': [endpoints(x) for x in bernstein],
                'variance': endpoints(variance), 'spectral_sum': endpoints(-coefficients[1]),
                'even_quotient_coefficients': [endpoints(x) for x in coefficients],
                'claim': 'Only this finite configuration: positive Weil matrix, simple even lowest eigenvector with nonzero boundary, positive spatial probability kernel, and the existing finite real-zero quotient/profile conclusion.',
                'remaining': 'No uniform gates, bounded variance along increasing support, or weak convergence to Xi theta measure.',
                'source_hashes': {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest() for name in
                                 ('isolated_kernel.py','certified_weil.py','weil_matrix.py','positive_kernel.py','eigenvector_coefficients.py')},
                'trust_boundary': 'Original interval matrix construction, certified eigenpair isolation and exact parity/displacement/Bernstein arguments; not Lean formalized.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cutoff',type=int,default=13)
    parser.add_argument('--modes',type=int,default=12)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=run(args.cutoff,args.modes)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],result['modes'])


if __name__=='__main__':
    main()
