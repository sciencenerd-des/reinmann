"""Independent comparison replay with 512-bit adaptive integrals.

The original verifier evaluates independent integrals at 256 bits. Its
1e-48 radius requirement failed at C=3.2; this wrapper raises precision,
preserves that requirement, and records both verifier source hashes.
"""
import argparse
import json
from pathlib import Path

from flint import arb, ctx

from certified_weil import entry
from full_ground_fourier import sha256
from threshold_ground_gap import box
from verify_window_positivity import independent_entry, verify
from weil_matrix import prime_powers


def replay(path):
    result = verify(path, independent=False)
    data = json.loads(Path(path).read_text())
    with ctx.workprec(512):
        a = arb(data['half_width']); c = (2*a).exp()
        powers = [(q, p) for q, p in prime_powers(int(c.ceil().fmpq())) if arb(q).log() < 2*a]
        beta, quad = box(data['beta']), box(data['quadrature_operator_error'])
        checks = []
        for parity, sector in enumerate(data['sectors']):
            for i, j in [(0, 0), (0, 1)]:
                value = independent_entry(2*i+parity, 2*j+parity, a, data['cutoff'], beta, powers)
                if not (box(sector['quadrature_matrix'][i][j])+arb(0, quad.upper())).overlaps(value):
                    raise ArithmeticError('independent frequency integral mismatch')
                checks.append([2*i+parity, 2*j+parity])
                print('512-bit independent entry checked:', checks[-1], flush=True)
        reduced = independent_entry(0, 0, a, data['cutoff'], beta, powers)
        if not entry(0, 0, 2*a, powers, c) >= reduced:
            raise ArithmeticError('independent geometric normalization failed')
    result.update({'independent_adaptive_integral_entries': checks,
                   'independent_geometric_constant_check': True,
                   'independent_integral_bits': 512,
                   'wrapper_sha256': sha256(Path(__file__))})
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    args.output.write_text(json.dumps(replay(args.certificate), indent=2)+'\n')
