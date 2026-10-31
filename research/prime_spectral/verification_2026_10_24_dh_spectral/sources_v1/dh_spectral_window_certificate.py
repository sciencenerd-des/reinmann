"""Certify one finite DH ground eigenpair's sign, parity, gap and boundary.

This does not certify Fourier roots, a full-operator eigenpair or convergence.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from flint import arb, ctx

from certified_weil import endpoints
from dh_weil_certificate import assemble
from isolated_kernel import isolated_spectrum


def certify(cutoff=31, modes=64, bits=768):
    if bits < 512:
        raise ValueError('at least 512 working bits required')
    with ctx.workprec(bits):
        even, odd = assemble(cutoff, modes)
        ev, raw = isolated_spectrum(even)
        ov, _ = isolated_spectrum(odd)
        gap = ev[1].min(ov[0])-ev[0]
        norm = sum((v*v for v in raw), arb(0)).sqrt()
        if not norm > 0 or not gap > 0:
            raise ArithmeticError('simple even finite ground unresolved')
        vector = [v/norm for v in raw]
        boundary = (vector[0]+arb(2).sqrt()*sum(vector[1:], arb(0)))/arb(cutoff).log().sqrt()
        if boundary.contains(0) or ev[0].contains(0):
            raise ArithmeticError('ground sign or nonzero boundary unresolved')
        return {'status': 'certified_finite_DH_ground_sign_parity_gap_boundary',
                'C': cutoff, 'modes': modes, 'bits': bits,
                'ground_sign': 'negative' if ev[0] < 0 else 'positive',
                'even_lowest': [endpoints(x) for x in ev[:3]],
                'odd_lowest': [endpoints(x) for x in ov[:2]],
                'global_gap': endpoints(gap),
                'unit_ground_coefficients': [endpoints(x) for x in vector],
                'boundary_value': endpoints(boundary),
                'algorithm': 'Arb geometric integrals; FLINT Rump eigenpair isolation with ordered disjoint spectral intervals in both parities',
                'scope': 'One finite Fourier compression only. No full-operator simplicity, zero-location replay, rank convergence or arithmetic separating inequality.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cutoff', type=int, default=31)
    parser.add_argument('--modes', type=int, default=64)
    parser.add_argument('--bits', type=int, default=768)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError('refusing to overwrite a certificate')
    result = certify(args.cutoff, args.modes, args.bits)
    result['base_commit'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
    result['source_sha256'] = {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
        for name in ('dh_spectral_window_certificate.py', 'dh_weil_certificate.py',
                     'isolated_kernel.py', 'davenport_heilbronn_control.py', 'certified_weil.py')}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'], result['ground_sign'])


if __name__ == '__main__':
    main()
