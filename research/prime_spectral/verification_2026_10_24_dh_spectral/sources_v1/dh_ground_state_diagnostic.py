"""Finite DH/zeta spectral negative control; numerical diagnostics, not RH.

See DH_SPECTRAL_PREREGISTRATION_2026_10_24.md for conventions and predictions.
Arb assembles matrices; midpoint eigenpairs and roots are approximate. Prolate
trials use double precision. Residuals are finite projected residuals only.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import subprocess

import mpmath as mp
import numpy as np
from numpy.polynomial.legendre import leggauss, legval
from scipy.linalg import eigh_tridiagonal
from flint import acb_mat, arb, ctx

from certified_weil import endpoints
from closed_weil import entry_closed
from davenport_heilbronn_control import dirichlet_coefficients
from dh_weil_certificate import assemble as dh_assemble
from prolate_candidate_diagnostic import _legendre_a, project_candidate
from weil_matrix import prime_powers


def midpoint(value):
    return mp.mpf(value.mid().str(mp.mp.dps, radius=False))


def decimal(value):
    return mp.nstr(value, min(65, mp.mp.dps))


def zeta_assemble(cutoff, modes, bits):
    length = arb(cutoff).log()
    powers = [(q, p) for q, p in prime_powers(cutoff) if q < cutoff]
    terms = math.ceil((bits + 32) * math.log(2) / (2 * math.log(cutoff)))
    def cell(m, n):
        return entry_closed(m, n, length, powers, terms)
    b = [arb(0)] + [n * cell(n, 0) for n in range(1, modes + 1)]
    even = [[arb(0) for _ in range(modes + 1)] for _ in range(modes + 1)]
    odd = [[arb(0) for _ in range(modes)] for _ in range(modes)]
    even[0][0] = cell(0, 0)
    for n in range(1, modes + 1):
        even[0][n] = even[n][0] = arb(2).sqrt() * b[n] / n
        even[n][n] = cell(n, n) + cell(n, -n)
        odd[n-1][n-1] = cell(n, n) - cell(n, -n)
        for m in range(1, n):
            even[m][n] = even[n][m] = 2*(n*b[n]-m*b[m])/(n*n-m*m)
            odd[m-1][n-1] = odd[n-1][m-1] = 2*(m*b[n]-n*b[m])/(n*n-m*m)
    return even, odd


def dh_candidate(cutoff, modes, terms=100, nodes=96):
    """E_DH of first odd prolate mode, with conductor-5 Fourier scaling."""
    if cutoff < 2 or modes < 1 or terms < 3 or nodes < 8:
        raise ValueError('invalid DH projection parameters')
    length, lam = np.log(cutoff), np.sqrt(cutoff)
    angular = 2 * np.pi * cutoff / 5
    degrees = 2 * np.arange(terms) + 1
    diagonal = np.array([ell*(ell+1) + angular**2 * (
        _legendre_a(ell+1)**2 + _legendre_a(ell)**2) for ell in degrees])
    off = np.array([angular**2*_legendre_a(ell+1)*_legendre_a(ell+2)
                    for ell in degrees[:-1]])
    eigenvalues, vectors = eigh_tridiagonal(
        diagonal, off, select='i', select_range=(0, 0))
    coefficients = np.zeros(2*terms)
    coefficients[1::2] = vectors[:, 0]*np.sqrt((2*degrees+1)/2)
    a = [float(x) for x in dirichlet_coefficients(cutoff)]

    def k_at(t):
        u = np.exp(t)
        value = np.zeros_like(u)
        for n in range(1, cutoff + 1):
            present = n*u <= lam
            value[present] += a[n]*legval(n*u[present]/lam, coefficients)
        return np.sqrt(u)*value

    x, w = leggauss(nodes)
    thresholds = sorted(np.log(lam/n) for n in range(1, cutoff + 1))
    projected = np.zeros(modes + 1)
    norm_squared = symmetry_squared = 0.0
    for left, right in zip(thresholds[:-1], thresholds[1:]):
        t = (left+right)/2+(right-left)*x/2
        weights = (right-left)*w/2
        k = k_at(t)
        projected[0] += np.sum(weights*k)/np.sqrt(length)
        for n in range(1, modes + 1):
            projected[n] += np.sqrt(2/length)*np.sum(
                weights*k*np.cos(2*np.pi*n*(t+length/2)/length))
        norm_squared += np.sum(weights*k*k)
        symmetry_squared += np.sum(weights*(k-k_at(-t))**2)
    norm = np.linalg.norm(projected)
    if not norm > 0 or not norm_squared > 0:
        raise ArithmeticError('zero DH trial')
    unit = projected/norm
    if unit[0] < 0:
        unit = -unit
    return {'unit_coefficients': unit.tolist(),
            'reflection_defect_ratio': float(np.sqrt(symmetry_squared/norm_squared)),
            'projected_l2_fraction': float(norm/np.sqrt(norm_squared)),
            'first_odd_prolate_eigenvalue': float(eigenvalues[0]),
            'angular_parameter': float(angular)}


def spectrum(matrix):
    values, vectors = acb_mat(matrix).eig(right=True, algorithm='approx')
    if not all(v.is_finite() and v.imag.contains(0) for v in values):
        raise ArithmeticError('real midpoint spectrum unresolved')
    order = sorted(range(len(values)), key=lambda j: midpoint(values[j].real))
    ordered = [midpoint(values[j].real) for j in order]
    vector = mp.matrix([midpoint(vectors[i, order[0]].real)
                        for i in range(len(matrix))])
    vector /= mp.norm(vector)
    if vector[0] < 0:
        vector = -vector
    return ordered, vector


def fourier_even(coefficients, length, height):
    """Centered cosine integral, including its removable singularities."""
    z = mp.mpf(height)
    def integral(frequency):
        return length*mp.sinc(frequency*length/2)
    value = coefficients[0]*integral(z)/mp.sqrt(length)
    for n in range(1, len(coefficients)):
        frequency = 2*mp.pi*n/length
        value += (coefficients[n]*(-1)**n/mp.sqrt(2*length)
                  * (integral(z-frequency)+integral(z+frequency)))
    return value


def real_roots(coefficients, length, maximum=100, step=mp.mpf('0.2')):
    """Sign-changing roots only; not a zero-count or complex-root certificate."""
    roots = []
    def f(t):
        return fourier_even(coefficients, length, t)
    left, fl = mp.mpf(0), f(0)
    while left < maximum:
        right = min(left+step, mp.mpf(maximum))
        fr = f(right)
        if fl*fr < 0 or fr == 0:
            lo, hi, flo = left, right, fl
            for _ in range(100):
                mid = (lo+hi)/2
                fm = f(mid)
                if flo*fm <= 0:
                    hi = mid
                else:
                    lo, flo = mid, fm
            root = (lo+hi)/2
            if not roots or abs(root-roots[-1]) > mp.mpf('1e-20'):
                roots.append(root)
        left, fl = right, fr
    return roots


def reference_zeros(kind, maximum):
    if kind == 'dh':
        path = Path('research/prime_spectral/verification_2026_10_13_calibration/dh5_refined_atlas.json')
        data = json.loads(path.read_text())
        values = [mp.mpf(str(Fraction(x['imag']['lo']).numerator)) /
                  Fraction(x['imag']['lo']).denominator for x in data['critical_line_disks']]
        return [x for x in values if 0 < x <= maximum], str(path)
    values, n = [], 1
    while True:
        t = mp.im(mp.zetazero(n))
        if t > maximum:
            return values, 'mpmath.zetazero; comparison only, not matrix input'
        values.append(t)
        n += 1


def analyze(kind, cutoff, modes, bits, terms, nodes, maximum):
    with ctx.workprec(bits), mp.workprec(bits):
        even, odd = (dh_assemble(cutoff, modes) if kind == 'dh'
                     else zeta_assemble(cutoff, modes, bits))
        ev, ground = spectrum(even)
        ov, _ = spectrum(odd)
        matrix = mp.matrix([[midpoint(x) for x in row] for row in even])
        gap = min(ev[1], ov[0])-ev[0]
        eigen_residual = mp.norm(matrix*ground-ev[0]*ground)
        entry_radius = max(mp.mpf(str(x.rad().upper().fmpq().p)) /
                           int(x.rad().upper().fmpq().q) for row in even for x in row)
        trial_data = (dh_candidate(cutoff, modes, terms, nodes) if kind == 'dh'
                      else project_candidate(cutoff, modes, terms, nodes))
        # These are the exact decimals representing a floating trial, not an
        # enclosure of the exact prolate projection.
        trial = mp.matrix([mp.mpf(repr(x)) for x in trial_data['unit_coefficients']])
        trial /= mp.norm(trial)
        mu = (trial.T*matrix*trial)[0]
        residual = mp.norm(matrix*trial-mu*trial)
        clearance = min(ev[1], ov[0])-mu
        overlap = abs((ground.T*trial)[0])
        length = mp.log(cutoff)
        boundary = (ground[0]+mp.sqrt(2)*sum(ground[1:]))/mp.sqrt(length)
        roots = real_roots(ground, length, maximum)
        references, reference_source = reference_zeros(kind, maximum)
        offsets = [{'line_zero': decimal(t),
                    'nearest_transform_root': decimal(min(roots, key=lambda x: abs(x-t))),
                    'absolute_offset': decimal(min(abs(x-t) for x in roots))}
                   for t in references] if roots else []
        return {'kind': kind, 'C': cutoff, 'modes': modes, 'bits': bits,
                'candidate_legendre_terms': terms, 'candidate_quadrature_nodes': nodes,
                'even_lowest': [decimal(x) for x in ev[:3]],
                'odd_lowest': [decimal(x) for x in ov[:2]],
                'global_gap_from_even': decimal(gap),
                'ground_is_even_midpoint_diagnostic': bool(gap > 0),
                'ground_coefficients': [decimal(x) for x in ground],
                'ground_boundary_value': decimal(boundary),
                'midpoint_ground_eigen_residual': decimal(eigen_residual),
                'even_entry_radius_max': decimal(entry_radius),
                'midpoint_eigen_residual_over_gap': decimal(eigen_residual/gap) if gap > 0 else None,
                'candidate': trial_data,
                'candidate_rayleigh': decimal(mu),
                'candidate_projected_residual': decimal(residual),
                'candidate_residual_over_global_gap': decimal(residual/gap) if gap > 0 else None,
                'global_second_minus_candidate_rayleigh': decimal(clearance),
                'candidate_ground_overlap': decimal(overlap),
                'ground_distance_from_residual_clearance': (
                    decimal(mp.sqrt(2)*residual/clearance) if clearance > 0 and gap > 0 else None),
                'root_search': {'maximum_height': maximum, 'step': '0.2',
                                'method': 'sign changes and 100 bisections; even multiplicities may be missed'},
                'real_transform_roots': [decimal(x) for x in roots],
                'line_zero_offsets': offsets, 'reference_zero_source': reference_source,
                'scope': 'Finite midpoint ground vector; double-precision projected candidate; no full-operator residual or convergence claim.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kind', choices=('dh', 'zeta'), default='dh')
    parser.add_argument('--cutoffs', type=int, nargs='+', default=[10, 13, 14, 20, 31, 35])
    parser.add_argument('--modes', type=int, nargs='+', default=[32, 64])
    parser.add_argument('--bits', type=int, default=512)
    parser.add_argument('--legendre-terms', type=int, default=100)
    parser.add_argument('--quadrature-nodes', type=int, default=96)
    parser.add_argument('--maximum-height', type=int, default=100)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError('refusing to overwrite a diagnostic receipt')
    if args.bits < 256 or any(not 2 <= c <= 1000 for c in args.cutoffs) or any(
            not 1 <= n <= 128 for n in args.modes) or args.maximum_height < 1:
        raise ValueError('invalid finite diagnostic range')
    records = []
    sources = ['dh_ground_state_diagnostic.py', 'dh_weil_certificate.py',
               'davenport_heilbronn_control.py', 'certified_weil.py',
               'closed_weil.py', 'prolate_candidate_diagnostic.py', 'weil_matrix.py']
    provenance = {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                  for name in sources}
    for cutoff in args.cutoffs:
        for modes in args.modes:
            record = analyze(args.kind, cutoff, modes, args.bits,
                             args.legendre_terms, args.quadrature_nodes, args.maximum_height)
            records.append(record)
            print(args.kind, cutoff, modes, 'ground', record['even_lowest'][0],
                  'r/gap', record['candidate_residual_over_global_gap'],
                  'overlap', record['candidate_ground_overlap'], flush=True)
    references = {r['reference_zero_source'] for r in records}
    result = {'status': 'finite_spectral_diagnostic_not_certificate',
              'base_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
              'source_sha256': provenance,
              'reference_sha256': {p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
                                   for p in references if Path(p).is_file()},
              'preregistration_sha256': hashlib.sha256(Path(
                  'research/prime_spectral/DH_SPECTRAL_PREREGISTRATION_2026_10_24.md').read_bytes()).hexdigest(),
              'records': records}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
