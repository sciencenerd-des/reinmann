"""Arb Sturm brackets and infinite-tail gaps for even prolate modes.

This certifies eigenvalue isolation, not eigenvectors or the candidate's
Fourier coefficients. It uses no zeta zeros or Weil-matrix eigenvectors.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb, ctx


def _a(index: int) -> arb:
    if index == 0:
        return arb(0)
    return arb(index) / (arb((2 * index - 1) * (2 * index + 1))).sqrt()


def jacobi_entries(cutoff: int, terms: int) -> tuple[list[arb], list[arb], arb, int]:
    if type(cutoff) is not int or cutoff < 2 or type(terms) is not int or terms < 4:
        raise ValueError('integer cutoff at least 2 and at least four even terms required')
    c_squared = (2 * arb.pi() * cutoff) ** 2
    diagonal = []
    off_diagonal = []
    for k in range(terms):
        degree = 2 * k
        diagonal.append(degree * (degree + 1)
                        + c_squared * (_a(degree) ** 2 + _a(degree + 1) ** 2))
        if k + 1 < terms:
            off_diagonal.append(c_squared * _a(degree + 1) * _a(degree + 2))
    beta = c_squared * _a(2 * terms - 1) * _a(2 * terms)
    tail_floor = 2 * terms * (2 * terms + 1)
    return diagonal, off_diagonal, beta, tail_floor


def sturm_count(diagonal: list[arb], off_diagonal: list[arb], shift: Fraction) -> int:
    if len(off_diagonal) + 1 != len(diagonal):
        raise ValueError('tridiagonal dimensions differ')
    shift_ball = arb(shift.numerator) / arb(shift.denominator)
    pivot = diagonal[0] - shift_ball
    if pivot.contains(0):
        raise ArithmeticError('Sturm pivot sign unresolved')
    negative = int(pivot < 0)
    for k in range(1, len(diagonal)):
        pivot = diagonal[k] - shift_ball - off_diagonal[k - 1] ** 2 / pivot
        if pivot.contains(0):
            raise ArithmeticError('Sturm pivot sign unresolved')
        negative += int(pivot < 0)
    return negative


def bracket(diagonal: list[arb], off_diagonal: list[arb], index: int,
            iterations: int = 96) -> tuple[Fraction, Fraction]:
    if type(index) is not int or not 0 <= index < len(diagonal):
        raise ValueError('eigenvalue index out of range')
    if type(iterations) is not int or iterations < 1:
        raise ValueError('positive bisection count required')
    bound = max(x.upper() for x in diagonal) + 2 * max(x.upper() for x in off_diagonal)
    width = int(bound.ceil().fmpq()) + 1
    lo, hi = Fraction(-width), Fraction(width)
    if sturm_count(diagonal, off_diagonal, lo) > index:
        raise ArithmeticError('lower spectral bracket unresolved')
    if sturm_count(diagonal, off_diagonal, hi) <= index:
        raise ArithmeticError('upper spectral bracket unresolved')
    for _ in range(iterations):
        mid = (lo + hi) / 2
        if sturm_count(diagonal, off_diagonal, mid) <= index:
            lo = mid
        else:
            hi = mid
    return lo, hi


def run(cutoff: int, terms: int = 80, tail_cut: int = 1500) -> dict:
    with ctx.workprec(256):
        diagonal, off_diagonal, beta, floor = jacobi_entries(cutoff, terms)
        if type(tail_cut) is not int or tail_cut >= floor:
            raise ValueError('integer tail cut must be below the tail floor')
        brackets = [bracket(diagonal, off_diagonal, j) for j in range(4)]
        if not all(hi < tail_cut for _, hi in brackets):
            raise ArithmeticError('target finite eigenvalue exceeds tail cut')
        tau = (beta ** 2 / (floor - tail_cut)).upper().fmpq()
        shift = Fraction(str(tau))
        full = [(lo - shift, hi) for lo, hi in brackets]
        gaps = [full[j + 1][0] - full[j][1] for j in range(3)]
        if not all(gap > 0 for gap in gaps):
            raise ArithmeticError('full low-mode isolation unresolved')
        return {
            'status': 'certified_even_prolate_low_mode_isolation_not_candidate_projection',
            'cutoff': cutoff,
            'even_legendre_terms': terms,
            'working_bits': 256,
            'bisection_steps': 96,
            'tail_cut': tail_cut,
            'tail_floor': floor,
            'coupling_beta_interval': {'lo': str(beta.lower().fmpq()),
                                       'hi': str(beta.upper().fmpq())},
            'schur_shift_upper': str(shift),
            'finite_eigenvalue_intervals': [
                {'lo': str(lo), 'hi': str(hi)} for lo, hi in brackets],
            'full_eigenvalue_intervals': [
                {'lo': str(lo), 'hi': str(hi)} for lo, hi in full],
            'consecutive_full_gap_lower': [str(gap) for gap in gaps],
            'generator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'scope': ('Schur-complement inertia and the positive infinite Legendre '
                      'tail isolate the first four even prolate eigenvalues.'),
            'remaining': ('This Jacobi certificate alone does not enclose prolate '
                          'eigenvectors or Fourier coefficients, or prove a Weil '
                          'residual/gap or RH.'),
        }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cutoff', type=int, required=True)
    parser.add_argument('--terms', type=int, default=80)
    parser.add_argument('--tail-cut', type=int, default=1500)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.cutoff, args.terms, args.tail_cut)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])


if __name__ == '__main__':
    main()
