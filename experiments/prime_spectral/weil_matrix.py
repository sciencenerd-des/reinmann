"""Finite arithmetic Weil form; floating-point diagnostics, never certificates.

Source: arXiv:2511.22755v1, equations 2.9--2.10 and 3.14--3.18.
Only Python's standard library is required. No zeta zeros are input.
"""
from __future__ import annotations

import argparse
import json
import hashlib
import math
from pathlib import Path

EULER_GAMMA = 0.5772156649015328606


def simpson(f, length: float, panels: int) -> float:
    if panels < 2 or panels % 2:
        raise ValueError("panels must be a positive even integer >= 2")
    step = length / panels
    return step / 3 * math.fsum(
        (1 if j in (0, panels) else 4 if j % 2 else 2) * f(j * step)
        for j in range(panels + 1)
    )


def prime_powers(cutoff: int) -> list[tuple[int, int]]:
    """All (p**k, p) up to the integer support cutoff, without duplicates."""
    if cutoff < 2:
        return []
    sieve = bytearray(b"\x01") * (cutoff + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(cutoff) + 1):
        if sieve[p]:
            sieve[p * p:cutoff + 1:p] = b"\x00" * ((cutoff - p * p) // p + 1)
    result = []
    for p in range(2, cutoff + 1):
        if sieve[p]:
            power = p
            while power <= cutoff:
                result.append((power, p))
                power *= p
    return sorted(result)


def correlation(m: int, n: int, y: float, length: float) -> float:
    """Even convolution q(U_m,U_n)(y), U_n=L^-1/2 exp(2 pi i n x/L)."""
    y = abs(y)
    if y >= length:
        return 0.0
    if m == n:
        return 2 * (1 - y / length) * math.cos(2 * math.pi * n * y / length)
    angle = math.pi * (m - n) * y / length
    sinc = math.sin(angle) / angle if angle else 1.0
    return -2 * y / length * math.cos(math.pi * (m + n) * y / length) * sinc


def components(m: int, n: int, length: float, panels: int, powers) -> dict[str, float]:
    q0 = 2.0 if m == n else 0.0
    q = lambda y: correlation(m, n, y, length)
    pole = simpson(lambda y: 2 * math.cosh(y / 2) * q(y), length, panels)

    def arch_integrand(y):
        if y == 0:
            return q0 / 4 - 1 / length
        # expm1 preserves the cancellation of the constant term near zero.
        numerator = math.expm1(y / 2) * q(y) + (q(y) - q0)
        return numerator / (2 * math.sinh(y))

    arch_tail = q0 / 2 * math.log(math.tanh(length / 2))
    arch = (math.log(4 * math.pi) + EULER_GAMMA) * q0 / 2
    arch += simpson(arch_integrand, length, panels) + arch_tail
    prime = math.fsum(math.log(p) / math.sqrt(power) * q(math.log(power))
                      for power, p in powers)
    return {"pole": pole, "archimedean": arch, "prime": prime,
            "archimedean_tail": arch_tail, "weil": pole - arch - prime}


def matrix(cutoff: int, modes: int, panels: int) -> list[list[float]]:
    if not 2 <= cutoff <= 100000:
        raise ValueError("cutoff must be an integer from 2 through 100000")
    if not 0 <= modes <= 16:
        raise ValueError("modes must be an integer from 0 through 16")
    length = math.log(cutoff)
    powers = prime_powers(cutoff)
    indices = range(-modes, modes + 1)
    return [[components(m, n, length, panels, powers)["weil"] for n in indices]
            for m in indices]


def jacobi(matrix_values, tolerance=1e-13):
    """Symmetric Jacobi diagonalization; residual bound is numerical only."""
    a = [row[:] for row in matrix_values]
    size = len(a)
    for iteration in range(max(1, 100 * size * size)):
        residual = max((math.fsum(abs(a[i][j]) for j in range(size) if i != j)
                        for i in range(size)), default=0.0)
        if residual <= tolerance:
            return sorted(a[i][i] for i in range(size)), residual, iteration
        p, q = max(((i, j) for i in range(size) for j in range(i + 1, size)),
                   key=lambda pair: abs(a[pair[0]][pair[1]]))
        angle = 0.5 * math.atan2(2 * a[p][q], a[q][q] - a[p][p])
        c, s = math.cos(angle), math.sin(angle)
        app, aqq, apq = a[p][p], a[q][q], a[p][q]
        for k in range(size):
            if k not in (p, q):
                kp, kq = a[k][p], a[k][q]
                a[k][p] = a[p][k] = c * kp - s * kq
                a[k][q] = a[q][k] = s * kp + c * kq
        a[p][p] = c * c * app - 2 * s * c * apq + s * s * aqq
        a[q][q] = s * s * app + 2 * s * c * apq + c * c * aqq
        a[p][q] = a[q][p] = 0.0
    raise ArithmeticError("Jacobi iteration limit reached")


def run(cutoff: int, modes: int, panels: int):
    coarse = matrix(cutoff, modes, panels)
    fine = matrix(cutoff, modes, 2 * panels)
    eigenvalues, residual, iterations = jacobi(fine)
    entry_delta = max(abs(a - b) for ra, rb in zip(coarse, fine) for a, b in zip(ra, rb))
    return {"schema_version": 1, "status": "uncertified_float_diagnostic",
            "source": "https://arxiv.org/html/2511.22755v1",
            "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "smallest_eigenvalue_diagnostic": (
                "unresolved_at_observed_refinement_scale"
                if eigenvalues[0] <= (2*modes+1)*entry_delta + residual
                else "positive_above_observed_refinement_scale_not_certified"),
            "cutoff": cutoff, "L": math.log(cutoff), "lambda": math.sqrt(cutoff),
            "modes": modes, "dimension": 2 * modes + 1, "fine_panels": 2 * panels,
            "prime_powers": prime_powers(cutoff), "matrix": fine,
            "eigenvalues_of_finite_weil_form": eigenvalues,
            "jacobi_offdiagonal_row_residual": residual, "jacobi_iterations": iterations,
            "refinement_max_entry_difference": entry_delta,
            "refinement_operator_norm_difference_upper_estimate": (2 * modes + 1) * entry_delta,
            "limitations": ["Refinement difference is not a quadrature error bound.",
                            "Floating-point rounding is not enclosed.",
                            "Finite Weil-form eigenvalues are not zeta zero ordinates.",
                            "No growing-mode or growing-support convergence is certified."]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cutoff", type=int, default=13)
    parser.add_argument("--modes", type=int, default=3)
    parser.add_argument("--panels", type=int, default=1024)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        if not 2 <= args.panels <= 65536 or args.panels % 2:
            raise ValueError("panels must be even and between 2 and 65536")
        result = run(args.cutoff, args.modes, args.panels)
    except (ValueError, ArithmeticError) as exc:
        parser.error(str(exc))
    output = json.dumps(result, indent=2, allow_nan=False) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output)
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
