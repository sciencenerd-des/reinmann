"""Rigorous Xi coefficient balls from FLINT series and an independent theta integral.

Trust boundary: FLINT/Arb numerical algorithms and the stated classical formulas;
these certificates are not proofs checked by the Lean kernel.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
from pathlib import Path

import flint
from flint import acb, acb_series, arb, ctx


def endpoints(value: arb) -> dict[str, str]:
    if not value.is_finite():
        raise ArithmeticError("nonfinite coefficient enclosure")
    return {"lo": str(value.lower().fmpq()), "hi": str(value.upper().fmpq())}


def taylor_coefficients(max_n: int, bits: int) -> list[arb]:
    """mu_n=[z^(2n)]xi(1/2+z), ordinary positive folded coefficients."""
    ctx.prec = bits
    ctx.cap = 2 * max_n + 1
    s = acb_series([arb(1) / 2, 1])
    xi = s * (s - 1) / 2 * ((-s / 2) * arb.pi().log()).exp()
    xi = xi * (s / 2).gamma() * s.zeta()
    for k in range(2 * max_n + 1):
        if not xi[k].is_finite() or not xi[k].imag.contains(0):
            raise ArithmeticError(f"nonreal or nonfinite series coefficient {k}")
        if k % 2 and not xi[k].real.contains(0):
            raise ArithmeticError(f"evenness check failed at coefficient {k}")
    return [xi[2 * n].real for n in range(max_n + 1)]


def theta_tail_bounds(n: int, terms: int, upper: int) -> tuple[arb, arb]:
    """Upper bounds on omitted theta terms on [0,U] and all terms on [U,infinity).

    Proof and normalization are in README.md. All inequalities are checked in
    ball arithmetic, so uncertain denominators fail closed.
    """
    if n < 0 or terms < 1 or upper < 1:
        raise ValueError("n>=0, terms>=1 and upper>=1 required")
    pi, u = arb.pi(), arb(upper)
    j = terms + 1
    q_terms = 16 * (-pi / 2 * (2 * j + 1)).exp()
    if not q_terms < 1:
        raise ArithmeticError("theta term-tail geometric ratio not below one")
    sum_tail = j**4 * (-pi * j**2 / 2).exp() / (1 - q_terms)
    common = 8 * pi**2 / math.factorial(2 * n)
    finite_tail = common * u ** (2 * n + 1) * (arb(9) * u / 2).exp()
    finite_tail *= (-pi / 2).exp() * sum_tail

    e = (2 * u).exp()
    q_space = 16 * (-3 * pi * e).exp()
    rate = 2 * pi * e - arb(9) / 2 - 2 * n / u
    if not q_space < 1 or not rate > 0:
        raise ArithmeticError("theta spatial tail needs a larger upper cutoff")
    spatial_tail = common * u ** (2 * n) * (arb(9) * u / 2 - pi * e).exp()
    spatial_tail /= (1 - q_space) * rate
    return finite_tail.upper(), spatial_tail.upper()


def theta_coefficient(n: int, terms: int, upper: int, bits: int,
                      accuracy: int) -> tuple[arb, dict]:
    ctx.prec = bits
    pi = arb.pi()
    normalization = arb(2) / math.factorial(2 * n)
    constants = [(4 * pi**2 * j**4, 6 * pi * j**2, pi * j**2)
                 for j in range(1, terms + 1)]

    def integrand(u: acb, _analytic: bool) -> acb:
        # Every operation is entire in u; no branch-cut qualification needed.
        e2, e9, e5 = (2 * u).exp(), (arb(9) * u / 2).exp(), (arb(5) * u / 2).exp()
        total = acb(0)
        for a, b, c in constants:
            total += (a * e9 - b * e5) * (-c * e2).exp()
        return normalization * u ** (2 * n) * total

    integral = acb.integral(integrand, 0, upper,
                            rel_tol=arb(2) ** (-accuracy - 16),
                            abs_tol=arb(2) ** (-accuracy - 160),
                            eval_limit=200000, depth_limit=40)
    if not integral.is_finite() or not integral.imag.contains(0):
        raise ArithmeticError("theta quadrature did not produce a real finite ball")
    series_tail, spatial_tail = theta_tail_bounds(n, terms, upper)
    value = integral.real + arb(0, (series_tail + spatial_tail).upper())
    if value.rel_accuracy_bits() < accuracy:
        raise ArithmeticError(f"theta n={n}: achieved only {value.rel_accuracy_bits()} bits")
    return value, {
        "finite_integral": endpoints(integral.real),
        "omitted_terms_absolute_upper": str(series_tail.fmpq()),
        "spatial_tail_absolute_upper": str(spatial_tail.fmpq()),
        "enclosure": endpoints(value),
        "relative_accuracy_bits": value.rel_accuracy_bits(),
    }


def generate(max_n: int = 32, bits: int = 1024, accuracy: int = 128,
             theta_max_n: int = 4, theta_terms: int = 12,
             theta_upper: int = 4, max_bits: int = 8192) -> dict:
    if not 0 <= max_n <= 256 or not -1 <= theta_max_n <= min(max_n, 32):
        raise ValueError("0<=max_n<=256 and -1<=theta_max_n<=min(max_n,32) required")
    if not 32 <= accuracy <= 1024 or not 128 <= bits <= max_bits <= 16384:
        raise ValueError("invalid precision budget")
    if not 1 <= theta_terms <= 64 or not 1 <= theta_upper <= 16:
        raise ValueError("invalid theta truncation budget")
    while True:
        mu = taylor_coefficients(max_n, bits)
        achieved = min(value.rel_accuracy_bits() for value in mu)
        if achieved >= accuracy and all(value > 0 for value in mu):
            break
        if bits >= max_bits:
            raise ArithmeticError(f"Taylor accuracy/positivity unresolved at {bits} bits")
        bits = min(bits * 2, max_bits)
    coeffs = [{"n": n, **endpoints(value),
               "relative_accuracy_bits": value.rel_accuracy_bits()}
              for n, value in enumerate(mu)]
    theta = []
    for n in range(theta_max_n + 1):
        value, evidence = theta_coefficient(n, theta_terms, theta_upper,
                                           max(256, accuracy + 128), accuracy)
        if not value.overlaps(mu[n]):
            raise ArithmeticError(f"independent formula disagreement at n={n}")
        theta.append({"n": n, "overlaps_taylor": True, **evidence})
    return {
        "schema_version": 1,
        "status": "rigorous_ball_enclosures_not_Lean_certificates",
        "convention": "mu_n = (-1)^n XiCoeff(n) = [z^(2n)]xi(1/2+z); ordinary, not n!-weighted",
        "method": "FLINT acb_series zeta/gamma/exp with rigorous analytic remainders",
        "flint_python_version": flint.__version__,
        "python_version": platform.python_version(),
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "max_n": max_n, "working_bits": bits, "requested_accuracy_bits": accuracy,
        "minimum_relative_accuracy_bits": achieved,
        "coefficients": coeffs,
        "theta_check": {"terms": theta_terms, "upper": theta_upper,
                        "formula": "mu_n=2/(2n)! integral_0^infinity u^(2n) Phi(u) du",
                        "records": theta},
        "trust_boundary": ["FLINT/Arb implementation and arithmetic",
                           "classical xi formula and theta representation",
                           "analytic tail inequalities documented in README",
                           "not independently checked by Lean"],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=32)
    parser.add_argument("--bits", type=int, default=1024)
    parser.add_argument("--accuracy", type=int, default=128)
    parser.add_argument("--theta-max-n", type=int, default=4)
    parser.add_argument("--theta-terms", type=int, default=12)
    parser.add_argument("--theta-upper", type=int, default=4)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        result = generate(args.max_n, args.bits, args.accuracy, args.theta_max_n,
                          args.theta_terms, args.theta_upper)
    except (ValueError, ArithmeticError) as exc:
        parser.error(str(exc))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Enclosed {result['max_n']+1} coefficients at >= "
          f"{result['minimum_relative_accuracy_bits']} relative bits; "
          f"{len(result['theta_check']['records'])} independent theta checks.")


if __name__ == "__main__":
    main()
