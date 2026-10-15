"""Numerical diagnostics for the infinite, symbolic Fock coefficient identities.

These checks are not interval certificates and do not assert zeta-zero inputs.
The infinite sums and arithmetic membership are verified separately in Lean.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp


def check_mode(real: str, imag: str, degree: int) -> dict:
    s = mp.mpc(real, imag)
    radius = abs(s) ** 2
    coefficient = mp.exp(-radius / 2)
    factorial = mp.mpf(1)
    coeffs, weights = [], []
    for n in range(degree + 1):
        coeffs.append(coefficient)
        weights.append(factorial)
        coefficient *= s / (n + 1)
        factorial *= n + 1
    lam = -mp.j * (s - mp.mpf("0.5"))
    action = [
        -mp.j * ((n + 1) * (coeffs[n + 1] if n < degree else 0) - coeffs[n] / 2)
        for n in range(degree + 1)
    ]
    residual = [w - lam * v for w, v in zip(action, coeffs)]

    def pair(left, right):
        return mp.fsum(w * a * mp.conj(b) for w, a, b in zip(weights, left, right))

    mass = pair(coeffs, coeffs).real
    defect = pair(action, coeffs) - pair(coeffs, action)
    residual_defect = pair(residual, coeffs) - pair(coeffs, residual)
    identity_error = abs(defect - residual_defect - (lam - mp.conj(lam)) * mass)
    residual_norm = mp.sqrt(pair(residual, residual).real)
    assert degree + 2 > radius
    next_mass_term = mp.exp(-radius) * radius ** (degree + 1) / mp.factorial(degree + 1)
    tail_bound = next_mass_term / (1 - radius / (degree + 2))
    tolerance = mp.mpf("1e-65")
    assert 0 < mass <= 1 + tolerance
    assert abs(1 - mass) <= tail_bound + tolerance
    assert identity_error < tolerance
    assert abs(defect - (lam - mp.conj(lam)) * mass) <= 2 * residual_norm * mp.sqrt(mass) + tolerance
    return {
        "s": [real, imag],
        "input_is_certified_zeta_zero": False,
        "degree": degree,
        "truncated_mass": mp.nstr(mass, 30),
        "mass_tail_bound_formula_evaluated": mp.nstr(tail_bound, 15),
        "truncated_eigenvector_residual_norm": mp.nstr(residual_norm, 15),
        "truncated_symmetry_defect_norm": mp.nstr(abs(defect), 20),
        "infinite_normalized_defect_norm": mp.nstr(2 * abs(s.real - mp.mpf("0.5")), 20),
        "residual_identity_error": mp.nstr(identity_error, 10),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("fock_diagnostics.json"))
    args = parser.parse_args()
    mp.mp.dps = 90
    record = {
        "status": "numerical_sanity_checks_passed",
        "precision_decimal_digits": mp.mp.dps,
        "rigorous_interval_certificate": False,
        "rh_proved": False,
        "modes": [check_mode(re, im, 1024) for re, im in
                  [("0.5", "1"), ("0.25", "1"), ("0.75", "1"), ("0.5", "14")]],
        "interpretation": "Small eigenvector residual alone does not make the off-critical symmetry defect vanish.",
    }
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(f"4 modes passed coefficient, mass-tail and paired-residual checks; saved {args.output}")


if __name__ == "__main__":
    main()
