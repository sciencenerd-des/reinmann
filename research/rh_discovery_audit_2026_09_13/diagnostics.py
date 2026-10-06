"""Reproduce bounded audit diagnostics without regenerating existing reports.

Exact Fraction results concern stored decimal midpoints, not certified Xi values.
Run from any directory with Python and the already available mpmath package.
"""
from fractions import Fraction
from hashlib import sha256
import importlib.util
import json
from math import factorial, log
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]


def load_script(name):
    path = ROOT / "scripts" / f"{name}.py"
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def exact_determinant(matrix):
    matrix = [row[:] for row in matrix]
    result = Fraction(1)
    for col in range(len(matrix)):
        pivot = next((row for row in range(col, len(matrix)) if matrix[row][col]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != col:
            matrix[col], matrix[pivot] = matrix[pivot], matrix[col]
            result = -result
        value = matrix[col][col]
        result *= value
        for row in range(col + 1, len(matrix)):
            ratio = matrix[row][col] / value
            for k in range(col + 1, len(matrix)):
                matrix[row][k] -= ratio * matrix[col][k]
    return result


def main():
    cache = ROOT / "research/figures/coeffs_M120.txt"
    raw = cache.read_bytes()
    signed = [Fraction(s) for s in raw.decode().splitlines()[1:] if s.strip()]
    mu = [(-1) ** n * value for n, value in enumerate(signed)]
    assert len(mu) >= 5 and all(value > 0 for value in mu)
    ratios = [b / a for a, b in zip(mu, mu[1:])]
    q = [mu[n] * mu[n + 2] / mu[n + 1] ** 2 for n in range(len(mu) - 2)]
    delta = [1 - value for value in q]
    assert all(0 < value < 1 for value in q)
    windows = []
    for n in range(len(mu) - 4):
        a, b, c, d, e = mu[n:n + 5]
        determinant = c ** 3 - 2*b*c*d + b*b*e + a*d*d - a*c*e
        direct = determinant / c ** 3
        deficit = delta[n + 1] ** 2 - q[n + 1] ** 2 * delta[n] * delta[n + 2]
        assert direct == deficit
        curvature = log(float(delta[n] * delta[n + 2] / delta[n + 1] ** 2))
        budget = -2 * log(float(q[n + 1]))
        windows.append({
            "offset": n,
            "normalized_determinant_approx": float(direct),
            "relative_safety_approx": float(direct / delta[n + 1] ** 2),
            "curvature_budget_ratio_approx": curvature / budget,
            "positive_midpoint": direct > 0,
        })

    quartic = load_script("uniformity_gap_experiment")
    quartic_disc = quartic.compute_jensen_discriminant([1, 0, 0, 0, 1])
    assert abs(quartic_disc - 256) < quartic.mp.mpf("1e-50")

    heat = load_script("de_bruijn_newman_simulation")
    history = heat.simulate_flow(heat.get_zeta_zeros(10), 0.01, 20, True)
    energies = [item["energy"] for item in history]
    hef = load_script("hef_theory_experiment")
    hef_derivative = hef.mp.diff(
        lambda t: hef.compute_deformed_coefficients([1, 2, 3, 4], t, max_k=1)[0], 0
    )
    assert hef_derivative == -4

    # Positive cosine-transform measure and even symmetry do not force real zeros.
    # 3*cos(t)+cos(2*t) has signed Taylor magnitudes (3+4^n)/(2n)!.
    toy_mu = [Fraction(3 + 4 ** n, factorial(2 * n)) for n in range(32)]
    toy_scan = []
    for rank in range(1, 7):
        negatives = []
        for shift in range(25):
            matrix = [[toy_mu[shift + i - j] if shift + i >= j else Fraction(0)
                       for j in range(rank)] for i in range(rank)]
            value = exact_determinant(matrix)
            if value < 0:
                negatives.append({"shift": shift, "determinant": str(value)})
        toy_scan.append({"rank": rank, "shifts_tested": 25, "negative_minors": negatives})
    assert all(not item["negative_minors"] for item in toy_scan[:5])
    assert toy_scan[5]["negative_minors"][0] == {
        "shift": 2, "determinant": "-26968264743653/74568823160832000"
    }

    result = {
        "repair_state": "Post-interface-repair replay; original diagnostics.json is historical",
        "scope": "Exact stored-midpoint algebra plus bounded floating-point diagnostics; not Xi enclosures or RH evidence",
        "input_sha256": sha256(raw).hexdigest(),
        "coefficient_count": len(mu),
        "exact_deficit_identity_windows": len(windows),
        "positive_midpoint_windows": sum(w["positive_midpoint"] for w in windows),
        "strictly_decreasing_cached_ratio_steps": sum(y < x for x, y in zip(ratios, ratios[1:])),
        "first_four_ratios_approx": [float(x) for x in ratios[:4]],
        "first_window": windows[0],
        "last_window": windows[-1],
        "quartic_control": {"polynomial": "X^4+1", "computed_discriminant": float(quartic_disc), "real_root_count_exact": 0},
        "heat_diagnostic": {"initial_energy": energies[0], "final_energy": energies[-1], "increasing_steps": sum(y > x for x, y in zip(energies, energies[1:])), "steps": 20},
        "hef_control": {"coefficients": [1, 2, 3, 4], "derivative_first_coefficient_at_zero": float(hef_derivative)},
        "positive_kernel_nonreal_zero_control": {
            "function": "3*cos(t)+cos(2*t)",
            "reason_nonreal_zeros": "cos(t)=(-3-sqrt(17))/4 < -1",
            "scan": toy_scan,
            "boundary": "Finite scan only: no claim of global PF5. Atomic positive measure, not the Xi theta kernel.",
        },
        "jensen_normalization_control": {
            "ordinary_generating_polynomial": "1+2z+2z^2",
            "degree_3_uncorrected_jensen": "1+6X+6X^2",
            "uncorrected_discriminant": 12,
            "degree_3_corrected_jensen": "1+6X+12X^2",
            "corrected_discriminant": -12,
        },
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
