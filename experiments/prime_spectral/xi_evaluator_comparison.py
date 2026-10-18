"""Compare explicit Arb Mellin Taylor models and Euler--Maclaurin/Stirling jets.

All coefficients are ordinary coefficients, through degree 16 in s. Explicit
analytic remainders are evaluated in Arb. This is not a Lean certificate. The
builtin Gamma/zeta series are used only as an independent comparison reference.
"""
import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import statistics
import time

from flint import acb, acb_series, arb, ctx


DEGREE = 16
CENTRE = acb(arb("1/2"), 14)


def ball(value, error):
    return acb(arb(value.real, error), arb(value.imag, error))


def reference():
    s = acb_series([CENTRE, 1])
    return s * (s / 2).gamma() * (-s * arb.pi().log() / 2).exp() * (s - 1) * s.zeta() / 2


def prefactor(s):
    return s * (s - 1) * (-s * arb.pi().log() / 2).exp() / 2


def mellin(degree, relative_half_width, theta_terms=3, endpoint=12):
    """Exact polynomial integration, with a Cauchy remainder on each t-disk.

    At c=.5+14i the j-th normalized s coefficient of the integrand is
    psi(t)*(log(t)/2)^j/j!*(t^(-.75+7i)+(-1)^j*t^(-.75-7i)).
    The t-disk radius is c_panel/2; h/c_panel is relative_half_width.
    """
    start = time.monotonic()
    saved_cap = ctx.cap
    ctx.cap = degree + 1
    integral = [acb(0) for _ in range(DEGREE + 1)]
    errors = [arb(0) for _ in range(DEGREE + 1)]
    left = Fraction(1)
    panels = 0
    alpha = Fraction(relative_half_width)
    while left < endpoint:
        right = min(Fraction(endpoint), left * (1 + alpha) / (1 - alpha))
        centre = arb(str((left + right) / 2))
        half = arb(str((right - left) / 2))
        radius = centre / 2
        t = acb_series([acb(centre), 1])
        logt = t.log()
        psi = sum(((-arb.pi() * n * n * t).exp() for n in range(1, theta_terms + 1)), acb_series([0]))
        plus = (acb(arb("-3/4"), 7) * logt).exp()
        minus = (acb(arb("-3/4"), -7) * logt).exp()
        weight = acb_series([1])
        # A bound on the whole complex t-disk, not on point samples.
        x = centre - radius
        angle = arb("1/2").asin()
        max_log = max(abs(x.log()).upper(), abs((centre + radius).log()).upper())
        log_norm = (arb(max_log) ** 2 + angle ** 2).sqrt()
        psi_bound = sum(((-arb.pi() * n * n * x).exp() for n in range(1, theta_terms + 1)), arb(0))
        base_bound = 2 * psi_bound * x ** arb("-3/4") * (7 * angle).exp()
        quotient = half / radius
        remainder_factor = 2 * half * quotient ** (degree + 1) / ((degree + 2) * (1 - quotient))
        for j in range(DEGREE + 1):
            model = psi * (plus + (-1) ** j * minus) * weight
            integral[j] += sum((model[k] * 2 * half ** (k + 1) / (k + 1)
                                for k in range(0, degree + 1, 2)), acb(0))
            errors[j] += base_bound * (log_norm / 2) ** j / math.factorial(j) * remainder_factor
            weight = weight * logt / (2 * (j + 1))
        panels += 1
        left = right
    # Uniform in |s-CENTRE|<=1: both powers have real exponent <= -1/4.
    # Cauchy on that s-disk bounds every normalized coefficient by the same error.
    tail = 2 * (-arb.pi() * endpoint).exp() / (arb.pi() * (1 - (-3 * arb.pi()).exp()))
    n = theta_terms + 1
    theta_tail = 2 * (-arb.pi() * n * n).exp() / (arb.pi() * n * n * (1 - (-arb.pi() * (2*n+1)).exp()))
    ctx.cap = saved_cap
    bounded = acb_series([ball(value, errors[j] + tail + theta_tail) for j, value in enumerate(integral)])
    s = acb_series([CENTRE, 1])
    result = s * (s - 1) * bounded / 2 + acb_series([arb("1/2")])
    return result, {
        "method": "Mellin_Taylor_model", "panel_degree": degree,
        "relative_half_width": str(alpha), "panels": panels, "theta_terms": theta_terms,
        "integration_endpoint": endpoint, "seconds": time.monotonic() - start,
        "integral_coefficient_error_bounds": [str(e.upper()) for e in errors],
        "uniform_tail_bound": str(tail.upper()), "uniform_theta_tail_bound": str(theta_tail.upper()),
        "point_jet_series_exp_log_calls": panels * (theta_terms + 3),
        "series_model_length": degree + 1,
        "operation_scope": "exp/log model calls plus degree-k model arithmetic per panel; not a measured Lean operation count"}


def zeta_em(s, terms, corrections):
    N = terms + 1
    logN = arb(N).log()
    n_power = (-s * logN).exp()
    value = sum(((-s * arb(n).log()).exp() for n in range(1, N)), acb_series([0]))
    value += n_power * N / (s - 1) + n_power / 2
    rising = acb_series([1])
    for k in range(1, 2 * corrections):
        rising *= s + k - 1
        if k % 2 == 1:
            value += arb.bernoulli(k+1) / math.factorial(k+1) * rising * n_power / N ** k
    return value


def zeta_error(terms, corrections):
    # Periodic Bernoulli Fourier bound; uniform on the unit s-disk.
    N = terms + 1
    sigma = arb("-1/2")
    rising_bound = math.prod(abs(CENTRE + j).upper() + 1 for j in range(2 * corrections))
    bernoulli_bound = 2 * (1 + arb(1) / (2 * corrections - 1)) / (2 * arb.pi()) ** (2 * corrections)
    return bernoulli_bound * rising_bound * arb(N) ** (1 - sigma - 2 * corrections) / (sigma + 2 * corrections - 1)


def gamma_stirling(s, shift, corrections):
    z = s / 2 + shift
    logg = (z - arb("1/2")) * z.log() - z + (2 * arb.pi()).log() / 2
    for k in range(1, corrections):
        logg += arb.bernoulli(2*k) / (2*k*(2*k-1)) * (1/z) ** (2*k-1)
    inverse_factors = math.prod(1/(s / 2 + j) for j in range(shift))
    return logg.exp() * inverse_factors


def gamma_error(shift, corrections):
    # DLMF 5.11(ii): sec(arg(z)/2)^(2m) times the first omitted term.
    # Re(z)>0 throughout the disk, so the secant factor is <=2^m.
    lower = abs(CENTRE / 2 + shift).lower() - arb("1/2")
    log_error = abs(arb.bernoulli(2*corrections)) * 2**corrections / (2*corrections*(2*corrections-1)*lower**(2*corrections-1))
    square = acb(arb("1/2", 1), arb(14, 1))
    upper = abs(gamma_stirling(acb_series([square]), shift, corrections)[0]).upper()
    return arb(upper) * log_error.expm1(), log_error, upper


def em_stirling(terms, zeta_corrections, shift, gamma_corrections):
    start = time.monotonic()
    s = acb_series([CENTRE, 1])
    zet = zeta_em(s, terms, zeta_corrections)
    gam = gamma_stirling(s, shift, gamma_corrections)
    ze = zeta_error(terms, zeta_corrections)
    ge, le, gu = gamma_error(shift, gamma_corrections)
    zet = acb_series([ball(zet[j], ze) for j in range(DEGREE+1)])
    gam = acb_series([ball(gam[j], ge) for j in range(DEGREE+1)])
    result = prefactor(s) * gam * zet
    return result, {
        "method": "Euler_Maclaurin_and_shifted_Stirling", "terms": terms,
        "zeta_corrections": zeta_corrections, "gamma_shift": shift,
        "gamma_corrections_including_omitted": gamma_corrections,
        "zeta_uniform_error": str(ze.upper()), "gamma_uniform_error": str(ge.upper()),
        "loggamma_uniform_error": str(le.upper()), "gamma_approx_square_upper": str(gu),
        "seconds": time.monotonic() - start,
        "point_jet_series_exp_log_calls": terms + 4,
        "point_jet_scalar_log_calls_before_constant_folding": terms + 3,
        "series_model_length": DEGREE + 1,
        "operation_scope": "finite exp/log models, Bernoulli corrections and shift product; not a measured Lean operation count"}


def describe(jet, row, truth):
    radii = [max(jet[j].real.rad().upper(), jet[j].imag.rad().upper()) for j in range(DEGREE+1)]
    complex_radii = [(jet[j].real.rad()**2+jet[j].imag.rad()**2).sqrt().upper()
                     for j in range(DEGREE+1)]
    row.update({"ordinary_jet": [str(jet[j]) for j in range(DEGREE+1)],
                "all_17_overlap_builtin_reference": all(jet[j].overlaps(truth[j]) for j in range(DEGREE+1)),
                "all_17_component_radii_below_1e_8": all(r < arb("1e-8") for r in radii),
                "all_17_complex_radii_below_1e_8": all(r < arb("1e-8") for r in complex_radii),
                "maximum_complex_radius": str(max(complex_radii)),
                "maximum_component_radius": str(max(radii)), "centre_component_radius": str(radii[0])})
    if not row["all_17_overlap_builtin_reference"]:
        raise RuntimeError("Independent reference disagrees with an explicit evaluator")
    return row


def hard_tile():
    """Complete external tile using the selected finite evaluator and Cauchy tail.

    The majorant 1000 is the proved coarse unit-circle bound from XiLocalCauchy.
    Keeping this bound isolates evaluator costs from a numerical majorant search.
    The certificate here still depends on externally justified EM/Stirling errors.
    """
    start = time.monotonic()
    jet, evaluator = em_stirling(10, 8, 12, 8)
    radius = arb("1/16")
    majorant = arb(1000)
    derivative = sum((j*abs(jet[j])*radius**(j-1) for j in range(1, DEGREE+1)), arb(0))
    derivative += majorant*radius**DEGREE*(DEGREE+1-DEGREE*radius)/(1-radius)**2
    margin = abs(jet[0]).lower()-derivative.upper()*radius
    if not margin > 0:
        raise RuntimeError("Explicit hard tile failed")
    return {"status": "external_complete_hard_tile", "centre": ["1/2", "14"],
            "radius": "1/16", "jet_degree": DEGREE, "unit_circle_majorant": 1000,
            "majorant_reference": "Reinmann.XiLocalCauchy.unit_circle_bound",
            "centre_modulus_lower": str(abs(jet[0]).lower()),
            "derivative_upper": str(derivative.upper()), "margin_lower": str(margin.lower()),
            "seconds": time.monotonic()-start, "evaluator_seconds": evaluator["seconds"],
            "Lean_complete_hard_tile_certified": False,
            "scope": "Full external local nonvanishing calculation, with explicit uniform EM/Stirling error bounds. Lean does not yet prove those remainders or the actual evaluator bridge."}


def run(output, repeats):
    ctx.prec = 192
    ctx.cap = DEGREE + 1
    truth = reference()
    rows = []
    for degree in [8, 12, 16]:
        timings = []
        for _ in range(repeats):
            jet, row = mellin(degree, "1/16")
            timings.append(row["seconds"])
        row["seconds"] = statistics.median(timings)
        row["timings_seconds"] = timings
        rows.append(describe(jet, row, truth))
        print(row["method"], degree, row["seconds"], row["maximum_component_radius"], flush=True)
    for corrections in [4, 6, 8]:
        timings = []
        for _ in range(repeats):
            jet, row = em_stirling(10, corrections, 12, 8)
            timings.append(row["seconds"])
        row["seconds"] = statistics.median(timings)
        row["timings_seconds"] = timings
        rows.append(describe(jet, row, truth))
        print(row["method"], corrections, row["seconds"], row["maximum_component_radius"], flush=True)
    tile_timings = []
    for _ in range(repeats):
        tile = hard_tile()
        tile_timings.append(tile["seconds"])
    tile["seconds"] = statistics.median(tile_timings)
    tile["timings_seconds"] = tile_timings
    result = {"status": "explicit_Arb_evaluator_comparison", "centre": ["1/2", "14"],
              "bits": ctx.prec, "jet_degree": DEGREE, "component_absolute_radius_target": "1e-8",
              "complex_absolute_radius_target": "1e-8",
              "timing_repeats": repeats, "timing_statistic": "median",
              "rows": rows, "selected_external_hard_tile": tile,
              "Lean_complete_hard_tile_certified": False,
              "sources": ["https://dlmf.nist.gov/5.11#ii", "https://arxiv.org/abs/1309.2877"],
              "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "scope": "Explicit external analytic error bounds and Arb arithmetic. No formal Euler--Maclaurin/Stirling remainder, Lean hard tile, or rectangle is asserted."}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--repeats", type=int, default=7)
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("repeats must be positive")
    run(args.output, args.repeats)
