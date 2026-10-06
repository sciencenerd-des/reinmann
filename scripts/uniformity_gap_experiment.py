import mpmath as mp
import math

# High precision
mp.mp.dps = 100

def xi(s):
    return (s * (s - 1) / 2) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)

def get_xi_coefficients(N):
    f = lambda t: xi(mp.mpf("0.5") + 1j * t)
    coeffs = mp.taylor(f, 0, 2 * N + 1)
    b = [coeffs[2 * n].real for n in range(N + 1)]
    return b

def compute_jensen_discriminant(cef):
    # cef is list of coefficients of the polynomial from low to high degree
    # J(X) = \sum_{k=0}^d cef[k] X^k
    # We use mpmath's polyroots to find the roots and calculate the product of squared differences of roots:
    # Disc = a_d^{2d-2} \prod_{i < j} (r_i - r_j)^2
    d = len(cef) - 1
    cef_hl = list(reversed(cef))
    try:
        roots = mp.polyroots(cef_hl, maxsteps=300, extraprec=300)
    except Exception as e:
        return None
    
    # Calculate discriminant
    disc = mp.mpf(1.0)
    for i in range(d):
        for j in range(i + 1, d):
            diff = roots[i] - roots[j]
            disc *= diff ** 2
            
    # Multiply by lead coefficient term
    lead_coef = cef_hl[0]
    disc *= lead_coef ** (2 * d - 2)
    return disc.real

def classical_jensen_coefficients(b, n, d):
    """Weight ordinary coefficients by n!. Signed b gives the reflected polynomial."""
    if n < 0 or d < 0 or n + d >= len(b):
        raise ValueError("Jensen offset/degree outside coefficient range")
    return [mp.binomial(d, k) * mp.factorial(n + k) * b[n + k]
            for k in range(d + 1)]


def numerical_root_status(coefficients, tolerance=None):
    """Floating root diagnostic, never a certified hyperbolicity decision."""
    tolerance = mp.mpf("1e-30") if tolerance is None else mp.mpf(tolerance)
    if tolerance <= 0:
        raise ValueError("tolerance must be positive")
    coefficients = list(coefficients)
    if not coefficients or not all(mp.isfinite(c) for c in coefficients):
        return {"status": "inconclusive", "max_relative_imaginary": None}
    while coefficients and coefficients[-1] == 0:
        coefficients.pop()
    if len(coefficients) <= 1:
        return {"status": "degenerate", "max_relative_imaginary": None}
    try:
        roots = mp.polyroots(list(reversed(coefficients)), maxsteps=300, extraprec=300)
    except (ValueError, ZeroDivisionError, mp.libmp.libhyper.NoConvergence):
        return {"status": "inconclusive", "max_relative_imaginary": None}
    if not all(mp.isfinite(r) for r in roots):
        return {"status": "inconclusive", "max_relative_imaginary": None}
    worst = max(abs(mp.im(r)) / max(1, abs(r)) for r in roots)
    return {"status": "numerically real" if worst <= tolerance else "numerically nonreal",
            "max_relative_imaginary": mp.nstr(worst, 12)}


def run_experiment():
    N = 14
    b = get_xi_coefficients(N)
    rows = []
    for d in (2, 3, 4):
        for n in range(N - d + 1):
            coefficients = classical_jensen_coefficients(b, n, d)
            diagnostic = numerical_root_status(coefficients)
            disc = compute_jensen_discriminant(coefficients)
            rows.append((d, n, "inconclusive" if disc is None else mp.nstr(disc, 12),
                         diagnostic["status"], diagnostic["max_relative_imaginary"]))
    with open("research/UNIFORMITY_GAP_SURFACE_LOG.md", "w") as f:
        f.write("# Finite Jensen root diagnostics\n\n")
        f.write("Uses gamma_n = n! b_n and uncertified numerical Xi coefficients. "
                "Positive discriminants do not classify real-rootedness in degree four or above. "
                "Root tolerances and solver convergence are numerical diagnostics only; "
                "these finite samples establish no uniformity boundary or RH claim.\n\n")
        f.write("| Degree | Offset | Discriminant | Root diagnostic | Max relative imaginary part |\n")
        f.write("|---|---|---|---|---|\n")
        for row in rows:
            f.write("| " + " | ".join(map(str, row)) + " |\n")


if __name__ == "__main__":
    run_experiment()
