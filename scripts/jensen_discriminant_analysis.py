import mpmath as mp
import math

# Set precision
mp.mp.dps = 80

def xi(s):
    return (s * (s - 1) / 2) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)

def get_xi_coefficients(N):
    f = lambda t: xi(mp.mpf("0.5") + 1j * t)
    coeffs = mp.taylor(f, 0, 2 * N + 1)
    b = [coeffs[2 * n].real for n in range(N + 1)]
    return b

def compute_discriminant_d2(b, n):
    """Quarter-discriminant for gamma_n = n! b_n (signed convention)."""
    gamma = [mp.factorial(n + k) * b[n + k] for k in range(3)]
    return gamma[1]**2 - gamma[0]*gamma[2]


def run_jensen_analysis():
    b = get_xi_coefficients(12)
    with open("research/JENSEN_DISCRIMINANT_LOG.md", "w") as f:
        f.write("# Classical Jensen quadratic diagnostics\n\n")
        f.write("gamma_n = n! b_n; J = gamma_n + 2 gamma_(n+1) X + gamma_(n+2) X^2. "
                "Values use uncertified numerical coefficients. Only quadratics are tested; "
                "discriminant positivity alone does not test hyperbolicity at arbitrary degree.\n\n")
        f.write("| Offset | Discriminant / 4 | Numerical sign |\n|---|---|---|\n")
        for n in range(len(b) - 2):
            delta = compute_discriminant_d2(b, n)
            sign = "positive" if delta > 0 else "negative" if delta < 0 else "zero"
            f.write(f"| {n} | {mp.nstr(delta, 15)} | {sign} |\n")


if __name__ == "__main__":
    run_jensen_analysis()
