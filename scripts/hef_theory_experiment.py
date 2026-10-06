import mpmath as mp
import math

# Set precision
mp.mp.dps = 100

def xi(s):
    return (s * (s - 1) / 2) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)

def get_xi_coefficients(N):
    f = lambda t: xi(mp.mpf("0.5") + 1j * t)
    coeffs = mp.taylor(f, 0, 2 * N + 1)
    b = [coeffs[2 * n].real for n in range(N + 1)]
    return b

def compute_deformed_coefficients(b0, t, max_k=5):
    # Truncated backward heat series exp(-t d_x^2) on sum b_m x^(2m).
    # Exact coefficients obey b_m' = -(2m+2)(2m+1) b_(m+1).
    # No infinite-tail error bound is supplied by this diagnostic.
    if max_k < 0 or max_k >= len(b0):
        raise ValueError("max_k must be within coefficient range")
    N = len(b0)
    bt = []
    for m in range(N - max_k):
        val = mp.mpf(0.0)
        for k in range(max_k + 1):
            coef_term = mp.factorial(2 * (m + k)) / mp.factorial(2 * m) * b0[m + k]
            val += ((-t) ** k / mp.factorial(k)) * coef_term
        bt.append(val)
    return bt

def compute_normalized_discriminant_d2(b, n):
    gamma = [mp.factorial(n + k) * b[n + k] for k in range(3)]
    delta = gamma[1]**2 - gamma[0]*gamma[2]
    denominator = abs(gamma[0] * gamma[2])
    return delta / denominator if denominator else mp.nan

def compute_entropy_d2(b_t, alpha=0.5):
    # H_2(t) = \sum_{n=0}^{N_limit} e^{-\alpha n} \log \bar{\Delta}(2, n, t)
    entropy = mp.mpf(0.0)
    # We can sum up to length - 3
    if len(b_t) < 3:
        raise ValueError("at least three coefficients required")
    limit = len(b_t) - 2
    for n in range(limit):
        norm_delta = compute_normalized_discriminant_d2(b_t, n)
        if norm_delta > 0:
            entropy += mp.exp(-alpha * n) * mp.log(norm_delta)
        else:
            # If any discriminant is negative (non-hyperbolic), entropy drops to minus infinity
            return -mp.inf
    return entropy

def run_experiment():
    print("Initializing Hyperbolic Entropic Flow (HEF) experiment...")
    
    # Get physical coefficients b_m(0)
    N = 16
    b0 = get_xi_coefficients(N)
    
    # Times to test: backward flow (t = -0.01), neutral (t = 0), forward flow (t = 0.01)
    times = [-0.01, -0.005, 0.0, 0.005, 0.01]
    entropy_values = []
    
    alpha = 0.5
    
    print("\nEvaluating Entropy H_2(t) for different flow times:")
    for t in times:
        # Compute deformed coefficients for time t (using max_k=4)
        bt = compute_deformed_coefficients(b0, t, max_k=4)
        
        # Calculate H_2(t)
        entropy = compute_entropy_d2(bt, alpha)
        entropy_values.append((t, entropy))
        print(f"  t = {t:+.3f} -> Entropy H_2(t) = {float(entropy):.8f}")
        
    # Verify Monotonicity
    is_monotonic = all(entropy_values[i][1] < entropy_values[i+1][1] for i in range(len(entropy_values)-1))
    print(f"\nStrict increase on the sampled times? {is_monotonic}")
    
    with open("research/HEF_THEORY_VERIFICATION_LOG.md", "w") as f:
        f.write("# Truncated backward heat coefficient diagnostic\n\n")
        f.write("Uses exp(-t d_x^2): b_m prime = -(2m+2)(2m+1)b_(m+1). "
                "The finite Taylor-in-time series has no certified infinite-tail error bound. "
                "The log-margin uses gamma_n=n!b_n and only degree two. "
                "No entropy monotonicity theorem or RH conclusion follows.\n\n")
        f.write("| Time | Log-margin sum | Next finite-difference slope |\n|---|---|---|\n")
        for i, (t, entropy) in enumerate(entropy_values):
            slope = "N/A"
            if i + 1 < len(entropy_values):
                tn, en = entropy_values[i + 1]
                slope = mp.nstr((en - entropy) / (tn - t), 12)
            f.write(f"| {t} | {mp.nstr(entropy, 12)} | {slope} |\n")
        f.write(f"\nStrict increase on sampled times: {is_monotonic}.\n")


if __name__ == "__main__":
    run_experiment()
