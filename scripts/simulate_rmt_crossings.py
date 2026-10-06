import random
import math

def generate_wigner_spacing(mean_spacing, rng):
    # Wigner surmise for GUE: P(s) = (32/pi^2) * s^2 * exp(-4*s^2/pi)
    # We can use acceptance-rejection sampling to generate a normalized spacing s
    while True:
        s = rng.uniform(0, 5)
        # Max of P(s) occurs at s = sqrt(pi)/2 ≈ 0.886, value is P(s_max) ≈ 1.08
        p = (32.0 / (math.pi**2)) * (s**2) * math.exp(-4.0 * (s**2) / math.pi)
        if rng.uniform(0, 1.2) < p:
            return s * mean_spacing

def run_simulation(num_runs=1000, gamma=100.0, seed=0):
    if num_runs <= 0 or not math.isfinite(gamma) or gamma <= 2 * math.pi:
        raise ValueError("positive runs and gamma > 2*pi required")
    rng = random.Random(seed)
    print(f"Simulating RMT spacings for height gamma = {gamma} ({num_runs} runs)...")
    
    # Leading mean spacing at height gamma: 2*pi / log(gamma/(2*pi))
    mean_spacing = 2.0 * math.pi / math.log(gamma / (2.0 * math.pi))
    
    zero_crossings = 0
    min_theta_prime_magnitude = float('inf')
    
    sigmas = [0.1, 0.2, 0.3, 0.4, 0.6, 0.7, 0.8, 0.9]
    
    # Gamma term approximation
    digamma_approx = -0.5 * (math.log(gamma / 2.0) if gamma > 2 else 0.0)
    E_val = -0.5 * (math.pi / 2.0)  # Imaginary part of digamma is approx pi/2
    gamma_offset = -0.5 * (math.pi / 2.0)  # -pi/4 ≈ -0.785
    
    for run in range(num_runs):
        # Generate eigenvalues (zeros) below and above gamma
        # Let gamma_0 = gamma
        heights = [gamma]
        
        # Zeros above gamma
        curr = gamma
        for _ in range(50):
            curr += generate_wigner_spacing(mean_spacing, rng)
            heights.append(curr)
            
        # Zeros below gamma
        curr = gamma
        for _ in range(50):
            curr -= generate_wigner_spacing(mean_spacing, rng)
            if curr > 0:
                heights.append(curr)
                
        # Sort all heights
        heights.sort()
        k_idx = heights.index(gamma)
        
        # Check if theta' ever crosses zero for sigma
        for sigma in sigmas:
            pos_sum = 0.0
            neg_sum = 0.0
            for h in heights:
                if h > gamma:
                    term = (h - gamma) / ((sigma - 0.5)**2 + (gamma - h)**2)
                    pos_sum += term
                elif 0 < h < gamma:
                    term = (gamma - h) / ((sigma - 0.5)**2 + (gamma - h)**2)
                    neg_sum += term
                # Conjugate term contribution
                term_conj = (h + gamma) / ((sigma - 0.5)**2 + (gamma + h)**2)
                neg_sum += term_conj
                    
            theta_prime = pos_sum - neg_sum + gamma_offset
            
            if abs(theta_prime) < min_theta_prime_magnitude:
                min_theta_prime_magnitude = abs(theta_prime)
                
            # If sign of theta' changes (crosses zero), we detect a crossing
            # However, since theta' is negative at the boundaries, crossing means theta' >= 0
            if theta_prime >= 0:
                zero_crossings += 1
                break
                
    crossing_prob = zero_crossings / num_runs
    print(f"Simulation completed for gamma = {gamma}.")
    print(f"Runs with nonnegative sampled proxy: {zero_crossings} / {num_runs} ({crossing_prob*100:.3f}%)")
    print(f"Min |theta'| magnitude found: {min_theta_prime_magnitude:.6f}")
    
    return zero_crossings, min_theta_prime_magnitude

if __name__ == "__main__":
    # Test for different heights gamma to see asymptotic decay
    heights_to_test = [50.0, 100.0, 500.0, 1000.0]
    
    with open("research/RMT_SIMULATION_LOG.md", "w") as f:
        f.write("# RMT Level Repulsion & Zero-Crossing Probability Simulation\n\n")
        f.write("This document logs the statistical simulation of zero-crossings of the horizontal phase derivative $\\theta'(\\sigma)$ in an independent truncated Wigner-spacing toy.\n\n")
        f.write("## Simulation Parameters\n\n")
        f.write("* **Wigner Surmise (GUE)**: Normalized spacing distribution $P(s) = \\frac{32}{\\pi^2} s^2 e^{-4s^2/\\pi}$\n")
        f.write("* **Average Spacing**: $d = 2\\pi / \\log(\\gamma/(2\\pi))$\n")
        f.write("* **Runs per height**: 1,000\n\n")
        
        f.write("## Results\n\n")
        f.write("| Height $\\gamma$ | Mean Spacing | Zeros Crossings | Crossing Probability | Min $|\\theta'|$ |\n")
        f.write("|---|---|---|---|---|\n")
        
        # First run the simulations and store results to write them dynamically
        sim_results = []
        for g in heights_to_test:
            crossings, min_mag = run_simulation(1000, g)
            mean_space = 2.0 * math.pi / math.log(g / (2.0 * math.pi))
            sim_results.append((g, mean_space, crossings, min_mag))
            
        for g, mean_space, crossings, min_mag in sim_results:
            f.write(f"| {g} | {mean_space:.4f} | {crossings} | {crossings/1000*100:.3f}% | {min_mag:.6f} |\n")
            
        f.write("\nSeed: 0 per height. Independent spacings follow a Wigner-surmisal "
                "density truncated at s=5; this renewal process is not GUE. "
                "The reported event is a nonnegative proxy at sampled sigma values, "
                "not a verified zero crossing. No theorem about actual zeta zeros "
                "or RH follows.\n")
