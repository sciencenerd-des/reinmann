import mpmath
import math

# Set precision
mpmath.mp.dps = 30

def get_zeta_zeros(n):
    # Fetch first n non-trivial zeros
    return [mpmath.zetazero(k) for k in range(1, n + 1)]

def flow_derivatives(zeros):
    # Finite rational-force toy equations:
    # d(rho_k)/dt = \sum_{j \ne k} 2 / (rho_k - rho_j)
    # Plus conjugate zeros to maintain symmetry:
    # Each zero has a conjugate zero \bar{rho}_j.
    # Total zeros = {rho_j} U {\bar{rho}_j}
    derivs = []
    num = len(zeros)
    
    # We include conjugates to make it a self-consistent symmetric system
    all_zeros = zeros + [mpmath.conj(z) for z in zeros]
    
    for k in range(num):
        rho_k = zeros[k]
        d_rho = mpmath.mpc(0.0)
        
        # Sum over all other zeros in the system
        for j, rho_j in enumerate(all_zeros):
            # Exclude self-interaction (k == j)
            if j == k:
                continue
            d_rho += 2.0 / (rho_k - rho_j)
            
        derivs.append(d_rho)
    return derivs

def simulate_flow(zeros, dt, steps, perturbed=False):
    # Finite rational-force toy in the s-plane, not a validated Xi heat flow.
    if steps < 0 or not mpmath.isfinite(dt):
        raise ValueError("invalid integration parameters")
    zeros = list(zeros)
    if perturbed and zeros:
        first = zeros[0]
        # Replace the first point with a mirror pair; conjugates are added below.
        zeros = [mpmath.mpc("0.51", mpmath.im(first)),
                 mpmath.mpc("0.49", mpmath.im(first))] + zeros[1:]

    history = []
    current = list(zeros)
    
    for step in range(steps + 1):
        # Calculate energy: E = sum (beta_k - 0.5)^2
        energy = sum((mpmath.re(z) - 0.5)**2 for z in current)
        history.append({
            'step': step,
            't': step * dt,
            'energy': float(energy),
            'zeros': [(float(mpmath.re(z)), float(mpmath.im(z))) for z in current]
        })
        
        if step < steps:
            # Simple Euler step for particle dynamics
            derivs = flow_derivatives(current)
            current = [current[i] + derivs[i] * dt for i in range(len(current))]
            
    return history

def run_experiment():
    print("Initializing De Bruijn-Newman particle flow simulation...")
    
    # Let's take the first 10 zeros
    num_zeros = 10
    raw_zeros = get_zeta_zeros(num_zeros)
    
    # Test 1: Flow with unperturbed zeros (on the critical line, Re = 0.5)
    print("Testing flow of unperturbed zeros (on the critical line)...")
    history_unperturbed = simulate_flow(raw_zeros, dt=0.01, steps=20, perturbed=False)
    
    # Test 2: Flow with perturbed zeros (one zero pushed slightly off-line)
    print("Testing flow of perturbed zeros (mirror pair perturbed off-line)...")
    history_perturbed = simulate_flow(raw_zeros, dt=0.01, steps=20, perturbed=True)
    
    # Write analysis log
    with open("research/DE_BRUIJN_NEWMAN_FLOW_LOG.md", "w") as f:
        f.write("# Finite Rational-Force Particle Toy\n\n")
        f.write("Finite s-plane rational-force toy with Euler integration, conjugate points "
                "and mirror-paired perturbations. This is not a certified approximation "
                "to the infinite de Bruijn-Newman deformation.\n\n")
        f.write("## 1. Unperturbed Flow (Starting on the Critical Line)\n\n")
        f.write("| Step | Time $t$ | Energy $E(t)$ | Zeros real parts (first 3) |\n")
        f.write("|---|---|---|---|\n")
        for h in history_unperturbed[::5]:
            reals_str = ", ".join(f"{z[0]:.6f}" for z in h['zeros'][:3])
            f.write(f"| {h['step']} | {h['t']:.2f} | {h['energy']:.6e} | {reals_str} |\n")
            
        f.write("\n## 2. Perturbed Flow (Mirror pair at 0.49 and $\\sigma = 0.51$)\n\n")
        f.write("| Step | Time $t$ | Energy $E(t)$ | $dE/dt$ (approx) | Zeros real parts (first 3) |\n")
        f.write("|---|---|---|---|---|\n")
        for idx in range(len(history_perturbed)):
            if idx % 4 == 0 or idx == len(history_perturbed) - 1:
                h = history_perturbed[idx]
                h_next = history_perturbed[idx+1] if idx < len(history_perturbed) - 1 else None
                dedt = (h_next['energy'] - h['energy']) / 0.01 if h_next else 0.0
                reals_str = ", ".join(f"{z[0]:.6f}" for z in h['zeros'][:3])
                f.write(f"| {h['step']} | {h['t']:.2f} | {h['energy']:.6e} | {dedt:.6e} | {reals_str} |\n")
                
        f.write("\n## 3. Findings\n\n")
        energies = [h["energy"] for h in history_perturbed]
        decreases = all(a > b for a, b in zip(energies, energies[1:]))
        increases = all(a < b for a, b in zip(energies, energies[1:]))
        f.write(f"Sampled perturbed energy strictly decreases: {decreases}.\n\n")
        f.write(f"Sampled perturbed energy strictly increases: {increases}.\n\n")
        f.write("These finite toy dynamics imply no attractor, Lyapunov theorem, "
                "Newman-constant bound, or statement about RH.\n")

    print("Log written to research/DE_BRUIJN_NEWMAN_FLOW_LOG.md")

if __name__ == "__main__":
    run_experiment()
