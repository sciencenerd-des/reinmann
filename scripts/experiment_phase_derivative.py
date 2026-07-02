import mpmath

# Set high precision for evaluations (e.g. 50 decimal digits)
mpmath.mp.dps = 50

def evaluate_phase_derivative(gamma, steps=100):
    print(f"\n--- Evaluating height gamma = {gamma} ---")
    
    # We evaluate from sigma = 0.01 to 0.99 to avoid poles/boundary effects
    sigmas = [0.01 + 0.98 * i / (steps - 1) for i in range(steps)]
    
    values = []
    strictly_negative = True
    
    for sigma in sigmas:
        s = mpmath.mpc(sigma, gamma)
        # Evaluate zeta(s) and zeta'(s)
        z = mpmath.zeta(s)
        zp = mpmath.diff(mpmath.zeta, s)
        
        # Logarithmic derivative zeta'/zeta
        log_deriv = zp / z
        
        # Phase derivative theta' is the imaginary part
        theta_prime = mpmath.im(log_deriv)
        values.append(theta_prime)
        
        if theta_prime >= 0:
            strictly_negative = False
            
    min_val = min(values)
    max_val = max(values)
    avg_val = sum(values) / len(values)
    
    print(f"Min theta'  = {min_val}")
    print(f"Max theta'  = {max_val}")
    print(f"Avg theta'  = {avg_val}")
    print(f"Strictly negative: {strictly_negative}")
    
    return strictly_negative

if __name__ == "__main__":
    # Test heights:
    # 1. gamma = 14.134725... (first zero)
    # 2. gamma = 21.022039... (second zero)
    # 3. gamma = 10.0 (no zero height)
    # 4. gamma = 15.0 (between zeros)
    heights = [14.13472514173469379045725, 21.02203963877155499262847, 10.0, 15.0]
    
    all_negative = True
    for h in heights:
        neg = evaluate_phase_derivative(h)
        if not neg:
            all_negative = False
            
    print("\n=================================")
    print(f"All tested heights strictly negative: {all_negative}")
    print("=================================")
