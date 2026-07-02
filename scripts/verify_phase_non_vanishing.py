import mpmath

# Set high precision
mpmath.mp.dps = 50

def run_phase_experiment(num_zeros=50):
    print(f"Starting experiment on the first {num_zeros} non-trivial zeros...")
    
    # 1. Fetch zero heights
    zeros = [mpmath.zetazero(k) for k in range(1, num_zeros + 1)]
    heights = [mpmath.im(z) for z in zeros]
    
    # Sigmas to evaluate (excluding 0.5 to avoid the pole at the actual critical-line zeros)
    sigmas = [0.05, 0.1, 0.2, 0.3, 0.4, 0.6, 0.7, 0.8, 0.9, 0.95]
    
    zero_heights_constant_sign = 0
    midpoint_heights_constant_sign = 0
    
    positive_zeros = 0
    negative_zeros = 0
    
    print("\n--- Phase Derivative at Zero Heights ---")
    for k, gamma in enumerate(heights):
        values = []
        for sigma in sigmas:
            s = mpmath.mpc(sigma, gamma)
            z = mpmath.zeta(s)
            zp = mpmath.diff(mpmath.zeta, s)
            theta_prime = mpmath.im(zp / z)
            values.append(theta_prime)
            
        all_pos = all(v > 0 for v in values)
        all_neg = all(v < 0 for v in values)
        constant = all_pos or all_neg
        
        if constant:
            zero_heights_constant_sign += 1
            if all_pos:
                positive_zeros += 1
            else:
                negative_zeros += 1
                
        # Print first few and summary stats
        if k < 5 or k == num_zeros - 1:
            sign_str = "Strictly Positive" if all_pos else ("Strictly Negative" if all_neg else "Changes Sign")
            print(f"Zero #{k+1} (gamma = {float(gamma):.6f}): {sign_str} (min_abs = {float(min(abs(v) for v in values)):.6f})")
            
    print("\n--- Phase Derivative at Midpoint Heights ---")
    for k in range(len(heights) - 1):
        gamma_mid = (heights[k] + heights[k+1]) / 2
        values = []
        for sigma in sigmas:
            s = mpmath.mpc(sigma, gamma_mid)
            z = mpmath.zeta(s)
            zp = mpmath.diff(mpmath.zeta, s)
            theta_prime = mpmath.im(zp / z)
            values.append(theta_prime)
            
        all_pos = all(v > 0 for v in values)
        all_neg = all(v < 0 for v in values)
        constant = all_pos or all_neg
        
        if constant:
            midpoint_heights_constant_sign += 1
            
        if k < 5 or k == len(heights) - 2:
            sign_str = "Strictly Positive" if all_pos else ("Strictly Negative" if all_neg else "Changes Sign")
            print(f"Midpoint #{k+1} (gamma = {float(gamma_mid):.6f}): {sign_str} (min_abs = {float(min(abs(v) for v in values)):.6f})")
            
    print("\n================ SUMMARY STATS ================")
    print(f"Total zeros tested: {num_zeros}")
    print(f"Zeros with constant phase derivative sign: {zero_heights_constant_sign} / {num_zeros} ({zero_heights_constant_sign/num_zeros*100:.1f}%)")
    print(f"  -> Strictly Positive: {positive_zeros}")
    print(f"  -> Strictly Negative: {negative_zeros}")
    print(f"Midpoints with constant phase derivative sign: {midpoint_heights_constant_sign} / {num_zeros-1} ({midpoint_heights_constant_sign/(num_zeros-1)*100:.1f}%)")
    print("===============================================")
    
if __name__ == "__main__":
    run_phase_experiment(200)
