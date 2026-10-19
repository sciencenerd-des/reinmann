"""Generate Reinmann/HardTileXi.lean and verify all rational inequalities."""
from fractions import Fraction as Q
from pathlib import Path
from degree8_scalar_certificates import Disk, exact, outward, lean_certificate, literal, pair, size
from degree8_model_generator import Builder, ZERO, add, scale, mul, exponential, Node


def build_hard_tile_xi(check=False):
    # Replay the exact builder from degree8_model_generator so J_gammaFinite,
    # J_emAfterCorr6, J_logpi, J_halfVariable, and J_sminusone match byte-for-byte.
    b = Builder()
    from degree8_model_generator import gamma_model, zeta_model
    g = gamma_model(b)
    z = zeta_model(b)

    logpi = next(x for x in b.nodes if x.name == 'logpi')
    half_s = next(x for x in b.nodes if x.name == 'halfVariable')
    s_minus_1 = next(x for x in b.nodes if x.name == 'sminusone')

    out = '''/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.HardTileFiniteJets
import Reinmann.ZetaJetRemainder
import Reinmann.TaylorDerivativeTail
import Reinmann.XiLocalCauchy
import Reinmann.XiAdaptiveTiles
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-! Complete degree-eight ordinary Taylor jet and nonvanishing certificate for
the actual completed Xi function on the hard tile `‖z - (1/2 + 14i)‖ ≤ 1/16`. -/
noncomputable section
namespace Reinmann.HardTileXi
open Finset Metric Filter
open CertifiedTaylorModel CertifiedTaylorComposition CertifiedTaylorInputs
open HardTileFiniteJets
open scoped Topology
set_option maxRecDepth 20000

'''

    def emit_node(name, jet, fn, analytic):
        nonlocal out
        out += f'def F_{name} (s : ℂ) : ℂ := {fn}\n\n'
        out += f'def J_{name} : Jet8 := fun k =>\n  match k.val with\n'
        for k, d in enumerate(jet):
            out += f'  | {k} => {d.lean()}\n'
        out += '  | _ => zero\n\n'
        out += f'theorem A_{name} : AnalyticAt ℂ F_{name} c := by\n  {analytic}\n\n'
        return Node(name, jet)

    def emit_arith(name, a, b_node=None, q=None):
        nonlocal out
        if q is not None:
            jet = scale(q, a.jet)
            fn = f'value {pair(q)}*F_{a.name} s'
            analytic = f'exact analyticAt_const.mul A_{a.name}'
            sound = f'sound_scale A_{a.name} S_{a.name}'
            op = 'jetScale'
            deps = f'J_{name}, J_{a.name}'
        else:
            jet = mul(a.jet, b_node.jet)
            fn = f'F_{a.name} s*F_{b_node.name} s'
            analytic = f'exact A_{a.name}.mul A_{b_node.name}'
            sound = f'sound_mul A_{a.name} A_{b_node.name} S_{a.name} S_{b_node.name}'
            op = 'jetMul'
            deps = f'J_{name}, J_{a.name}, J_{b_node.name}'
        for k in range(9):
            if q is not None:
                raw = exact(*q).mul(a.jet[k])
            else:
                raw = ZERO
                for i in range(k + 1):
                    raw = raw.add(a.jet[i].mul(b_node.jet[k - i]))
            lhs = raw.r + size((raw.c[0] - jet[k].c[0], raw.c[1] - jet[k].c[1]))
            assert lhs <= jet[k].r, (name, k, lhs, jet[k].r)
        node = emit_node(name, jet, fn, analytic)
        out += f'''set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_{name} : Sound J_{name} F_{name} c := by
  apply sound_round ({sound})
  intro k
  fin_cases k <;> norm_num [{deps}, {op}, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

'''
        return node

    # 1. Prefactor jet: ((s/2)*(s-1)) * exp((-log pi)*(s/2))
    neg_logpi = emit_arith('negLogPi', logpi, q=(Q(-1), Q(0)))
    pi_arg = emit_arith('piArg', neg_logpi, half_s)

    cert_text, constant = lean_certificate('piPowerValue', pi_arg.jet[0])
    out += cert_text
    pi_pow_jet = exponential(pi_arg.jet, constant)
    pi_pow = emit_node('piPower', pi_pow_jet, 'Complex.exp (F_piArg s)', "exact A_piArg.cexp'")
    out += '''set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_piPower : Sound J_piPower F_piPower c := by
  apply exp_sound A_piArg S_piArg piPowerValue piPowerValue_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [piPowerValue, J_piArg]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [J_piPower, J_piArg, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

'''

    poly_pre = emit_arith('polyPrefactor', half_s, s_minus_1)
    pre = emit_arith('prefactor', poly_pre, pi_pow)

    # 2. Inflated actual Gamma(s/2) and zeta(s) jets
    g_err = Q(4, 10**14)
    z_err = Q(1, 10**7)
    g_inf_jet = [outward(Disk(d.c, d.r + g_err)) for d in g.jet]
    z_inf_jet = [outward(Disk(d.c, d.r + z_err)) for d in z.jet]

    for k in range(9):
        assert g.jet[k].r + g_err + size((g.jet[k].c[0] - g_inf_jet[k].c[0], g.jet[k].c[1] - g_inf_jet[k].c[1])) <= g_inf_jet[k].r
        assert z.jet[k].r + z_err + size((z.jet[k].c[0] - z_inf_jet[k].c[0], z.jet[k].c[1] - z_inf_jet[k].c[1])) <= z_inf_jet[k].r

    g_actual = emit_node(
        'gammaActual',
        g_inf_jet,
        'Complex.Gamma (s / 2)',
        '''apply DifferentiableOn.analyticAt (s := Metric.ball EulerMaclaurinAnalytic.hardCentre 1)
    _ (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1))
  intro z hz
  exact (StirlingAnalytic.gamma_factor_differentiableAt
    (mem_ball_iff_norm.mp hz).le).differentiableWithinAt'''
    )
    out += '''theorem S_gammaApprox : Sound J_gammaFinite StirlingAnalytic.gammaApprox c :=
  sound_congr S_gammaFinite (Eventually.of_forall gammaFinite_identity)

theorem S_gammaPerturb :
    Sound (fun k => inflate (J_gammaFinite k) (4 / 10 ^ 14) (by norm_num)) F_gammaActual c := by
  apply sound_perturb (by norm_num) S_gammaApprox
  intro k
  simpa only [coefficient, F_gammaActual, c, HardTileGammaLogJet.centre,
    EulerMaclaurinAnalytic.hardCentre, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using
    StirlingAnalytic.gamma_coefficient_error_le k.val

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round S_gammaPerturb
  intro k
  fin_cases k <;> norm_num [J_gammaActual, J_gammaFinite, inflate, zero, size]

'''

    z_actual = emit_node(
        'zetaActual',
        z_inf_jet,
        'riemannZeta s',
        '''apply DifferentiableOn.analyticAt (s := Metric.ball EulerMaclaurinAnalytic.hardCentre 1)
    _ (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1))
  intro z hz
  exact (differentiableAt_riemannZeta
    (ZetaJetRemainder.hard_disk_ne_one (mem_ball_iff_norm.mp hz).le)).differentiableWithinAt'''
    )
    out += '''theorem S_zetaApprox :
    Sound J_emAfterCorr6 (fun s => EulerMaclaurinZeta.finiteModel s 21) c :=
  sound_congr S_emAfterCorr6 (Eventually.of_forall zetaFinite_identity)

theorem S_zetaPerturb :
    Sound (fun k => inflate (J_emAfterCorr6 k) (1 / 10 ^ 7) (by norm_num)) F_zetaActual c := by
  apply sound_perturb (by norm_num) S_zetaApprox
  intro k
  simpa only [coefficient, F_zetaActual, c, HardTileGammaLogJet.centre,
    EulerMaclaurinAnalytic.hardCentre, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
    Rat.cast_pow] using ZetaJetRemainder.zeta_coefficient_error_le k.val

set_option maxHeartbeats 5000000 in
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := by
  apply sound_round S_zetaPerturb
  intro k
  fin_cases k <;> norm_num [J_zetaActual, J_emAfterCorr6, inflate, zero, size]

'''

    # 3. Multiply prefactor * gammaActual * zetaActual
    pre_gamma = emit_arith('prefactorGamma', pre, g_actual)

    # For xiProduct, round k=0 onto the real axis (im = 0) since xi(1/2 + 14i) is real,
    # making the norm of the centre disk value purely rational!
    raw_xi = mul(pre_gamma.jet, z_actual.jet)
    d0 = raw_xi[0]
    step0 = Q(1, 2**50)
    c0_re = round(d0.c[0] / step0) * step0
    r0_raw = d0.r + abs(d0.c[0] - c0_re) + abs(d0.c[1])
    r0 = -(-r0_raw // step0) * step0
    raw_xi[0] = Disk((c0_re, Q(0)), r0)

    # Verify all 9 convolution + rounding inequalities in Python
    for k in range(9):
        conv = ZERO
        for i in range(k + 1):
            conv = conv.add(pre_gamma.jet[i].mul(z_actual.jet[k - i]))
        lhs = conv.r + size((conv.c[0] - raw_xi[k].c[0], conv.c[1] - raw_xi[k].c[1]))
        assert lhs <= raw_xi[k].r, ('xiProduct', k, lhs, raw_xi[k].r)

    xi_node = emit_node('xiProduct', raw_xi, 'F_prefactorGamma s*F_zetaActual s', 'exact A_prefactorGamma.mul A_zetaActual')
    out += '''set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul A_prefactorGamma A_zetaActual S_prefactorGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_prefactorGamma, J_zetaActual, jetMul, sum,
    CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
    exact, zero, qmul, qadd, size]

'''

    # Verify derivative bound and tile margin in Python
    r_tile = Q(1, 16)
    K_head = sum((n + 1) * (size(raw_xi[n + 1].c) + raw_xi[n + 1].r) * (r_tile ** n) for n in range(8))
    K_tail = Q(1000) * (r_tile ** 8) * (r_tile / (1 - r_tile) ** 2 + Q(9) / (1 - r_tile))
    K_total = K_head + K_tail
    K_cap = Q(9, 5000)
    assert K_total <= K_cap, (float(K_total), float(K_cap))
    assert raw_xi[0].r + K_cap * r_tile < raw_xi[0].c[0], (float(raw_xi[0].r + K_cap * r_tile), float(raw_xi[0].c[0]))

    c0_num, c0_den = raw_xi[0].c[0].numerator, raw_xi[0].c[0].denominator
    r0_num, r0_den = raw_xi[0].r.numerator, raw_xi[0].r.denominator

    out += f'''/-! ## Identification with `xiCompleted` and hard-tile nonvanishing -/

theorem piPower_eq (s : ℂ) : (Real.pi : ℂ) ^ (-s / 2) = F_piPower s := by
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [Complex.cpow_def_of_ne_zero hpi0, ← Complex.ofReal_log Real.pi_pos.le]
  unfold F_piPower F_piArg F_negLogPi F_logpi F_halfVariable F_variable
  simp only [value, Rat.cast_neg, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_zero, zero_mul, add_zero]
  congr 1
  ring

theorem xiProduct_eq_xiCompleted {{s : ℂ}} (hr : 0 < s.re) (h1 : s ≠ 1) :
    F_xiProduct s = xiCompleted s := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hr
  have hgamma : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hr
  have heq : completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero h0]
    field_simp
  rw [xiCompleted_eq_product h0 h1, heq, Complex.Gammaℝ_def, piPower_eq]
  unfold F_xiProduct F_prefactorGamma F_prefactor F_polyPrefactor
    F_halfVariable F_sminusone F_q12 F_variable F_gammaActual F_zetaActual
  simp only [value, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_neg,
    Rat.cast_zero, zero_mul, add_zero]
  ring

theorem quarter_ball_domain {{s : ℂ}} (hs : s ∈ Metric.ball c (1 / 4)) :
    0 < s.re ∧ s ≠ 1 := by
  have hn : ‖c - s‖ < 1 / 4 := by
    rw [norm_sub_rev]
    exact mem_ball_iff_norm.mp hs
  have hr := (Complex.re_le_norm (c - s)).trans_lt hn
  have hi := (Complex.im_le_norm (c - s)).trans_lt hn
  norm_num [c, HardTileGammaLogJet.centre, Complex.sub_re, Complex.sub_im] at hr hi
  refine ⟨by linarith, ?_⟩
  intro h1
  rw [h1] at hi
  norm_num at hi

theorem xiProduct_eventuallyEq : F_xiProduct =ᶠ[𝓝 c] xiCompleted := by
  filter_upwards [Metric.ball_mem_nhds c (by norm_num : (0 : ℝ) < 1 / 4)] with s hs
  exact xiProduct_eq_xiCompleted (quarter_ball_domain hs).1 (quarter_ball_domain hs).2

/-- Certified degree-eight ordinary Taylor jet for the actual completed Xi
function at the hard centre `1/2 + 14i`. -/
theorem xiCompleted_sound : Sound J_xiProduct xiCompleted c :=
  sound_congr S_xiProduct xiProduct_eventuallyEq

/-- All nine ordinary coefficient disks meet the requested `1e-7` budget. -/
theorem xiCompleted_coefficient_error_budget (k : Fin 9) :
    ‖coefficient xiCompleted c k.val - value (J_xiProduct k).centre‖ ≤ (1 / 10 ^ 7 : ℝ) := by
  have h : ‖coefficient xiCompleted c k.val - value (J_xiProduct k).centre‖ ≤
      ((J_xiProduct k).radius : ℝ) := xiCompleted_sound k
  apply h.trans
  fin_cases k <;> norm_num [J_xiProduct]

theorem hard_centre_value :
    value (J_xiProduct ⟨0, by omega⟩).centre =
      ({c0_num} / {c0_den} : ℂ) := by
  norm_num [J_xiProduct, value]

/-- Certified value enclosure for `xiCompleted (1/2 + 14i)`. -/
theorem hard_centre_enclosure :
    ‖xiCompleted c - ({c0_num} / {c0_den} : ℂ)‖ ≤
      ({r0_num} / {r0_den} : ℝ) := by
  have h := centre_contains xiCompleted_sound
  unfold Contains at h
  rw [hard_centre_value] at h
  simpa [J_xiProduct] using h

theorem xiCompleted_coeff_le_thousand (n : ℕ) :
    ‖coefficient xiCompleted c n‖ ≤ 1000 := by
  unfold coefficient
  apply XiLocalCauchy.taylor_coefficient_bound
  · norm_num [c, HardTileGammaLogJet.centre]
  · norm_num [c, HardTileGammaLogJet.centre]
  · norm_num [c, HardTileGammaLogJet.centre]

theorem xiCompleted_coeff_norm_le (k : Fin 9) :
    ‖coefficient xiCompleted c k.val‖ ≤
      ((size (J_xiProduct k).centre + (J_xiProduct k).radius : ℚ) : ℝ) :=
  norm_le_of_contains (xiCompleted_sound k)

def coeffBound (m : ℕ) : ℚ :=
  size (CertifiedTaylorModel.get J_xiProduct m).centre +
    (CertifiedTaylorModel.get J_xiProduct m).radius

theorem xiCompleted_coeff_le_bound {{n : ℕ}} (hn : n ∈ range 8) :
    ‖coefficient xiCompleted c (n + 1)‖ ≤ (coeffBound (n + 1) : ℝ) := by
  have hlt : n + 1 < 8 + 1 := Nat.succ_lt_succ (mem_range.mp hn)
  simpa [coeffBound, CertifiedTaylorModel.get, hlt] using
    xiCompleted_coeff_norm_le ⟨n + 1, hlt⟩

set_option maxHeartbeats 5000000 in
/-- Uniform derivative bound on the closed hard tile `‖z - (1/2 + 14i)‖ ≤ 1/16`,
combining the eight certified nonconstant Taylor coefficients and the proved
unit-circle Cauchy majorant `1000`. -/
theorem hard_tile_deriv_le {{z : ℂ}} (hz : ‖z - c‖ ≤ 1 / 16) :
    ‖deriv xiCompleted z‖ ≤ (9 / 5000 : ℝ) := by
  have h := TaylorDerivativeTail.derivative_bound differentiable_xiCompleted
    (r := (1 / 16 : ℝ)) (M := 1000) (by norm_num) (by norm_num) hz
    xiCompleted_coeff_le_thousand
  have hsum :
      (∑ n ∈ range 8, ((n + 1 : ℕ) : ℝ) * ‖coefficient xiCompleted c (n + 1)‖ * (1 / 16 : ℝ) ^ n) ≤
        ∑ n ∈ range 8, ((n + 1 : ℕ) : ℝ) * (coeffBound (n + 1) : ℝ) * (1 / 16 : ℝ) ^ n := by
    apply Finset.sum_le_sum
    intro n hn
    have hc := xiCompleted_coeff_le_bound hn
    gcongr
  apply h.trans ((add_le_add hsum le_rfl).trans _)
  norm_num [Finset.sum_range_succ, coeffBound, CertifiedTaylorModel.get, J_xiProduct, size]

/-- Complete hard-tile certificate: `xiCompleted z ≠ 0` throughout the closed
complex disk `‖z - (1/2 + 14i)‖ ≤ 1/16`. -/
theorem hard_tile_nonzero {{z : ℂ}} (hz : ‖z - c‖ ≤ 1 / 16) :
    xiCompleted z ≠ 0 := by
  have hcover := XiAdaptiveTiles.adaptive_cover_nonzero (n := 1)
    (f := xiCompleted) (S := Metric.closedBall c (1 / 16))
    (fun _ => Metric.closedBall c (1 / 16)) (fun _ => c)
    (fun _ => ({c0_num} / {c0_den} : ℂ))
    (fun _ => (1 / 16 : ℝ)) (fun _ => (9 / 5000 : ℝ))
    (fun _ => ({r0_num} / {r0_den} : ℝ))
    (fun _ => convex_closedBall c (1 / 16)) (fun _ => by simp)
    (fun _ w _ => differentiable_xiCompleted w) (fun _ => by norm_num)
    (fun _ _ hw => hard_tile_deriv_le (mem_closedBall_iff_norm.mp hw))
    (fun _ => hard_centre_enclosure)
    (fun w hw => ⟨⟨0, by omega⟩, hw, mem_closedBall_iff_norm.mp hw⟩)
    (fun _ => by norm_num)
  exact hcover z (mem_closedBall_iff_norm.mpr hz)

/-- Consequence for the Riemann zeta function on the hard tile
`‖z - (1/2 + 14i)‖ ≤ 1/16`. -/
theorem hard_tile_zeta_nonzero {{z : ℂ}} (hz : ‖z - c‖ ≤ 1 / 16) :
    riemannZeta z ≠ 0 := by
  intro hzeta
  have hball : z ∈ Metric.ball c (1 / 4) :=
    mem_ball_iff_norm.mpr (hz.trans_lt (by norm_num))
  have hd := quarter_ball_domain hball
  have hxi : xiCompleted z = 0 := by
    rw [← xiProduct_eq_xiCompleted hd.1 hd.2]
    simp [F_xiProduct, F_zetaActual, hzeta]
  exact hard_tile_nonzero hz hxi

end Reinmann.HardTileXi
'''
    target = Path(__file__).resolve().parents[2] / 'Reinmann/HardTileXi.lean'
    if check:
        assert target.read_text()==out, "Generated Xi certificate differs"
    else:
        target.write_text(out)
    print(f'{"Checked" if check else "Wrote"} {target} ({len(out.splitlines())} lines)')
    print(f'c0 = {float(raw_xi[0].c[0]):.12e}, r0 = {float(raw_xi[0].r):.6e}')
    print(f'K_total = {float(K_total):.9e} <= K_cap = {float(K_cap):.9e}')
    print(f'margin = {float(raw_xi[0].c[0] - (raw_xi[0].r + K_cap * r_tile)):.9e}')


if __name__ == '__main__':
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true")
    build_hard_tile_xi(parser.parse_args().check)
