/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.PseudoHermitianPacketNorm
import Reinmann.XiDividedDifference
import Reinmann.XiAnnihilator

/-!
# Xi kernel packets realized in the arithmetic coefficient domain

The finite packet form is the actual Xi kernel Gram form. Its action
intertwines the independently defined coefficient differentiation operator.
This is a checked finite core, not a substitute for the written full Fock
construction. Norms here are coordinate packet norms, not formal Fock norms.
The final theorem is conditional on a simple off-critical zero; it asserts
neither existence nor absence of such a zero. Higher-jet masses remain a
separate arithmetic obligation.
-/

noncomputable section
open Complex
open scoped ComplexConjugate

namespace Reinmann.XiKernelPackets
open XiDividedDifference XiAnnihilator

abbrev Packet := ℂ × ℂ

def form (s t : ℂ) : AdditiveScalarForm Packet where
  η x y := x.1 * conj y.1 * kernel s s + x.1 * conj y.2 * kernel s t +
    x.2 * conj y.1 * kernel t s + x.2 * conj y.2 * kernel t t
  smul_left := by
    intro a x y
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  smul_right := by
    intro a x y
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_mul]
    ring
  add_left := by
    intro x y z
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  add_right := by
    intro x y z
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    ring

theorem form_hermitian (s t : ℂ) (x y : Packet) :
    conj ((form s t).η y x) = (form s t).η x y := by
  simp only [form, map_add, map_mul, Complex.conj_conj, ← kernel_hermitian]
  ring

def action (s t : ℂ) : Packet →ₗ[ℂ] Packet where
  toFun x := (spectralParam s * x.1, spectralParam t * x.2)
  map_add' := by intro x y; ext <;> simp [mul_add]
  map_smul' := by intro a x; ext <;> simp [smul_eq_mul] <;> ring

theorem action_form_symmetric {s t : ℂ} (hs : xiCompleted s = 0)
    (ht : xiCompleted t = 0) (x y : Packet) :
    (form s t).η (action s t x) y = (form s t).η x (action s t y) := by
  have hss := kernel_zero_spectral_symmetry hs hs
  have hst := kernel_zero_spectral_symmetry hs ht
  have hts := kernel_zero_spectral_symmetry ht hs
  have htt := kernel_zero_spectral_symmetry ht ht
  simp only [form, action, LinearMap.coe_mk, AddHom.coe_mk, map_mul]
  linear_combination x.1 * conj y.1 * hss + x.1 * conj y.2 * hst +
    x.2 * conj y.1 * hts + x.2 * conj y.2 * htt

def realize (s t : ℂ) (hs : xiCompleted s = 0) (ht : xiCompleted t = 0) :
    Packet →ₗ[ℂ] domain where
  toFun x := x.1 • zeroState s hs + x.2 • zeroState t ht
  map_add' := by intro x y; simp only [Prod.fst_add, Prod.snd_add]; module
  map_smul' := by
    intro a x
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    module

theorem realize_action (s t : ℂ) (hs : xiCompleted s = 0) (ht : xiCompleted t = 0)
    (x : Packet) :
    spectralOnDomain (realize s t hs ht x) = realize s t hs ht (action s t x) := by
  change spectralOnDomain (x.1 • zeroState s hs + x.2 • zeroState t ht) =
    (spectralParam s * x.1) • zeroState s hs + (spectralParam t * x.2) • zeroState t ht
  rw [map_add, map_smul, map_smul, zeroState_eigen, zeroState_eigen]
  module

theorem realize_residual (s t : ℂ) (hs : xiCompleted s = 0) (ht : xiCompleted t = 0)
    (x : Packet) (μ : ℂ) :
    realize s t hs ht (action s t x - μ • x) =
      spectralOnDomain (realize s t hs ht x) - μ • realize s t hs ht x := by
  rw [map_sub, map_smul, realize_action]

theorem realize_injective {s t : ℂ} (hst : s ≠ t)
    (hs : xiCompleted s = 0) (ht : xiCompleted t = 0) :
    Function.Injective (realize s t hs ht) := by
  intro x y h
  have h0 := congrArg (fun v : domain => (v : FockEigenvectors.Coeff) 0) h
  have h1 := congrArg (fun v : domain => (v : FockEigenvectors.Coeff) 1) h
  simp [realize, zeroState, FockEigenvectors.coherent, smul_eq_mul] at h0 h1
  have hz : (x.1 - y.1) * (s - t) = 0 := by linear_combination h1 - t * h0
  have hx : x.1 = y.1 := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hst))
  have hy : x.2 = y.2 := by linear_combination h0 - hx
  exact Prod.ext hx hy

def partner (s : ℂ) : ℂ := 1 - conj s

theorem partner_zero {s : ℂ} (hz : xiCompleted s = 0) : xiCompleted (partner s) = 0 := by
  rw [partner, xi_one_sub, xi_conj, hz, map_zero]

theorem kernel_partner (s : ℂ) : kernel s (partner s) = I * deriv xiCompleted s := by
  apply kernel_at_reflection
  simp [partner]

/-- This finite core verifies mass and ordinary residual smallness in the same
arithmetic kernel form. The paired defect remains fixed and nonzero off the line. -/
theorem simple_offcritical_unit_mass_packets {s : ℂ} (hz : xiCompleted s = 0)
    (hoff : s.re ≠ 1 / 2) (hder : deriv xiCompleted s ≠ 0) {τ : ℝ} (hτ : 0 < τ) :
    ∃ x : Packet, (form s (partner s)).η x x = 1 ∧
      realize s (partner s) hz (partner_zero hz) x ≠ 0 ∧
      ‖action s (partner s) x - spectralParam s • x‖ < τ ∧
      ‖(form s (partner s)).toScalarHomogeneousForm.defect x
        (action s (partner s) x - spectralParam s • x)‖ = 2 * |s.re - 1 / 2| := by
  have heig : action s (partner s) (1, 0) = spectralParam s • ((1, 0) : Packet) := by
    ext <;> simp [action, smul_eq_mul]
  have hv : (form s (partner s)).η (1, 0) (1, 0) = 0 := by
    simpa [form] using kernel_mass_off_critical hz hoff
  have hB : (form s (partner s)).η (1, 0) (0, 1) ≠ 0 := by
    simpa [form, kernel_partner] using mul_ne_zero Complex.I_ne_zero hder
  obtain ⟨x, hx, hmass, hr⟩ := PacketMass.exists_unit_mass_small_residual
    (form s (partner s)) (form_hermitian s (partner s)) (action s (partner s))
    heig hv hB hτ
  have hst : s ≠ partner s := mt (reflected_self_iff s).mp hoff
  have hreal : realize s (partner s) hz (partner_zero hz) x ≠ 0 := by
    intro hzero
    apply hx
    apply realize_injective hst hz (partner_zero hz)
    simpa using hzero
  refine ⟨x, hmass, hreal, hr, ?_⟩
  exact PacketMass.paired_residual_norm_of_unit_mass (form s (partner s))
    (action s (partner s)) x s (by rw [hmass, norm_one])
    (action_form_symmetric hz (partner_zero hz) x x)

end Reinmann.XiKernelPackets
