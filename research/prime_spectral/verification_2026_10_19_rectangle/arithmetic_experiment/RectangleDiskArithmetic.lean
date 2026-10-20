/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.CertifiedTaylorModel

/-! Projection rules avoid normalizing unused proof fields in finite disk sums. -/
noncomputable section
namespace Reinmann.RectangleDiskArithmetic
open CertifiedTaylorModel

@[simp↓] theorem add_centre (a b : Disk) : (add a b).centre = qadd a.centre b.centre := rfl
@[simp↓] theorem mul_centre (a b : Disk) : (mul a b).centre = qmul a.centre b.centre := rfl

@[simp↓] theorem add_re (a b : Disk) : (add a b).centre.1 = a.centre.1+b.centre.1 := rfl
@[simp↓] theorem add_im (a b : Disk) : (add a b).centre.2 = a.centre.2+b.centre.2 := rfl
@[simp↓] theorem add_radius (a b : Disk) : (add a b).radius = a.radius+b.radius := rfl
@[simp↓] theorem mul_re (a b : Disk) : (mul a b).centre.1 =
    a.centre.1*b.centre.1-a.centre.2*b.centre.2 := rfl
@[simp↓] theorem mul_im (a b : Disk) : (mul a b).centre.2 =
    a.centre.1*b.centre.2+a.centre.2*b.centre.1 := rfl
@[simp↓] theorem mul_radius (a b : Disk) : (mul a b).radius =
    a.radius*size b.centre+size a.centre*b.radius+a.radius*b.radius := rfl

@[simp↓] theorem sum_re (f : ℕ → Disk) (n : ℕ) :
    (sum f n).centre.1 = ∑ i ∈ Finset.range n, (f i).centre.1 := by
  induction n with
  | zero => simp [sum,zero,exact]
  | succ n ih => simp only [sum,add_re,ih,Finset.sum_range_succ]

@[simp↓] theorem sum_im (f : ℕ → Disk) (n : ℕ) :
    (sum f n).centre.2 = ∑ i ∈ Finset.range n, (f i).centre.2 := by
  induction n with
  | zero => simp [sum,zero,exact]
  | succ n ih => simp only [sum,add_im,ih,Finset.sum_range_succ]

@[simp↓] theorem sum_radius (f : ℕ → Disk) (n : ℕ) :
    (sum f n).radius = ∑ i ∈ Finset.range n, (f i).radius := by
  induction n with
  | zero => simp [sum,zero,exact]
  | succ n ih => simp only [sum,add_radius,ih,Finset.sum_range_succ]
end Reinmann.RectangleDiskArithmetic
