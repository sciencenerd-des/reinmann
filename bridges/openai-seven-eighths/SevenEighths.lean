import OAI.NumberTheory.DirichletL.Nonvanishing

/-! Run inside the pinned OpenAI Lean 4.34.1 project. This file mirrors the
Reinmann contract; it does not import Lean 4.30 binaries across toolchains. -/
namespace Reinmann

def ZetaZeroFreeRightOf (sigma : ℝ) : Prop :=
  ∀ s : ℂ, sigma < s.re → riemannZeta s ≠ 0

theorem zetaZeroFreeRightOf_sevenEighths : ZetaZeroFreeRightOf (7 / 8) :=
  fun s hs => OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re hs

end Reinmann

#check Reinmann.zetaZeroFreeRightOf_sevenEighths
#print axioms OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re
#print axioms Reinmann.zetaZeroFreeRightOf_sevenEighths
