import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Proposition 4.4: bootstrap to smoothness

This file isolates the induction at the end of the zero-temperature smoothness proof.  The analytic
work supplies a base case and an improvement rule; the theorem below records that iterating that
rule gives smoothness of every finite order, hence `C^∞` regularity.
-/

namespace FRSB.ZeroTemperature.Smoothness

open Set
open scoped ContDiff

/-- A `C⁰` function is smooth on a set if regularity of every finite order can be improved by one.

In Proposition `prop:zt-smoothness`, the set is a compact interval `[0,T]`.  Moment regularity and
the positive-denominator quotient formula provide `improve`; continuity of the quotient provides
`base`. -/
theorem contDiffOn_top_of_zero_of_succ
    {f : ℝ → ℝ} {s : Set ℝ}
    (base : ContDiffOn ℝ 0 f s)
    (improve : ∀ r : ℕ, ContDiffOn ℝ r f s → ContDiffOn ℝ (r + 1) f s) :
    ContDiffOn ℝ ∞ f s := by
  rw [contDiffOn_infty]
  intro r
  induction r with
  | zero => exact base
  | succ r hr => simpa [Nat.succ_eq_add_one] using improve r hr

end FRSB.ZeroTemperature.Smoothness
