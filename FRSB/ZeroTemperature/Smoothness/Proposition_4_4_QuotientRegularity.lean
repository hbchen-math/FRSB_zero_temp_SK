import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Proposition 4.4: quotient regularity in the smoothness bootstrap

The order parameter is represented in the paper as a quotient of two stochastic moments.  Once
the moment-regularity lemma supplies the same differentiability order for numerator and denominator,
strict positivity of the denominator preserves that order for the quotient.
-/

namespace FRSB.ZeroTemperature.Smoothness

open Set

/-- A quotient of two `C^n` real functions is `C^n` wherever its denominator is positive.

Applied with `n = r + 1`, this is the deterministic final step in each iteration of the bootstrap
in Proposition `prop:zt-smoothness`. -/
theorem contDiffOn_div_of_pos
    {n : WithTop ℕ∞} {s : Set ℝ} {numerator denominator : ℝ → ℝ}
    (hnum : ContDiffOn ℝ n numerator s)
    (hden : ContDiffOn ℝ n denominator s)
    (hden_pos : ∀ x ∈ s, 0 < denominator x) :
    ContDiffOn ℝ n (fun x ↦ numerator x / denominator x) s := by
  exact hnum.fun_div hden fun x hx ↦ (hden_pos x hx).ne'

end FRSB.ZeroTemperature.Smoothness
