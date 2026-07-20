import Mathlib

/-!
# Appendix B: passage of the third-derivative sign to zero temperature

This file formalizes the final limiting implication in the active Appendix B
proof of `lem:zt-regularized-terminal-data`.
-/

namespace FRSB.ZeroTemperature

/-- Nonpositivity of every sufficiently large regularized third derivative
passes to its pointwise limit.

In the paper, `regularizedThird lambda t x` is
`∂_x^3 u_lambda(t,x)`.  The first hypothesis is
`eq:zt-ulambda-D-negative`; the second is the `j = 3` case of
`eq:zt-lambda-smooth-convergence`.  The conclusion is exactly the sign
assertion `eq:zt-D-negative`. -/
theorem lemma_3_4_thirdDerivative_nonpositive_of_regularized_limit
    (regularizedThird : ℝ → ℝ → ℝ → ℝ)
    (thirdDerivative : ℝ → ℝ → ℝ)
    (hregularized : ∀ lambda > 0, ∀ t, 0 ≤ t → t < 1 →
      ∀ x > 0, regularizedThird lambda t x ≤ 0)
    (hlimit : ∀ t, 0 ≤ t → t < 1 → ∀ x > 0,
      Filter.Tendsto (fun lambda => regularizedThird lambda t x)
        Filter.atTop (nhds (thirdDerivative t x))) :
    ∀ t, 0 ≤ t → t < 1 → ∀ x > 0, thirdDerivative t x ≤ 0 := by
  intro t ht0 ht1 x hx
  apply le_of_tendsto (hlimit t ht0 ht1 x hx)
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with lambda hlambda
  exact hregularized lambda hlambda t ht0 ht1 x hx

end FRSB.ZeroTemperature
