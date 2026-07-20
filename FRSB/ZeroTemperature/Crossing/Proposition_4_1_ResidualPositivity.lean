import Mathlib

/-!
# Proposition 4.1: positivity of the residual integrand

This is the exact algebra at the end of Step 5 of the arbitrary-gap crossing
proof.  The analytic/PDE estimates enter only through their displayed signs.
-/

namespace FRSB.ZeroTemperature.Crossing

/-- The residual integrand is bounded below by `w z J τ`.

Here `cJB` denotes `c J_B`, `zJ` denotes `z J`, and `cz` denotes `c z`.
The assumptions are exactly `0 ≤ τ ≤ c z`, `c J_B ≤ 3 z J`, and the
nonnegativity of the weights appearing in the manuscript. -/
theorem residual_integrand_lower_bound
    {w tau cz cJB zJ : ℝ}
    (hw : 0 ≤ w)
    (htau_upper : tau ≤ cz)
    (hcJB : cJB ≤ 3 * zJ) :
    w * (2 * cJB * (tau - cz) + zJ * (6 * cz - 5 * tau)) ≥
      w * zJ * tau := by
  have hdiff : tau - cz ≤ 0 := sub_nonpos.mpr htau_upper
  have hmul : 2 * (3 * zJ) * (tau - cz) ≤
      2 * cJB * (tau - cz) := by
    exact mul_le_mul_of_nonpos_right (by linarith) hdiff
  have hinside : zJ * tau ≤
      2 * cJB * (tau - cz) + zJ * (6 * cz - 5 * tau) := by
    nlinarith
  have := mul_le_mul_of_nonneg_left hinside hw
  nlinarith

/-- Nonnegativity of the residual follows after integration once the
pointwise lower bound is combined with `w z J τ ≥ 0`. -/
theorem residual_integrand_nonnegative
    {w tau cz cJB zJ : ℝ}
    (hw : 0 ≤ w)
    (htau : 0 ≤ tau)
    (htau_upper : tau ≤ cz)
    (hcJB : cJB ≤ 3 * zJ)
    (hzJ : 0 ≤ zJ) :
    0 ≤ w * (2 * cJB * (tau - cz) + zJ * (6 * cz - 5 * tau)) := by
  exact (mul_nonneg (mul_nonneg hw hzJ) htau).trans
    (residual_integrand_lower_bound hw htau_upper hcJB)

end FRSB.ZeroTemperature.Crossing
