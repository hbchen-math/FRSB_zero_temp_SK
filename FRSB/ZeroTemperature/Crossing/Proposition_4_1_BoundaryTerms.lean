import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Proposition 4.1: boundary terms in the residual integration by parts

This file isolates the deterministic endpoint argument in Steps 4--5 of the
arbitrary-gap crossing proof.  In the manuscript, `F(B) = ∫_B^1 w Φ`, the
centered identity gives `F(0)=0`, and the PDE tail estimates give
`F(B) R₀(B) → 0` as `B ↑ 1`.  After extending the endpoint value by zero,
these are exactly the two boundary hypotheses below.
-/

namespace FRSB.ZeroTemperature.Crossing

open Set
open scoped Interval

/-- The centered identity `∫₀¹ w Φ = 0` makes the tail antiderivative
`F(B) = ∫_B^1 w Φ` vanish at the left endpoint. -/
theorem tailAntiderivative_zero_at_zero
    (f F : ℝ → ℝ)
    (hF : ∀ B ∈ Icc (0 : ℝ) 1, F B = ∫ θ in B..1, f θ)
    (hcentered : ∫ θ in (0 : ℝ)..1, f θ = 0) :
    F 0 = 0 := by
  rw [hF 0 (by simp), hcentered]

/-- Integration by parts with precisely the two vanishing PDE boundary
products used in Proposition 4.1.

Taking `F' = -w Φ` and `R' = (R₀)_B` yields
`∫ w Φ R = ∫ F (R₀)_B`. -/
theorem residual_integrationByParts_of_boundaryTerms
    (F R : ℝ → ℝ)
    (hF : AbsolutelyContinuousOnInterval F 0 1)
    (hR : AbsolutelyContinuousOnInterval R 0 1)
    (hleft : F 0 * R 0 = 0)
    (hright : F 1 * R 1 = 0) :
    (∫ B in (0 : ℝ)..1, (-deriv F B) * R B) =
      ∫ B in (0 : ℝ)..1, F B * deriv R B := by
  have hibp := hF.integral_mul_deriv_eq_deriv_mul hR
  rw [hright, hleft, sub_zero, zero_sub] at hibp
  calc
    (∫ B in (0 : ℝ)..1, (-deriv F B) * R B) =
        -(∫ B in (0 : ℝ)..1, deriv F B * R B) := by
          rw [← intervalIntegral.integral_neg]
          apply intervalIntegral.integral_congr
          intro B _
          ring
    _ = ∫ B in (0 : ℝ)..1, F B * deriv R B := hibp.symm

/-- Convenient specialization when both endpoint values of `F` are zero. -/
theorem residual_integrationByParts_of_F_endpoint_zero
    (F R : ℝ → ℝ)
    (hF : AbsolutelyContinuousOnInterval F 0 1)
    (hR : AbsolutelyContinuousOnInterval R 0 1)
    (hF0 : F 0 = 0)
    (hF1 : F 1 = 0) :
    (∫ B in (0 : ℝ)..1, (-deriv F B) * R B) =
      ∫ B in (0 : ℝ)..1, F B * deriv R B := by
  apply residual_integrationByParts_of_boundaryTerms F R hF hR
  · simp [hF0]
  · simp [hF1]

end FRSB.ZeroTemperature.Crossing
