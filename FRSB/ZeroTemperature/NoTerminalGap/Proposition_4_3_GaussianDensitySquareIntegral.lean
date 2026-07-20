import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FieldSimp

/-!
# Proposition 4.3: square integral of the standard Gaussian density

This is the explicit Gaussian integral needed after reducing the manuscript's CDF product integral
by integration by parts.
-/

namespace FRSB.ZeroTemperature.NoTerminalGap

open MeasureTheory ProbabilityTheory Real

/-- The square of the standard-normal density is integrable. -/
theorem integrable_standardGaussianPDF_sq :
    Integrable (fun x : ℝ => (gaussianPDFReal 0 1 x) ^ 2) := by
  have hsqrt2pi_sq : (√(2 * Real.pi)) ^ 2 = 2 * Real.pi :=
    Real.sq_sqrt (by positivity)
  have hpoint : ∀ x : ℝ,
      (gaussianPDFReal 0 1 x) ^ 2 =
        (1 / (2 * Real.pi)) * Real.exp (-1 * x ^ 2) := by
    intro x
    rw [gaussianPDFReal]
    simp only [NNReal.coe_one, sub_zero, mul_one, div_one]
    rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
    field_simp
    rw [show x ^ 2 * (-1 + -1) / 2 = -x ^ 2 by ring]
    rw [hsqrt2pi_sq]
  apply ((integrable_exp_neg_mul_sq (by norm_num : 0 < (1 : ℝ))).const_mul
    (1 / (2 * Real.pi))).congr
  filter_upwards with x
  exact (hpoint x).symm

/-- The square of the standard-normal density has integral `1 / (2 * sqrt pi)`. -/
theorem integral_standardGaussianPDF_sq :
    (∫ x : ℝ, (gaussianPDFReal 0 1 x) ^ 2) = 1 / (2 * √Real.pi) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrtpi : 0 < √Real.pi := Real.sqrt_pos.2 hpi
  have hsqrt2pi_sq : (√(2 * Real.pi)) ^ 2 = 2 * Real.pi :=
    Real.sq_sqrt (by positivity)
  have hpoint : ∀ x : ℝ,
      (gaussianPDFReal 0 1 x) ^ 2 =
        (1 / (2 * Real.pi)) * Real.exp (-1 * x ^ 2) := by
    intro x
    rw [gaussianPDFReal]
    simp only [NNReal.coe_one, sub_zero, mul_one, div_one]
    rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
    field_simp
    rw [show x ^ 2 * (-1 + -1) / 2 = -x ^ 2 by ring]
    rw [hsqrt2pi_sq]
  calc
    (∫ x : ℝ, (gaussianPDFReal 0 1 x) ^ 2) =
        ∫ x : ℝ, (1 / (2 * Real.pi)) * Real.exp (-1 * x ^ 2) := by
          apply integral_congr_ae
          filter_upwards with x
          exact hpoint x
    _ = (1 / (2 * Real.pi)) * ∫ x : ℝ, Real.exp (-1 * x ^ 2) := by
      rw [integral_const_mul]
    _ = (1 / (2 * Real.pi)) * √(Real.pi / 1) := by rw [integral_gaussian]
    _ = 1 / (2 * √Real.pi) := by
      rw [div_one]
      field_simp
      nlinarith [Real.sq_sqrt hpi.le]

end FRSB.ZeroTemperature.NoTerminalGap
