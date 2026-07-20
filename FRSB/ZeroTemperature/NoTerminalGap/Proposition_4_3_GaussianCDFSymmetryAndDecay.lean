import FRSB.ZeroTemperature.NoTerminalGap.Proposition_4_3_GaussianCDFFiniteIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Proposition 4.3: symmetry and decay of the standard Gaussian

This file records the elementary analytic boundary facts used in passing from
finite-interval identities to the whole-line Gaussian identity.
-/

namespace FRSB.ZeroTemperature.NoTerminalGap

open Asymptotics Filter MeasureTheory ProbabilityTheory Set

/-- The standard Gaussian density is even. -/
theorem gaussianPDFReal_zero_one_neg (x : ℝ) :
    gaussianPDFReal 0 1 (-x) = gaussianPDFReal 0 1 x := by
  simp [gaussianPDFReal]

/-- The standard Gaussian CDF is symmetric about the origin. -/
theorem standardNormalCDF_neg (x : ℝ) :
    standardNormalCDF (-x) = 1 - standardNormalCDF x := by
  have hpdf : Integrable (gaussianPDFReal 0 1) := integrable_gaussianPDFReal 0 1
  have hleft_right := integral_comp_neg_Iic (-x) (gaussianPDFReal 0 1)
  simp_rw [neg_neg, gaussianPDFReal_zero_one_neg] at hleft_right
  rw [standardNormalCDF_eq_integral_Iic, standardNormalCDF_eq_integral_Iic]
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (hpdf.integrableOn : IntegrableOn (gaussianPDFReal 0 1) (Iic x))
    (hpdf.integrableOn : IntegrableOn (gaussianPDFReal 0 1) (Ioi x))
  rw [integral_gaussianPDFReal_eq_one (0 : ℝ) (by norm_num : (1 : NNReal) ≠ 0)] at hsplit
  rw [hleft_right]
  linarith

/-- The standard Gaussian CDF tends to one at `+∞`. -/
theorem tendsto_standardNormalCDF_atTop :
    Tendsto standardNormalCDF atTop (nhds 1) := by
  unfold standardNormalCDF
  exact ProbabilityTheory.tendsto_cdf_atTop _

/-- The standard Gaussian CDF tends to zero at `-∞`. -/
theorem tendsto_standardNormalCDF_atBot :
    Tendsto standardNormalCDF atBot (nhds 0) := by
  unfold standardNormalCDF
  exact ProbabilityTheory.tendsto_cdf_atBot _

/-- The standard Gaussian density tends to zero at `+∞`. -/
theorem tendsto_gaussianPDFReal_zero_one_atTop :
    Tendsto (gaussianPDFReal 0 1) atTop (nhds 0) := by
  have hrapid :
      (fun x : ℝ => Real.exp ((-(1 / 2 : ℝ)) * x ^ 2 + 0 * x))
        =o[atTop] (fun x : ℝ => x ^ (-1 : ℝ)) :=
    rexp_neg_quadratic_isLittleO_rpow_atTop (by norm_num) 0 (-1)
  have hexp :
      Tendsto (fun x : ℝ => Real.exp ((-(1 / 2 : ℝ)) * x ^ 2 + 0 * x))
        atTop (nhds 0) := by
    exact hrapid.trans_tendsto (by
      simpa using tendsto_rpow_neg_atTop (show 0 < (1 : ℝ) by norm_num))
  unfold gaussianPDFReal
  have hc : Tendsto
      (fun _ : ℝ => (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹)
      atTop (nhds ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹)) :=
    tendsto_const_nhds
  convert hc.mul hexp using 1 <;> norm_num <;> ring_nf

/-- The standard Gaussian density tends to zero at `-∞`. -/
theorem tendsto_gaussianPDFReal_zero_one_atBot :
    Tendsto (gaussianPDFReal 0 1) atBot (nhds 0) := by
  have h : Tendsto (fun x : ℝ => gaussianPDFReal 0 1 (-x)) atBot (nhds 0) := by
    simpa only [Function.comp_apply] using
      tendsto_gaussianPDFReal_zero_one_atTop.comp tendsto_neg_atBot_atTop
  simpa only [gaussianPDFReal_zero_one_neg] using h

/-- The density-weighted CDF boundary factor in the integration-by-parts
primitive vanishes at `+∞`. -/
theorem tendsto_gaussianPDFReal_mul_one_sub_two_mul_cdf_atTop :
    Tendsto
      (fun x : ℝ => gaussianPDFReal 0 1 x * (1 - 2 * standardNormalCDF x))
      atTop (nhds 0) := by
  have hfactor : Tendsto (fun x : ℝ => 1 - 2 * standardNormalCDF x)
      atTop (nhds (-1)) := by
    convert tendsto_const_nhds.sub
      (tendsto_const_nhds.mul tendsto_standardNormalCDF_atTop) using 1 <;> norm_num
  convert tendsto_gaussianPDFReal_zero_one_atTop.mul hfactor using 1 <;> norm_num

/-- The same density-weighted boundary factor vanishes at `-∞`. -/
theorem tendsto_gaussianPDFReal_mul_one_sub_two_mul_cdf_atBot :
    Tendsto
      (fun x : ℝ => gaussianPDFReal 0 1 x * (1 - 2 * standardNormalCDF x))
      atBot (nhds 0) := by
  have hfactor : Tendsto (fun x : ℝ => 1 - 2 * standardNormalCDF x)
      atBot (nhds 1) := by
    convert tendsto_const_nhds.sub
      (tendsto_const_nhds.mul tendsto_standardNormalCDF_atBot) using 1 <;> norm_num
  convert tendsto_gaussianPDFReal_zero_one_atBot.mul hfactor using 1 <;> norm_num

/-- The linear CDF-product part of the primitive vanishes at `+∞`.
This is the finite-first-moment tail estimate specialized to the Gaussian. -/
theorem tendsto_id_mul_standardNormalCDF_product_atTop :
    Tendsto
      (fun x : ℝ => x * (standardNormalCDF x * (1 - standardNormalCDF x)))
      atTop (nhds 0) := by
  let pdf : ℝ → ℝ := gaussianPDFReal 0 1
  have hpdf : Integrable pdf := integrable_gaussianPDFReal 0 1
  have hmoment : Integrable (fun z : ℝ => z * pdf z) := by
    dsimp [pdf]
    unfold gaussianPDFReal
    have h := (integrable_mul_exp_neg_mul_sq
      (by norm_num : 0 < (1 / 2 : ℝ))).const_mul
      ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹)
    convert h using 1 <;> norm_num
    funext z
    ring
  have htail (x : ℝ) :
      1 - standardNormalCDF x = ∫ z in Ioi x, pdf z := by
    have hsplit := intervalIntegral.integral_Iic_add_Ioi
      (hpdf.integrableOn : IntegrableOn pdf (Iic x))
      (hpdf.integrableOn : IntegrableOn pdf (Ioi x))
    rw [integral_gaussianPDFReal_eq_one (0 : ℝ)
      (by norm_num : (1 : NNReal) ≠ 0)] at hsplit
    rw [standardNormalCDF_eq_integral_Iic]
    dsimp [pdf] at hsplit ⊢
    linarith
  have hmomentTail :
      Tendsto (fun x : ℝ => ∫ z in Ioi x, z * pdf z) atTop (nhds 0) :=
    MeasureTheory.tendsto_integral_Ioi_zero tendsto_id
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hmomentTail
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact mul_nonneg hx <| mul_nonneg
      (ProbabilityTheory.cdf_nonneg _ x)
      (sub_nonneg.mpr (ProbabilityTheory.cdf_le_one _ x))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have hPhi0 : 0 ≤ standardNormalCDF x := ProbabilityTheory.cdf_nonneg _ x
    have hPhi1 : standardNormalCDF x ≤ 1 := ProbabilityTheory.cdf_le_one _ x
    calc
      x * (standardNormalCDF x * (1 - standardNormalCDF x)) ≤
          x * (1 - standardNormalCDF x) := by
        apply mul_le_mul_of_nonneg_left _ hx
        exact mul_le_of_le_one_left (sub_nonneg.mpr hPhi1) hPhi1
      _ = ∫ z in Ioi x, x * pdf z := by
        rw [htail, MeasureTheory.integral_const_mul]
      _ ≤ ∫ z in Ioi x, z * pdf z := by
        apply MeasureTheory.integral_mono_ae
        · exact (hpdf.const_mul x).integrableOn
        · exact hmoment.integrableOn
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
          exact mul_le_mul_of_nonneg_right (le_of_lt hz)
            (gaussianPDFReal_nonneg 0 1 z)

/-- By Gaussian symmetry, the linear CDF-product part also vanishes at `-∞`. -/
theorem tendsto_id_mul_standardNormalCDF_product_atBot :
    Tendsto
      (fun x : ℝ => x * (standardNormalCDF x * (1 - standardNormalCDF x)))
      atBot (nhds 0) := by
  have h := tendsto_id_mul_standardNormalCDF_product_atTop.comp
    tendsto_neg_atBot_atTop
  have hneg : Tendsto
      (fun x : ℝ => -((fun y : ℝ =>
        y * (standardNormalCDF y * (1 - standardNormalCDF y))) (-x)))
      atBot (nhds 0) := by
    simpa only [Function.comp_apply, neg_zero] using h.neg
  convert hneg using 1
  funext x
  simp only [Function.comp_apply]
  rw [standardNormalCDF_neg]
  ring

/-- The complete finite-interval primitive tends to zero at `+∞`. -/
theorem tendsto_gaussianCDFProductPrimitive_atTop :
    Tendsto gaussianCDFProductPrimitive atTop (nhds 0) := by
  unfold gaussianCDFProductPrimitive
  simpa using tendsto_id_mul_standardNormalCDF_product_atTop.add
    tendsto_gaussianPDFReal_mul_one_sub_two_mul_cdf_atTop

/-- The complete finite-interval primitive tends to zero at `-∞`. -/
theorem tendsto_gaussianCDFProductPrimitive_atBot :
    Tendsto gaussianCDFProductPrimitive atBot (nhds 0) := by
  unfold gaussianCDFProductPrimitive
  simpa using tendsto_id_mul_standardNormalCDF_product_atBot.add
    tendsto_gaussianPDFReal_mul_one_sub_two_mul_cdf_atBot

end FRSB.ZeroTemperature.NoTerminalGap
