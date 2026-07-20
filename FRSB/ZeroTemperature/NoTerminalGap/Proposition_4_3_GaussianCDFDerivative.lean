import FRSB.ZeroTemperature.NoTerminalGap.Proposition_4_3_GaussianBoundaryFactor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Proposition 4.3: the standard Gaussian CDF and its derivative

This supplies the first analytic bridge needed to reduce the manuscript's
Gaussian CDF product integral to the already evaluated density-square
integral.
-/

namespace FRSB.ZeroTemperature.NoTerminalGap

open MeasureTheory ProbabilityTheory Set

/-- Mathlib's standard Gaussian CDF is the integral of its real density over
the left half-line. -/
theorem standardNormalCDF_eq_integral_Iic (x : ℝ) :
    standardNormalCDF x =
      ∫ z : ℝ in Iic x, gaussianPDFReal 0 1 z := by
  rw [standardNormalCDF, ProbabilityTheory.cdf_eq_real]
  rw [measureReal_def,
    gaussianReal_apply_eq_integral (0 : ℝ) (by norm_num : (1 : NNReal) ≠ 0)]
  rw [ENNReal.toReal_ofReal]
  exact integral_nonneg_of_ae <|
    ae_restrict_mem measurableSet_Iic |>.mono fun z _ => gaussianPDFReal_nonneg 0 1 z

/-- The standard Gaussian CDF has derivative equal to the standard Gaussian
density at every real point. -/
theorem hasDerivAt_standardNormalCDF (x : ℝ) :
    HasDerivAt standardNormalCDF (gaussianPDFReal 0 1 x) x := by
  let pdf : ℝ → ℝ := gaussianPDFReal 0 1
  have hpdf_integrable : Integrable pdf := integrable_gaussianPDFReal 0 1
  have hpdf_continuous : Continuous pdf := by
    unfold pdf gaussianPDFReal
    fun_prop
  have hrepr : standardNormalCDF = fun u =>
      (∫ z : ℝ in Iic x, pdf z) + ∫ z : ℝ in x..u, pdf z := by
    funext u
    rw [standardNormalCDF_eq_integral_Iic]
    have hdiff := intervalIntegral.integral_Iic_sub_Iic
      (hpdf_integrable.integrableOn) (hpdf_integrable.integrableOn)
      (a := x) (b := u)
    linarith
  have hint : HasDerivAt (fun u => ∫ z : ℝ in x..u, pdf z) (pdf x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (hpdf_continuous.intervalIntegrable _ _)
      hpdf_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hpdf_continuous.continuousAt
  rw [hrepr]
  simpa only [Pi.add_apply, zero_add] using
    (hasDerivAt_const x (∫ z : ℝ in Iic x, pdf z)).add hint

/-- In particular, the standard Gaussian CDF is continuous. -/
theorem continuous_standardNormalCDF : Continuous standardNormalCDF :=
  continuous_iff_continuousAt.2 fun x =>
    (hasDerivAt_standardNormalCDF x).continuousAt

end FRSB.ZeroTemperature.NoTerminalGap
