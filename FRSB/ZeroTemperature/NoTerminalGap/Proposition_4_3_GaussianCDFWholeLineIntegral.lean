import FRSB.ZeroTemperature.NoTerminalGap.Proposition_4_3_GaussianCDFSymmetryAndDecay
import FRSB.ZeroTemperature.NoTerminalGap.Proposition_4_3_GaussianDensitySquareIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Proposition 4.3: whole-line Gaussian CDF product integral

This closes the Gaussian integration-by-parts subcalculation used in the
terminal boundary factor.  The proof passes from the finite-interval identity
to the whole line using the explicitly proved primitive decay.
-/

namespace FRSB.ZeroTemperature.NoTerminalGap

open Filter MeasureTheory ProbabilityTheory Real Set

/-- The Gaussian CDF product has the exact whole-line integral appearing in
the manuscript. -/
theorem integral_standardNormalCDF_mul_one_sub :
    (∫ x : ℝ, standardNormalCDF x * (1 - standardNormalCDF x)) =
      1 / Real.sqrt Real.pi := by
  let F : ℝ → ℝ := fun x => standardNormalCDF x * (1 - standardNormalCDF x)
  let G : ℝ → ℝ := fun x => (gaussianPDFReal 0 1 x) ^ 2
  have hG : Integrable G := by
    simpa [G] using integrable_standardGaussianPDF_sq
  have hGinterval :
      Tendsto (fun r : ℝ => ∫ x in -r..r, G x) atTop (nhds (∫ x, G x)) :=
    intervalIntegral_tendsto_integral hG tendsto_neg_atTop_atBot tendsto_id
  have hprimNeg : Tendsto (fun r : ℝ => gaussianCDFProductPrimitive (-r))
      atTop (nhds 0) :=
    tendsto_gaussianCDFProductPrimitive_atBot.comp tendsto_neg_atTop_atBot
  have hRHS : Tendsto
      (fun r : ℝ => 2 * (∫ x in -r..r, G x) +
        gaussianCDFProductPrimitive r - gaussianCDFProductPrimitive (-r))
      atTop (nhds (2 * (∫ x, G x))) := by
    convert (tendsto_const_nhds.mul hGinterval).add
      tendsto_gaussianCDFProductPrimitive_atTop |>.sub hprimNeg using 1 <;> norm_num
  have hinterval : Tendsto (fun r : ℝ => ∫ x in -r..r, F x)
      atTop (nhds (2 * (∫ x, G x))) := by
    apply hRHS.congr'
    filter_upwards with r
    simpa [F, G] using
      (integral_standardNormalCDF_mul_one_sub_interval (-r) r).symm
  have hcont : Continuous F := by
    dsimp [F]
    exact continuous_standardNormalCDF.mul
      (continuous_const.sub continuous_standardNormalCDF)
  have hfi : ∀ r : ℝ, IntegrableOn F (Ioc (-r) r) := by
    intro r
    by_cases hr : -r ≤ r
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).mp
        (hcont.intervalIntegrable (-r) r)
    · rw [Ioc_eq_empty (not_lt.mpr (not_le.mp hr).le)]
      exact integrableOn_empty
  have hset : Tendsto (fun r : ℝ => ∫ x in Ioc (-r) r, F x)
      atTop (nhds (2 * (∫ x, G x))) := by
    apply hinterval.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    rw [intervalIntegral.integral_of_le (by linarith)]
  have hnonneg : 0 ≤ᵐ[volume] F := by
    filter_upwards with x
    exact mul_nonneg (ProbabilityTheory.cdf_nonneg _ x)
      (sub_nonneg.mpr (ProbabilityTheory.cdf_le_one _ x))
  have hcover : AECover volume atTop (fun r : ℝ => Ioc (-r) r) :=
    aecover_Ioc tendsto_neg_atTop_atBot tendsto_id
  have hwhole : (∫ x : ℝ, F x) = 2 * (∫ x : ℝ, G x) :=
    hcover.integral_eq_of_tendsto_of_nonneg_ae _ hnonneg hfi hset
  dsimp [F, G] at hwhole ⊢
  rw [hwhole, integral_standardGaussianPDF_sq]
  field_simp

/-- Consequently the Gaussian boundary-layer integral has the exact
coefficient required by Proposition 4.3, with no remaining Gaussian/Fubini
hypothesis. -/
theorem terminalBoundaryIntegral_eq_four_div_sqrt_pi_proved :
    (∫ y : ℝ, (1 - (2 * standardNormalCDF y - 1) ^ 2)) =
      4 / Real.sqrt Real.pi :=
  terminalBoundaryIntegral_eq_four_div_sqrt_pi
    integral_standardNormalCDF_mul_one_sub

end FRSB.ZeroTemperature.NoTerminalGap
