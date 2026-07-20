import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Proposition 4.4: interval masses from a smooth density

This file formalizes the fundamental-theorem-of-calculus step behind
`d gamma(t) = gamma'(t) dt` in `eq:zt-smoothness-conclusion`.
-/

namespace FRSB.ZeroTemperature.Smoothness

open MeasureTheory Set intervalIntegral

/-- If `rho` is a continuous nonnegative derivative of `gamma` on `[a,b]`,
then the Stieltjes interval increment equals the Lebesgue mass of `rho` on
`(a,b]`.  This is the interval-level content of the measure identity in
paper Proposition 4.4. -/
theorem stieltjesIntervalIncrement_eq_lintegral_density
    {gamma rho : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hgamma : ContinuousOn gamma (Icc a b))
    (hrho : ContinuousOn rho (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt gamma (rho x) x)
    (hrho_nonnegative : ∀ x ∈ Ioc a b, 0 ≤ rho x) :
    ENNReal.ofReal (gamma b - gamma a) =
      ∫⁻ x in Ioc a b, ENNReal.ofReal (rho x) := by
  have hcontu : ContinuousOn rho (uIcc a b) := by
    rwa [uIcc_of_le hab]
  have hint : IntervalIntegrable rho volume a b :=
    hcontu.intervalIntegrable
  have hFTC : ∫ x in a..b, rho x = gamma b - gamma a :=
    integral_eq_sub_of_hasDerivAt_of_le hab hgamma hderiv hint
  have hintSet : IntegrableOn rho (Ioc a b) := by
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hint).mono_set
      Ioc_subset_Icc_self
  have hnonnegative : 0 ≤ᵐ[volume.restrict (Ioc a b)] rho :=
    (ae_restrict_mem measurableSet_Ioc).mono hrho_nonnegative
  rw [← hFTC, integral_of_le hab]
  exact ofReal_integral_eq_lintegral_ofReal hintSet hnonnegative

end FRSB.ZeroTemperature.Smoothness
