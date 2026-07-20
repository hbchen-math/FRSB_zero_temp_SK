import FRSB.ZeroTemperature.NoTerminalGap.Proposition_4_3_GaussianCDFProductDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Proposition 4.3: Gaussian CDF product on a finite interval

This integrates the exact primitive identity on an arbitrary finite interval.
The whole-line result will follow once the boundary primitive is shown to
vanish at both infinities.
-/

namespace FRSB.ZeroTemperature.NoTerminalGap

open MeasureTheory ProbabilityTheory Real

/-- Write the primitive used in the Gaussian CDF integration-by-parts step. -/
noncomputable def gaussianCDFProductPrimitive (x : ℝ) : ℝ :=
  x * (standardNormalCDF x * (1 - standardNormalCDF x)) +
    gaussianPDFReal 0 1 x * (1 - 2 * standardNormalCDF x)

/-- Exact finite-interval identity:

`∫_a^b Phi(1-Phi) = 2 ∫_a^b phi^2 + H(b) - H(a)`.

There is no boundary-limit assumption in this theorem. -/
theorem integral_standardNormalCDF_mul_one_sub_interval (a b : ℝ) :
    (∫ x in a..b, standardNormalCDF x * (1 - standardNormalCDF x)) =
      2 * (∫ x in a..b, (gaussianPDFReal 0 1 x) ^ 2) +
        gaussianCDFProductPrimitive b - gaussianCDFProductPrimitive a := by
  let PhiProduct : ℝ → ℝ := fun x =>
    standardNormalCDF x * (1 - standardNormalCDF x)
  let phiSq : ℝ → ℝ := fun x => (gaussianPDFReal 0 1 x) ^ 2
  have hphi : Continuous (gaussianPDFReal 0 1) :=
    continuous_iff_continuousAt.2 fun x =>
      (hasDerivAt_standardGaussianPDF x).continuousAt
  have hPhiProduct : Continuous PhiProduct := by
    dsimp [PhiProduct]
    exact continuous_standardNormalCDF.mul
      (continuous_const.sub continuous_standardNormalCDF)
  have hphiSq : Continuous phiSq := by
    dsimp [phiSq]
    fun_prop
  have hderiv : ∀ x,
      HasDerivAt gaussianCDFProductPrimitive (PhiProduct x - 2 * phiSq x) x := by
    intro x
    exact hasDerivAt_standardNormalCDF_product_primitive x
  have hFTC :
      (∫ x in a..b, PhiProduct x - 2 * phiSq x) =
        gaussianCDFProductPrimitive b - gaussianCDFProductPrimitive a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hderiv x)
      ((hPhiProduct.sub (hphiSq.const_mul 2)).intervalIntegrable a b)
  rw [intervalIntegral.integral_sub
      (hPhiProduct.intervalIntegrable a b)
      ((hphiSq.const_mul 2).intervalIntegrable a b),
    intervalIntegral.integral_const_mul] at hFTC
  dsimp [PhiProduct, phiSq] at hFTC ⊢
  linarith

end FRSB.ZeroTemperature.NoTerminalGap
