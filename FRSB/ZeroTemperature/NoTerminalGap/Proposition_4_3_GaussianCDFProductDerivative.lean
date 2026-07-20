import FRSB.ZeroTemperature.NoTerminalGap.Proposition_4_3_GaussianCDFDerivative

/-!
# Proposition 4.3: differential Gaussian CDF product identity

This file proves the exact pointwise calculus used in the manuscript's
integration-by-parts evaluation of the Gaussian boundary factor.  No
whole-line integrability or boundary limit is assumed here.
-/

namespace FRSB.ZeroTemperature.NoTerminalGap

open ProbabilityTheory Real

/-- The derivative of `Phi * (1 - Phi)`. -/
theorem hasDerivAt_standardNormalCDF_mul_one_sub (x : ℝ) :
    HasDerivAt
      (fun y => standardNormalCDF y * (1 - standardNormalCDF y))
      (gaussianPDFReal 0 1 x * (1 - 2 * standardNormalCDF x)) x := by
  have hPhi := hasDerivAt_standardNormalCDF x
  convert hPhi.mul ((hasDerivAt_const x (1 : ℝ)).sub hPhi) using 1 <;>
    simp only [Pi.sub_apply, Pi.mul_apply, id_eq] <;> ring

/-- The standard Gaussian density satisfies `phi' = -x phi`. -/
theorem hasDerivAt_standardGaussianPDF (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1)
      (-x * gaussianPDFReal 0 1 x) x := by
  have hexponent : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
    convert (((hasDerivAt_id x).pow 2).neg.div_const 2) using 1 <;>
      simp only [id_eq] <;> ring
  have hexp := hexponent.exp
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, sub_zero, mul_one]
  convert hexp.const_mul (√(2 * Real.pi))⁻¹ using 1 <;> ring

/-- The pointwise integration-by-parts primitive:

`d/dx [x Phi(1-Phi) + phi(1-2 Phi)] = Phi(1-Phi) - 2 phi^2`.

Integrating this identity over the real line and proving that the primitive
vanishes at both ends reduces the CDF product integral to twice the density
square integral. -/
theorem hasDerivAt_standardNormalCDF_product_primitive (x : ℝ) :
    HasDerivAt
      (fun y =>
        y * (standardNormalCDF y * (1 - standardNormalCDF y)) +
          gaussianPDFReal 0 1 y * (1 - 2 * standardNormalCDF y))
      (standardNormalCDF x * (1 - standardNormalCDF x) -
        2 * (gaussianPDFReal 0 1 x) ^ 2) x := by
  have hPhi := hasDerivAt_standardNormalCDF x
  have hproduct := hasDerivAt_standardNormalCDF_mul_one_sub x
  have hpdf := hasDerivAt_standardGaussianPDF x
  have htwoPhi : HasDerivAt (fun y => 1 - 2 * standardNormalCDF y)
      (-2 * gaussianPDFReal 0 1 x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub (hPhi.const_mul 2) using 1 <;> ring
  convert ((hasDerivAt_id x).mul hproduct).add (hpdf.mul htwoPhi) using 1 <;>
    simp only [Pi.add_apply, Pi.mul_apply, id_eq] <;> ring

end FRSB.ZeroTemperature.NoTerminalGap
