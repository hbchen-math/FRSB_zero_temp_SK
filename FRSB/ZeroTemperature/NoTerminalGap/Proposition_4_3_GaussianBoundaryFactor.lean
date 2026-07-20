import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring

/-!
# Proposition 4.3: algebraic extraction of the Gaussian boundary factor

The paper's `phi` is represented by the CDF of Mathlib's standard real Gaussian measure.  This
file isolates the exact algebraic passage from the Gaussian/Fubini integral to the coefficient in
`eq:zt-terminal-square-root`.
-/

namespace FRSB.ZeroTemperature.NoTerminalGap

open MeasureTheory ProbabilityTheory

/-- The standard-normal distribution function used in the manuscript. -/
noncomputable def standardNormalCDF : ℝ → ℝ :=
  cdf (gaussianReal 0 1)

/-- Once the Gaussian/Fubini calculation gives
`integral phi(y) (1-phi(y)) = 1/sqrt pi`, the boundary-layer integral is exactly `4/sqrt pi`.

The hypothesis is displayed separately to make the remaining probability/Fubini dependency
explicit rather than hiding it as an axiom. -/
theorem terminalBoundaryIntegral_eq_four_div_sqrt_pi
    (hGaussianFubini :
      (∫ y : ℝ, standardNormalCDF y * (1 - standardNormalCDF y)) = 1 / √Real.pi) :
    (∫ y : ℝ, (1 - (2 * standardNormalCDF y - 1) ^ 2)) = 4 / √Real.pi := by
  have hpoint : ∀ y : ℝ,
      1 - (2 * standardNormalCDF y - 1) ^ 2 =
        4 * (standardNormalCDF y * (1 - standardNormalCDF y)) := by
    intro y
    ring
  calc
    (∫ y : ℝ, (1 - (2 * standardNormalCDF y - 1) ^ 2)) =
        ∫ y : ℝ, 4 * (standardNormalCDF y * (1 - standardNormalCDF y)) := by
          apply integral_congr_ae
          filter_upwards with y
          exact hpoint y
    _ = 4 * ∫ y : ℝ, standardNormalCDF y * (1 - standardNormalCDF y) := by
      rw [integral_const_mul]
    _ = 4 / √Real.pi := by
      rw [hGaussianFubini]
      ring

end FRSB.ZeroTemperature.NoTerminalGap
