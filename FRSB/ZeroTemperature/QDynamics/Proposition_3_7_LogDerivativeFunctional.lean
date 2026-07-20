import FRSB.ZeroTemperature.QDynamics.Proposition_3_7_LogDerivativeIdentity
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Functional logarithmic-derivative identity for Proposition 3.7

This file proves the differentiable-function form of
`eq:zt-r-H-identity`, used in paper Proposition 3.7.
-/

namespace FRSB.ZeroTemperature

/-- Let `Qx` represent the first derivative of a nonzero function `Q` and let
`Qxx` be its derivative at `x`.  Then the logarithmic slope
`r = -Qx / Q` has the derivative asserted in `eq:zt-r-H-identity`, and hence
`Qxx / Q = r^2 - r_x` at `x`. -/
theorem hasDerivAt_logSlope_and_curvatureIdentity
    {Q Qx : ℝ → ℝ} {x Qxx : ℝ}
    (hQ : HasDerivAt Q (Qx x) x)
    (hQx : HasDerivAt Qx Qxx x)
    (hQne : Q x ≠ 0) :
    HasDerivAt (fun y => -Qx y / Q y)
      (-(Qxx * Q x - Qx x ^ 2) / Q x ^ 2) x ∧
      Qxx / Q x = (-Qx x / Q x) ^ 2 -
        (-(Qxx * Q x - Qx x ^ 2) / Q x ^ 2) := by
  constructor
  · convert hQx.neg.div hQ hQne using 1 <;>
      simp only [Pi.neg_apply] <;> ring
  · exact curvatureRatio_eq_logSlope_sq_sub_deriv hQne rfl rfl

end FRSB.ZeroTemperature
