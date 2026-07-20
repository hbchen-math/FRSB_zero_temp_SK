import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

/-!
# Logarithmic-derivative identity

This file checks the pointwise quotient algebra in `eq:zt-r-H-identity`.
-/

namespace FRSB.ZeroTemperature

/-- Pointwise algebra behind
`H = r^2 - r_x` when `r = -Q_x / Q` and
`r_x = -(Q_xx * Q - Q_x^2) / Q^2`.
This is `eq:zt-r-H-identity`. -/
theorem curvatureRatio_eq_logSlope_sq_sub_deriv
    {Q Qx Qxx r rx : ℝ} (hQ : Q ≠ 0)
    (hr : r = -Qx / Q)
    (hrx : rx = -(Qxx * Q - Qx ^ 2) / Q ^ 2) :
    Qxx / Q = r ^ 2 - rx := by
  rw [hr, hrx]
  field_simp
  ring

end FRSB.ZeroTemperature
