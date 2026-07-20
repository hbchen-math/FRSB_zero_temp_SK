import FRSB.ZeroTemperature.Foundations.TransformedDensity

/-!
# Jump rule for the transformed density

This file formalizes `eq:zt-Q-jump` as a standalone proposition.
-/

namespace FRSB.ZeroTemperature

/-- If the right-continuous coefficient jumps from `gammaLeft` to
`gammaLeft + delta`, then the transformed density is multiplied by
`exp (-delta * u)`.  This is `eq:zt-Q-jump`. -/
theorem transformedDensity_jump_rule
    (rho u : ℝ → ℝ) (gammaLeft delta x : ℝ) :
    transformedDensity rho u (gammaLeft + delta) x =
      Real.exp (-delta * u x) *
        transformedDensity rho u gammaLeft x := by
  unfold transformedDensity
  rw [show -(gammaLeft + delta) * u x =
      (-delta * u x) + (-gammaLeft * u x) by ring]
  rw [Real.exp_add]
  ring

end FRSB.ZeroTemperature
