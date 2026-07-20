import FRSB.ZeroTemperature.QDynamics.Lemma_3_5_JumpRule

/-!
# Lemma 3.5: jump rule

The paper's jump identity is an equality of spatial functions.  This module
lifts the pointwise transformed-density calculation to exactly that level.
-/

namespace FRSB.ZeroTemperature

/-- The jump part of `lem:zt-Q-dynamics` as an equality of functions on
`ℝ`.  No regularity hypothesis is needed once the same `rho` and `u` are used
on the two sides of the jump. -/
theorem lemma_3_5_transformedDensity_jump
    (rho u : ℝ → ℝ) (gammaLeft delta : ℝ) :
    (fun x => transformedDensity rho u (gammaLeft + delta) x) =
      fun x => Real.exp (-delta * u x) *
        transformedDensity rho u gammaLeft x := by
  funext x
  exact transformedDensity_jump_rule rho u gammaLeft delta x

end FRSB.ZeroTemperature
