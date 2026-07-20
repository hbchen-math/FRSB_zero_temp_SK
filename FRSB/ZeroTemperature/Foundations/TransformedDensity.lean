import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Transformed-density definitions

Foundational definitions for the function `Q` in `eq:zt-Q-def`.  This module
contains definitions only; paper-level propositions are placed in separate
files.
-/

namespace FRSB.ZeroTemperature

/-- Pointwise transformed density `Q = rho * exp (-gamma * u)` from
`eq:zt-Q-def`. -/
noncomputable def transformedDensity
    (rho u : ℝ → ℝ) (gamma : ℝ) (x : ℝ) : ℝ :=
  rho x * Real.exp (-gamma * u x)

end FRSB.ZeroTemperature
