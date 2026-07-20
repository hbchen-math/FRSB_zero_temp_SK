import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Heat cancellation for the transformed density

This file proves the pointwise algebraic cancellation in `eq:zt-Q-heat`.
The analytic facts that the displayed quantities are derivatives and satisfy
the Parisi and Fokker--Planck equations remain separate obligations.
-/

namespace FRSB.ZeroTemperature

/-- The Fokker--Planck equation and the Parisi PDE cancel after the
transformation `Q = rho * exp (-m * u)`, leaving `Q_t = Q_xx / 2`.

This is the exact pointwise algebra used in the constant-coefficient part of
`lem:zt-Q-dynamics` (`eq:zt-Q-heat`). -/
theorem transformedDensity_heat_cancellation
    {m u ux uxx ut rho rhox rhoxx rhot Qt Qxx : ℝ}
    (hrhot : rhot = (1 / 2 : ℝ) * rhoxx - m * (uxx * rho + ux * rhox))
    (hut : ut = -(1 / 2 : ℝ) * (uxx + m * ux ^ 2))
    (hQt : Qt = Real.exp (-m * u) * (rhot - m * rho * ut))
    (hQxx : Qxx = Real.exp (-m * u) *
      (rhoxx - 2 * m * ux * rhox - m * uxx * rho + m ^ 2 * ux ^ 2 * rho)) :
    Qt = (1 / 2 : ℝ) * Qxx := by
  rw [hQt, hQxx, hrhot, hut]
  ring

end FRSB.ZeroTemperature
