import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Proposition 4.3: dominated convergence in the terminal boundary layer

This file isolates the dominated-convergence step immediately before
`eq:zt-terminal-square-root`.  The parameter `epsilon` tends to zero from the right, and `y` is the
rescaled coordinate in the change of variables `x = sqrt epsilon * y`.
-/

namespace FRSB.ZeroTemperature.NoTerminalGap

open Filter MeasureTheory Set Topology

/-- Pointwise convergence of the rescaled density and slope, together with a common integrable
dominator, gives convergence of the rescaled terminal-deficit integral.

In the manuscript, `rho epsilon y = rho_(1-epsilon)(sqrt epsilon * y)`, `B epsilon y` is
`B_epsilon(y)`, `rhoOne` is `rho_1(0)`, and `b y = 2 phi(y) - 1`. -/
theorem tendsto_terminalDeficitIntegral_of_dominated
    (rho B : ℝ → ℝ → ℝ) (rhoOne : ℝ) (b bound : ℝ → ℝ)
    (hrho : ∀ y, Tendsto (fun ε ↦ rho ε y) (nhdsWithin 0 (Ioi 0)) (nhds rhoOne))
    (hB : ∀ y, Tendsto (fun ε ↦ B ε y) (nhdsWithin 0 (Ioi 0)) (nhds (b y)))
    (hmeas : ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
      AEStronglyMeasurable (fun y ↦ rho ε y * (1 - (B ε y) ^ 2)) volume)
    (hbound : ∀ᶠ ε in nhdsWithin 0 (Ioi 0), ∀ᵐ y ∂volume,
      ‖rho ε y * (1 - (B ε y) ^ 2)‖ ≤ bound y)
    (hbound_integrable : Integrable bound) :
    Tendsto
      (fun ε ↦ ∫ y, rho ε y * (1 - (B ε y) ^ 2))
      (nhdsWithin 0 (Ioi 0))
      (nhds (rhoOne * ∫ y, (1 - (b y) ^ 2))) := by
  have hpoint : ∀ᵐ y ∂volume,
      Tendsto (fun ε ↦ rho ε y * (1 - (B ε y) ^ 2))
        (nhdsWithin 0 (Ioi 0)) (nhds (rhoOne * (1 - (b y) ^ 2))) := by
    filter_upwards with y
    exact (hrho y).mul (tendsto_const_nhds.sub ((hB y).pow 2))
  have hdc := tendsto_integral_filter_of_dominated_convergence
    bound hmeas hbound hbound_integrable hpoint
  simpa only [integral_const_mul] using hdc

end FRSB.ZeroTemperature.NoTerminalGap
