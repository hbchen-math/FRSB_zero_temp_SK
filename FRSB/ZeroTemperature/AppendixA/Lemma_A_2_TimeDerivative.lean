import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.OrderClosed

/-!
# Appendix A, Lemma A.2: terminal-time derivative sign

This file formalizes the one-sided time calculus needed when a compact-strip
minimum occurs at the terminal time of the strip.
-/

namespace FRSB.ZeroTemperature.AppendixA

open Filter Set Topology

/-- At a minimum approached from earlier times, a certified left derivative
is nonpositive.

Applied to the time slice of the exponentially transformed solution in
`lem:app-comparison`, this is the missing `w_r ≤ 0` condition when the global
minimum occurs at the terminal time `R`. -/
theorem timeDerivative_nonpositive_at_terminalMinimum
    {f : ℝ → ℝ} {R fR wr : ℝ}
    (hminimum : ∀ᶠ h in 𝓝[<] (0 : ℝ), fR ≤ f (R + h))
    (hderiv : Tendsto (fun h => (f (R + h) - fR) / h)
      (𝓝[<] (0 : ℝ)) (𝓝 wr)) :
    wr ≤ 0 := by
  have hquotient : ∀ᶠ h in 𝓝[<] (0 : ℝ),
      (f (R + h) - fR) / h ≤ 0 := by
    filter_upwards [hminimum, self_mem_nhdsWithin] with h hmin hh
    exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hmin) hh.le
  exact le_of_tendsto hderiv hquotient

end FRSB.ZeroTemperature.AppendixA
