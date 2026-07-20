import Mathlib

/-!
# Appendix A, Lemma A.2: spatial second-derivative sign

This file formalizes the second-derivative test needed at the spatial slice
minimum in the proof of `lem:app-comparison`.
-/

namespace FRSB.ZeroTemperature.AppendixA

open Filter Topology

/-- **Active Appendix A, Lemma `lem:app-comparison`: spatial second
derivative.**

The hypothesis `hsecond` is the Peano form of the explicit second derivative
witness at `B`; `hminimum` is the punctured-neighborhood form of spatial local
minimality.  If the first derivative vanishes, the second derivative is
nonnegative. -/
theorem spatialSecondDerivative_nonnegative_at_localMinimum
    {f : ℝ → ℝ} {B fB wB wBB : ℝ}
    (hfB : f B = fB)
    (hfirst : wB = 0)
    (hminimum : ∀ᶠ h in 𝓝[≠] (0 : ℝ), fB ≤ f (B + h))
    (hsecond : Tendsto
      (fun h => (f (B + h) - fB - wB * h) / h ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (wBB / 2))) :
    0 ≤ wBB := by
  have hquotient : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      0 ≤ (f (B + h) - fB - wB * h) / h ^ 2 := by
    filter_upwards [hminimum, self_mem_nhdsWithin] with h hmin hne
    rw [hfirst, zero_mul, sub_zero]
    exact div_nonneg (sub_nonneg.mpr hmin) (sq_nonneg h)
  have hhalf : 0 ≤ wBB / 2 := ge_of_tendsto hsecond hquotient
  linarith

end FRSB.ZeroTemperature.AppendixA
