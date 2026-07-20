import FRSB.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Proposition 4.2: from absence of internal gaps to interval closure

The paper states Proposition 4.2 by excluding an open component of the
complement of the Stieltjes support.  `SupportAssembly` uses the equivalent
order-convex formulation `FRSB.IntervalClosed`.  This file proves the precise
bridge, including the topological closedness enjoyed by a measure support.
-/

namespace FRSB.ZeroTemperature.NoInternalGap

/-- **Set-theoretic bridge for paper Proposition 4.2.**

Let `S ⊆ [0,1)` be closed.  Assume there is no empty open interval around a
point strictly between two points of `S`: equivalently, every metric
neighborhood of such a point meets `S`.  Then `S` contains every point between
any two of its points, which is exactly the `FRSB.IntervalClosed S` input used
by `SupportAssembly`.

The subset hypothesis records the paper's ambient half-open interval.  It is
not needed for the purely order-topological implication. -/
theorem intervalClosed_of_noInternalEmptyInterval
    {S : Set ℝ}
    (_hunit : S ⊆ Set.Ico (0 : ℝ) 1)
    (hclosed : IsClosed S)
    (hnoEmpty : ∀ ⦃a b x : ℝ⦄, a ∈ S → b ∈ S → a < x → x < b →
      ∀ ε > 0, ∃ y ∈ S, dist x y < ε) :
    FRSB.IntervalClosed S := by
  intro a b x ha hb hax hxb
  rcases hax.eq_or_lt with rfl | hax'
  · exact ha
  rcases hxb.eq_or_lt with rfl | hxb'
  · exact hb
  have hxclosure : x ∈ closure S := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    exact hnoEmpty ha hb hax' hxb' ε hε
  rwa [hclosed.closure_eq] at hxclosure

end FRSB.ZeroTemperature.NoInternalGap
