import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Order.Basic

/-!
# Proposition 4.4: identifying the continuous representative

The smoothness proof first obtains an almost-everywhere formula for the order parameter and then
uses right continuity to identify it with the continuous quotient at every time.  The theorem below
isolates the topological core of that argument.  Its final hypothesis says that equality points can
be found arbitrarily close from the right; for Lebesgue-a.e. equality on a real interval this follows
because every nonempty right-hand interval has positive Lebesgue measure.
-/

namespace FRSB.ZeroTemperature.Smoothness

open Filter Set Topology

/-- A right-continuous function agrees everywhere with a continuous representative if their
equality set approaches every point from the right.

This is the representative-identification step used in Proposition `prop:zt-smoothness`: after the
quotient formula is known almost everywhere, right continuity of the order parameter and continuity
of the quotient upgrade it to a pointwise identity. -/
theorem rightContinuous_eq_continuous_of_frequently_eq
    {X Y : Type*} [TopologicalSpace X] [Preorder X] [TopologicalSpace Y] [T2Space Y]
    {f g : X → Y}
    (hf : ∀ x, ContinuousWithinAt f (Ici x) x)
    (hg : Continuous g)
    (hfg : ∀ x, ∃ᶠ y in nhdsWithin x (Ici x), f y = g y) :
    f = g := by
  funext x
  exact tendsto_nhds_unique_of_frequently_eq (hf x) hg.continuousAt.continuousWithinAt (hfg x)

end FRSB.ZeroTemperature.Smoothness
