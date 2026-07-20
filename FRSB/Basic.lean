import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Common definitions

The formalization refers to manuscript results by their LaTeX labels rather
than by section or equation numbers. This makes the Lean sources insensitive
to later cosmetic changes in the manuscript.
-/

namespace FRSB

noncomputable section

/-- The zero-temperature support claimed in `thm:zero-temperature`. -/
def unitInterior : Set ℝ := Set.Ico 0 1

/-- A set contains every point lying between any two of its points. -/
def IntervalClosed (S : Set ℝ) : Prop :=
  ∀ ⦃a b x : ℝ⦄, a ∈ S → b ∈ S → a ≤ x → x ≤ b → x ∈ S

/-- The set has points arbitrarily far to the right below the endpoint one. -/
def CofinalAtOne (S : Set ℝ) : Prop :=
  ∀ ⦃x : ℝ⦄, x < 1 → ∃ y ∈ S, x ≤ y

end

end FRSB
