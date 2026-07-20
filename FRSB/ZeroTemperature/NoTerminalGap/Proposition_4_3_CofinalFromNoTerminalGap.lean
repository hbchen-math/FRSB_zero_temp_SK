import FRSB.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Monotone

/-!
# Proposition 4.3: from terminal-gap exclusion to cofinality

The manuscript states Proposition `prop:zt-no-terminal-gap` as the nonexistence of a last support
point followed by an empty interval up to one.  The final theorem uses the equivalent cofinality
formulation.  This file proves the passage between those formulations, using the relative closedness
of a measure support.
-/

namespace FRSB.ZeroTemperature.NoTerminalGap

open Set

/-- A nonempty set below one that is relatively closed below one and has no terminal gap is cofinal
at one.

The hypothesis `closedBelowOne` is the ambient-real formulation of relative closedness in `[0,1)`:
every closure point strictly below one belongs to the set.  The hypothesis `noTerminalGap` is the
literal conclusion of Proposition `prop:zt-no-terminal-gap`. -/
theorem cofinalAtOne_of_noTerminalGap
    {S : Set ℝ}
    (hne : S.Nonempty)
    (closedBelowOne : ∀ ⦃a : ℝ⦄, a < 1 → a ∈ closure S → a ∈ S)
    (noTerminalGap :
      ¬ ∃ a : ℝ, a < 1 ∧ a ∈ S ∧ ∀ t : ℝ, a < t → t < 1 → t ∉ S) :
    FRSB.CofinalAtOne S := by
  intro x hx
  by_contra hcofinal
  have hbelow : ∀ y ∈ S, y < x := by
    intro y hy
    exact lt_of_not_ge fun hxy ↦ hcofinal ⟨y, hy, hxy⟩
  have hbdd : BddAbove S := ⟨x, fun y hy ↦ (hbelow y hy).le⟩
  let a := sSup S
  have ha_le_x : a ≤ x := csSup_le hne fun y hy ↦ (hbelow y hy).le
  have ha_lt_one : a < 1 := ha_le_x.trans_lt hx
  have ha_closure : a ∈ closure S := csSup_mem_closure hne hbdd
  have ha_mem : a ∈ S := closedBelowOne ha_lt_one ha_closure
  apply noTerminalGap
  refine ⟨a, ha_lt_one, ha_mem, ?_⟩
  intro t hat _ht1 htS
  exact (not_lt_of_ge (le_csSup hbdd htS)) hat

end FRSB.ZeroTemperature.NoTerminalGap
