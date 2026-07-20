import FRSB.Paper.Definitions
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Proposition 4.3: relative closedness of the support image

The Stieltjes support is closed in the half-open time domain.  This file
proves that its image in the real line therefore contains each of its closure
points that lies strictly below one.  This is the topological input needed to
turn the literal statement of `prop:zt-no-terminal-gap` into cofinality.
-/

namespace FRSB.ZeroTemperature.NoTerminalGap

open Set
open FRSB.Paper

/-- If `S` is closed in `[0,1)`, then its ambient-real image is relatively
closed at every point strictly below one. -/
theorem image_closedBelowOne_of_isClosed
    {S : Set UnitHalfOpen} (hS : IsClosed S) {a : ℝ}
    (ha1 : a < 1) (ha : a ∈ closure (Subtype.val '' S)) :
    a ∈ Subtype.val '' S := by
  have himage : Subtype.val '' S ⊆ Set.Icc (0 : ℝ) 1 := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x.property.1, x.property.2.le⟩
  have haIcc : a ∈ Set.Icc (0 : ℝ) 1 :=
    (closure_minimal himage isClosed_Icc) ha
  let a' : UnitHalfOpen := ⟨a, haIcc.1, ha1⟩
  have ha'_closure : a' ∈ closure S := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨y, hy, hdist⟩ := (Metric.mem_closure_iff.mp ha) ε hε
    obtain ⟨y', hy'S, rfl⟩ := hy
    exact ⟨y', hy'S, by simpa using hdist⟩
  have ha'S : a' ∈ S := by
    rw [hS.closure_eq] at ha'_closure
    exact ha'_closure
  exact ⟨a', ha'S, rfl⟩

end FRSB.ZeroTemperature.NoTerminalGap
