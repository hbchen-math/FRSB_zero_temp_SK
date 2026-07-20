import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.Linarith

/-!
# Appendix B: the bounded-drift event bracket

This is the deterministic probability comparison in Step 1 of the proof of
`lem:zt-tails` (Uniform tail estimates).  In the manuscript one takes `Z = W₁ - Wₜ` and lets
`D` be the time-integrated drift, whose absolute value is bounded by `A`.
-/

namespace FRSB.ZeroTemperature.AppendixB

open MeasureTheory Set

/-- If `Y = x + Z + D` and the perturbation `D` is bounded in absolute value by `A`, then the
lower-tail events for `Y` are bracketed by shifted lower-tail events for `Z`.  Consequently their
probabilities are bracketed in the same order.

This formalizes the displayed event inclusions immediately preceding
`eq:zt-B-Gaussian-bracket` in Appendix B, proof of `lem:zt-tails`, Step 1. -/
theorem boundedDrift_lowerTail_probability_bracket
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z D : Ω → ℝ) (x A : ℝ)
    (hD : ∀ ω, |D ω| ≤ A) :
    μ {ω | Z ω < -x - A} ≤
        μ {ω | x + Z ω + D ω < 0} ∧
      μ {ω | x + Z ω + D ω < 0} ≤
        μ {ω | x + Z ω + D ω ≤ 0} ∧
      μ {ω | x + Z ω + D ω ≤ 0} ≤
        μ {ω | Z ω ≤ -x + A} := by
  have hleft : {ω | Z ω < -x - A} ⊆ {ω | x + Z ω + D ω < 0} := by
    intro ω hω
    have hDupper : D ω ≤ A := (abs_le.mp (hD ω)).2
    simp only [mem_setOf_eq] at hω ⊢
    linarith
  have hmiddle : {ω | x + Z ω + D ω < 0} ⊆ {ω | x + Z ω + D ω ≤ 0} := by
    intro ω hω
    simp only [mem_setOf_eq] at hω ⊢
    exact le_of_lt hω
  have hright : {ω | x + Z ω + D ω ≤ 0} ⊆ {ω | Z ω ≤ -x + A} := by
    intro ω hω
    have hDlower : -A ≤ D ω := (abs_le.mp (hD ω)).1
    simp only [mem_setOf_eq] at hω ⊢
    linarith
  exact ⟨measure_mono hleft, measure_mono hmiddle, measure_mono hright⟩

end FRSB.ZeroTemperature.AppendixB
