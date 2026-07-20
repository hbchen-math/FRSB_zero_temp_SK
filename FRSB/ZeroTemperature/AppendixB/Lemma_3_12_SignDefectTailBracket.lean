import FRSB.ZeroTemperature.AppendixB.Lemma_3_12_UniformTailDriftBracket
import Mathlib.MeasureTheory.Function.AEMeasurableSequence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.GCongr

/-!
# Appendix B: the sign-defect tail bracket

This file continues Step 1 of the proof of `lem:zt-tails`.  It converts the bounded-drift event
inclusions into the two-sided estimate for the quantity
`2 P(Y < 0) + P(Y = 0)`, retaining the possible atom at zero exactly as in the manuscript.
-/

namespace FRSB.ZeroTemperature.AppendixB

open MeasureTheory Set

/-- Let `Y = x + Z + D`, where `D` is bounded by `A`.  The sign-defect mass
`2 μ{Y < 0} + μ{Y = 0}` lies between twice the corresponding shifted lower tails of `Z`.

This is the measure-theoretic step between the event inclusions in the proof of `lem:zt-tails`
and the Gaussian-tail estimate `eq:zt-B-Gaussian-bracket`. -/
theorem boundedDrift_signDefect_tail_bracket
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z D : Ω → ℝ) (x A : ℝ)
    (hY : Measurable (fun ω ↦ x + Z ω + D ω))
    (hD : ∀ ω, |D ω| ≤ A) :
    2 * μ {ω | Z ω < -x - A} ≤
        2 * μ {ω | x + Z ω + D ω < 0} +
          μ {ω | x + Z ω + D ω = 0} ∧
      2 * μ {ω | x + Z ω + D ω < 0} +
          μ {ω | x + Z ω + D ω = 0} ≤
        2 * μ {ω | Z ω ≤ -x + A} := by
  let Y : Ω → ℝ := fun ω ↦ x + Z ω + D ω
  have hbracket := boundedDrift_lowerTail_probability_bracket μ Z D x A hD
  have hleft : μ {ω | Z ω < -x - A} ≤ μ {ω | Y ω < 0} := by
    simpa only [Y] using hbracket.1
  have hright : μ {ω | Y ω ≤ 0} ≤ μ {ω | Z ω ≤ -x + A} := by
    simpa only [Y] using hbracket.2.2
  have hneg_meas : MeasurableSet {ω | Y ω < 0} := hY measurableSet_Iio
  have hzero_meas : MeasurableSet {ω | Y ω = 0} := hY (measurableSet_singleton 0)
  have hdisj : Disjoint {ω | Y ω < 0} {ω | Y ω = 0} := by
    rw [Set.disjoint_left]
    intro ω hneg hzero
    exact (ne_of_lt hneg) hzero
  have hunion : {ω | Y ω ≤ 0} = {ω | Y ω < 0} ∪ {ω | Y ω = 0} := by
    ext ω
    simp only [mem_setOf_eq, mem_union]
    exact le_iff_lt_or_eq
  have hmeasure : μ {ω | Y ω ≤ 0} = μ {ω | Y ω < 0} + μ {ω | Y ω = 0} := by
    rw [hunion, measure_union hdisj hzero_meas]
  constructor
  · calc
      2 * μ {ω | Z ω < -x - A} ≤ 2 * μ {ω | Y ω < 0} := by
        exact mul_le_mul_left' hleft 2
      _ ≤ 2 * μ {ω | Y ω < 0} + μ {ω | Y ω = 0} := le_add_right le_rfl
  · calc
      2 * μ {ω | Y ω < 0} + μ {ω | Y ω = 0}
          ≤ 2 * (μ {ω | Y ω < 0} + μ {ω | Y ω = 0}) := by
            rw [mul_add]
            apply add_le_add le_rfl
            calc
              μ {ω | Y ω = 0} = 1 * μ {ω | Y ω = 0} := by rw [one_mul]
              _ ≤ 2 * μ {ω | Y ω = 0} := mul_le_mul_right' (by norm_num) _
      _ = 2 * μ {ω | Y ω ≤ 0} := by rw [hmeasure]
      _ ≤ 2 * μ {ω | Z ω ≤ -x + A} := by
        exact mul_le_mul_left' hright 2

end FRSB.ZeroTemperature.AppendixB
