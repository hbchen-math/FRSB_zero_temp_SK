import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Appendix A: the `K`-average consequence

This file formalizes the deterministic integral step in the active text of
Appendix A, Proposition `prop:app-fixed-parameter`, immediately following
equation `eq:app-K-average`.
-/

namespace FRSB.ZeroTemperature.AppendixA

open intervalIntegral MeasureTheory

/-- **Appendix A, `eq:app-K-average` and the paragraph following
`eq:app-JB-positive`.**

For `B > 0`, if `J` is continuous, nonnegative, and nondecreasing on
`[0,B]`, and

`B K(B) = ∫₀ᴮ J(v) dv`,

then `0 ≤ K(B) ≤ J(B)`.  In the manuscript these inequalities yield
`K ≥ 0` and, using `J = K + B K_B`, also `K_B ≥ 0`.
-/
theorem K_nonnegative_and_le_endpoint_of_average
    {B KB : ℝ} (J : ℝ → ℝ)
    (hB : 0 < B)
    (hJcont : ContinuousOn J (Set.Icc 0 B))
    (hJnonneg : ∀ v ∈ Set.Icc (0 : ℝ) B, 0 ≤ J v)
    (hJmono : MonotoneOn J (Set.Icc 0 B))
    (haverage : B * KB = ∫ v in (0 : ℝ)..B, J v) :
    0 ≤ KB ∧ KB ≤ J B := by
  have hJcontu : ContinuousOn J (Set.uIcc 0 B) := by
    rwa [Set.uIcc_of_le hB.le]
  have hJint : IntervalIntegrable J volume 0 B :=
    hJcontu.intervalIntegrable
  have hzeroInt : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 B :=
    intervalIntegrable_const (c := (0 : ℝ)) (by simp)
  have hconstInt : IntervalIntegrable (fun _ : ℝ => J B) volume 0 B :=
    intervalIntegrable_const (c := J B) (by simp)
  have hint_nonneg : 0 ≤ ∫ v in (0 : ℝ)..B, J v := by
    have hmono := integral_mono_on hB.le hzeroInt hJint
      (fun v hv => hJnonneg v hv)
    simpa using hmono
  have hint_upper : (∫ v in (0 : ℝ)..B, J v) ≤ B * J B := by
    have hmono := integral_mono_on hB.le hJint hconstInt (fun v hv => by
      exact hJmono hv ⟨hB.le, le_rfl⟩ hv.2)
    simpa [intervalIntegral.integral_const] using hmono
  constructor <;> nlinarith

end FRSB.ZeroTemperature.AppendixA
