import FRSB.Basic
import FRSB.ZeroTemperature.Crossing.Proposition_4_1_CrossingRule
import FRSB.ZeroTemperature.NoInternalGap.Proposition_4_2_GapContradiction
import FRSB.ZeroTemperature.NoTerminalGap.Proposition_4_3_TerminalSquareRootContradiction

/-!
# Selected analytic inputs and derived gap exclusions

Theorem 1.3 must not receive `no internal gap` or `no terminal gap` as opaque
fields.  This file instead records candidate-wise analytic data: if a gap is
alleged, the analytic chain supplies the functions and identities appearing in
Propositions 4.1--4.3.  The gap conclusions are then derived in Lean by the
already formalized deterministic contradictions.
-/

namespace FRSB.ZeroTemperature

open MeasureTheory Set
open scoped Interval

namespace NoInternalGap

/-- Exact Proposition 4.2 data attached to an alleged internal gap. -/
structure ContradictionData (a b : ℝ) where
  c : ℝ
  Γa : ℝ
  Γb : ℝ
  Γpa : ℝ
  f : ℝ → ℝ
  hab : a < b
  hac : a < c
  hcb : c < b
  f_continuous : ContinuousOn f (uIcc a b)
  negative_before_crossing : ∀ t, a < t → t < c → f t < 0
  positive_after_crossing : ∀ t, c < t → t < b → 0 < f t
  weighted_second_zero :
    ∫ t in a..b, (t - a) * (b - t) * f t = 0
  first_moment : Γb - Γa - (b - a) * Γpa =
    ∫ t in a..b, (b - t) * f t
  endpoint_increment : Γb - Γa = b - a
  left_slope_le_one : Γpa ≤ 1

/-- The Proposition 4.2 deterministic chain rules out the supplied data. -/
theorem ContradictionData.false {a b : ℝ} (d : ContradictionData a b) : False :=
  noInternalGap_of_weightedCrossing d.f d.hab d.hac d.hcb
    d.f_continuous d.negative_before_crossing d.positive_after_crossing
    d.weighted_second_zero d.first_moment d.endpoint_increment
    d.left_slope_le_one

/-- Candidate-wise analytic output for internal gaps.

The field does not assert interval-closedness.  It says that any specific
failure of interval-closedness produces the endpoint, crossing-sign, and
integral data computed in the Proposition 4.1--4.2 analytic chain. -/
structure AnalyticInputs (S : Set ℝ) where
  contradictionData : ∀ ⦃a b x : ℝ⦄,
    a ∈ S → b ∈ S → a ≤ x → x ≤ b → x ∉ S → ContradictionData a b

/-- Derive `no internal gap` rather than accepting it as a final input. -/
theorem intervalClosed_of_analyticInputs {S : Set ℝ}
    (h : AnalyticInputs S) : FRSB.IntervalClosed S := by
  intro a b x ha hb hax hxb
  by_contra hx
  exact (h.contradictionData ha hb hax hxb hx).false

end NoInternalGap

namespace NoTerminalGap

/-- Exact Step 4 data attached to an alleged terminal support gap. -/
structure ContradictionData where
  Gamma : ℝ → ℝ
  c : ℝ
  c_pos : 0 < c
  Gamma_continuous : ContinuousOn Gamma (Icc 0 1)
  Gamma_one : Gamma 1 = 1
  squareRootLower :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      c / 2 * √ε ≤ 1 - Gamma (1 - ε)
  variational_nonnegative :
    ∀ q : ℝ, 0 ≤ q → q < 1 →
      0 ≤ ∫ t in q..1, (Gamma t - t)

/-- The terminal square-root estimate contradicts the variational sign. -/
theorem ContradictionData.false (d : ContradictionData) : False :=
  terminalSquareRoot_contradicts_nonnegative_integral
    d.Gamma d.c d.c_pos d.Gamma_continuous d.Gamma_one
    d.squareRootLower d.variational_nonnegative

/-- Candidate-wise analytic output for terminal gaps. -/
structure AnalyticInputs (S : Set ℝ) where
  contradictionData : ∀ ⦃a : ℝ⦄,
    a < 1 → a ∈ S →
      (∀ t : ℝ, a < t → t < 1 → t ∉ S) → ContradictionData

/-- Derive the literal Proposition 4.3 terminal-gap exclusion. -/
theorem noTerminalGap_of_analyticInputs {S : Set ℝ}
    (h : AnalyticInputs S) :
    ¬ ∃ a : ℝ, a < 1 ∧ a ∈ S ∧
      ∀ t : ℝ, a < t → t < 1 → t ∉ S := by
  rintro ⟨a, ha1, haS, hgap⟩
  exact (h.contradictionData ha1 haS hgap).false

end NoTerminalGap

end FRSB.ZeroTemperature
