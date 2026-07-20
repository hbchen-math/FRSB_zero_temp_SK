import FRSB.Paper.ExternalInputs
import FRSB.PositiveTemperature.EndpointAlgebra
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Theorem 1.2: quantitative endpoint control

This file formalizes the scalar assembly of `thm:finite-temperature` from the
endpoint identities and strict inequalities proved in the manuscript.  The
Parisi PDE and optimal-diffusion analysis enters through the explicit external
declaration `cited_positiveTemperatureEndpointData`; the downstream quantitative
argument is kernel-checked here.

The comments below retain the exact TeX labels from `my_paper.tex`.
-/

namespace FRSB.Paper

open Filter Topology
open FRSB.PositiveTemperature

noncomputable section

/-- The endpoint `q_beta` supplied by the external theorem
`thm:finite-temperature-structure`.  Values at `beta ≤ 1` are irrelevant to
the paper and are set to zero only so that the limit at infinity is expressed
for a function on all real inverse temperatures. -/
def qBetaTotal (β : ℝ) : ℝ :=
  if hβ : 1 < β then qBeta β hβ else 0

/-- The endpoint atom `c_beta` supplied by the external theorem
`thm:finite-temperature-structure`. -/
def cBetaTotal (β : ℝ) : ℝ :=
  if hβ : 1 < β then cBeta β hβ else 0

/-- The range of `q_beta` from `thm:finite-temperature-structure`. -/
theorem qBetaTotal_mem {β : ℝ} (hβ : 1 < β) :
    qBetaTotal β ∈ Set.Ioo (0 : ℝ) 1 := by
  simp only [qBetaTotal, dif_pos hβ]
  exact (lopatto_positiveTemperatureStructure β hβ).q_mem

/-- The range of `c_beta` from `thm:finite-temperature-structure`. -/
theorem cBetaTotal_mem {β : ℝ} (hβ : 1 < β) :
    cBetaTotal β ∈ Set.Ioo (0 : ℝ) 1 := by
  simp only [cBetaTotal, dif_pos hβ]
  exact (lopatto_positiveTemperatureStructure β hβ).c_mem

/-- `prop:ft-endpoint-quantitative` for one inverse temperature, including the
derived lower bound in the sentence following
`eq:intro-finite-endpoint-bounds`. -/
theorem prop_ft_endpoint_quantitative {β : ℝ} (hβ : 1 < β) :
    (1 : ℝ) / 3 < cBetaTotal β ∧
      (3 - cBetaTotal β) / (2 * β ^ 2) < 1 - qBetaTotal β ∧
      1 - qBetaTotal β < 2 / β ^ 2 ∧
      1 / β ^ 2 < 1 - qBetaTotal β := by
  let input := cited_positiveTemperatureEndpointData β hβ
  have hq : input.1.q = qBetaTotal β := by
    simpa only [qBetaTotal, dif_pos hβ] using input.2.1
  have hcEq : input.1.c = cBetaTotal β := by
    simpa only [cBetaTotal, dif_pos hβ] using input.2.2
  have hquant := endpoint_quantitative input.1
  rw [hq, hcEq] at hquant
  rcases hquant with ⟨hc, hlower, hupper⟩
  have hβsq : 0 < β ^ 2 := sq_pos_of_pos input.1.betaPos
  have hcLtOne : cBetaTotal β < 1 := (cBetaTotal_mem hβ).2
  have hderived : 1 / β ^ 2 < 1 - qBetaTotal β := by
    calc
      1 / β ^ 2 = 2 / (2 * β ^ 2) := by
        field_simp [ne_of_gt hβsq]
      _ < (3 - cBetaTotal β) / (2 * β ^ 2) := by
        exact (div_lt_div_iff_of_pos_right (mul_pos (by norm_num) hβsq)).2
          (by linarith)
      _ < 1 - qBetaTotal β := hlower
  exact ⟨hc, hlower, hupper, hderived⟩

/-- The endpoint gaps tend to zero.  This is the squeeze argument used for the
last assertion of `thm:finite-temperature`. -/
theorem endpoint_gap_tendsto_zero
    : Tendsto (fun β => 1 - qBetaTotal β) atTop (𝓝 0) := by
  have hbound : Tendsto (fun β : ℝ => 2 / β ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with β hβ
    exact sub_nonneg.mpr (qBetaTotal_mem hβ).2.le
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with β hβ
    exact (prop_ft_endpoint_quantitative hβ).2.2.1.le

/-- Exact Lean transcription of the conclusion of
`thm:finite-temperature` (Theorem 1.2).

The pointwise conclusion contains both bounds in
`eq:intro-finite-endpoint-bounds` and the stated consequence
`1 / β^2 < 1 - q_β`.  The last conjunct is the precise Lean form of
`lim_{β → ∞} q_β = 1`. -/
def Theorem1_2Conclusion : Prop :=
  (∀ β : ℝ, 1 < β →
    (1 : ℝ) / 3 < cBetaTotal β ∧
      (3 - cBetaTotal β) / (2 * β ^ 2) < 1 - qBetaTotal β ∧
      1 - qBetaTotal β < 2 / β ^ 2 ∧
      1 / β ^ 2 < 1 - qBetaTotal β) ∧
    Tendsto qBetaTotal atTop (𝓝 1)

/-- Theorem 1.2, with its cited analytic inputs declared explicitly in
`ExternalInputs.lean`.  No endpoint-witness hypothesis remains. -/
theorem theorem1_2 : Theorem1_2Conclusion := by
  constructor
  · intro β hβ
    exact prop_ft_endpoint_quantitative hβ
  · have hgap := endpoint_gap_tendsto_zero
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    simpa only [sub_sub_cancel, sub_zero] using
      (hone.sub hgap)

/-- Backwards-compatible name for the final scalar assembly. -/
theorem theorem1_2_assembly : Theorem1_2Conclusion := theorem1_2

end

end FRSB.Paper
