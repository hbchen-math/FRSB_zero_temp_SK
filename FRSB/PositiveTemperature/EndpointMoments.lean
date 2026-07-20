import FRSB.PositiveTemperature.EndpointCovariance

/-!
# Endpoint moments from the diffusion law

This file records the endpoint law semantically and derives the first endpoint
identity from self-consistency.  The remaining Itô inputs will supply the
second-moment and balance identities downstream.
-/

namespace FRSB.PositiveTemperature

open Filter MeasureTheory

noncomputable section

/-- Even endpoint moments of `C = sech² X`. -/
def endpointMoment (law : Measure ℝ) (n : ℕ) : ℝ :=
  ∫ x, sech x ^ (2 * n) ∂law

theorem continuous_tanh : Continuous Real.tanh := by
  convert Real.continuous_sinh.div Real.continuous_cosh
    (fun x ↦ ne_of_gt (Real.cosh_pos x))
  funext x
  simpa only [Pi.div_apply] using Real.tanh_eq_sinh_div_cosh x

theorem sech_sq_add_tanh_sq (x : ℝ) :
    sech x ^ 2 + Real.tanh x ^ 2 = 1 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  unfold sech
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  field_simp [hc]
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

theorem endpointMoment_nonneg (law : Measure ℝ) (n : ℕ) :
    0 ≤ endpointMoment law n := by
  exact integral_nonneg fun x ↦ pow_nonneg (sech_pos x).le _

/-- A probability law for the endpoint diffusion together with Parisi
self-consistency at the endpoint. -/
structure EndpointLawData (q : ℝ) where
  law : Measure ℝ
  probability : IsProbabilityMeasure law
  selfConsistency : ∫ x, Real.tanh x ^ 2 ∂law = q

namespace EndpointLawData

theorem sechPow_memLp {q : ℝ} (d : EndpointLawData q) (n : ℕ) :
    MemLp (fun x ↦ sech x ^ n) 2 d.law := by
  letI := d.probability
  apply MemLp.of_bound (continuous_sech.pow n).aestronglyMeasurable 1
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sech_pos x).le _)]
  have hsech : sech x ≤ 1 := by
    unfold sech
    apply (div_le_iff₀ (Real.cosh_pos x)).2
    simpa using Real.one_le_cosh x
  exact pow_le_one₀ (sech_pos x).le hsech

theorem tanhSq_integrable {q : ℝ} (d : EndpointLawData q) :
    Integrable (fun x ↦ Real.tanh x ^ 2) d.law := by
  letI := d.probability
  apply (MemLp.of_bound (continuous_tanh.pow 2).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x ↦ ?_) :
      MemLp (fun x ↦ Real.tanh x ^ 2) 2 d.law).integrable (by norm_num)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := abs_sinh_lt_cosh x
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc := Real.cosh_pos x
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hc)).2
  have hp := mul_nonneg (sub_nonneg.mpr h.le)
    (add_nonneg hc.le (abs_nonneg (Real.sinh x)))
  nlinarith [sq_abs (Real.sinh x)]

/-- The first identity in `prop:ft-endpoint-identities` follows directly
from endpoint self-consistency. -/
theorem firstMoment {q : ℝ} (d : EndpointLawData q) :
    endpointMoment d.law 1 = 1 - q := by
  letI := d.probability
  have hsech : Integrable (fun x ↦ sech x ^ 2) d.law :=
    (d.sechPow_memLp 2).integrable (by norm_num)
  calc
    endpointMoment d.law 1 = ∫ x, sech x ^ 2 ∂d.law := by
      simp [endpointMoment]
    _ = ∫ x, (1 : ℝ) - Real.tanh x ^ 2 ∂d.law := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        linarith [sech_sq_add_tanh_sq x]
    _ = (∫ _x, (1 : ℝ) ∂d.law) - ∫ x, Real.tanh x ^ 2 ∂d.law := by
      rw [integral_sub (integrable_const _) d.tanhSq_integrable]
    _ = 1 - q := by rw [d.selfConsistency]; simp

theorem momentPos {q : ℝ} (d : EndpointLawData q) (n : ℕ) :
    0 < endpointMoment d.law n := by
  letI := d.probability
  have hint : Integrable (fun x ↦ sech x ^ (2 * n)) d.law :=
    (d.sechPow_memLp (2 * n)).integrable (by norm_num)
  apply (integral_pos_iff_support_of_nonneg
    (fun x ↦ pow_nonneg (sech_pos x).le _) hint).2
  have hsupp : Function.support (fun x ↦ sech x ^ (2 * n)) = Set.univ := by
    ext x
    simp only [Function.mem_support, ne_eq, Set.mem_univ, iff_true]
    exact (pow_pos (sech_pos x) _).ne'
  rw [hsupp, measure_univ]
  norm_num

end EndpointLawData

/-- Identification of the scalar moments in `EndpointData` with actual
moments of the endpoint diffusion law. -/
structure EndpointMomentRepresentation (q m1 m2 m3 : ℝ) where
  endpointLaw : EndpointLawData q
  m1_eq : m1 = endpointMoment endpointLaw.law 1
  m2_eq : m2 = endpointMoment endpointLaw.law 2
  m3_eq : m3 = endpointMoment endpointLaw.law 3

namespace EndpointMomentRepresentation

theorem m1Pos {q m1 m2 m3 : ℝ}
    (d : EndpointMomentRepresentation q m1 m2 m3) : 0 < m1 := by
  rw [d.m1_eq]
  exact d.endpointLaw.momentPos 1

theorem m2Pos {q m1 m2 m3 : ℝ}
    (d : EndpointMomentRepresentation q m1 m2 m3) : 0 < m2 := by
  rw [d.m2_eq]
  exact d.endpointLaw.momentPos 2

theorem firstMoment {q m1 m2 m3 : ℝ}
    (d : EndpointMomentRepresentation q m1 m2 m3) : m1 = 1 - q := by
  rw [d.m1_eq]
  exact d.endpointLaw.firstMoment

end EndpointMomentRepresentation

end

end FRSB.PositiveTemperature
