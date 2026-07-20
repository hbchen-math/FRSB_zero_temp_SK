import FRSB.PositiveTemperature.SechIntegrals
import FRSB.PositiveTemperature.StrictCovariance
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Endpoint covariance specializations

This file packages the two finite measures with densities `sech` and
`sech³` on the positive half-line.  They are the reference measures in the
two applications of `eq:ft-strict-covariance`.
-/

namespace FRSB.PositiveTemperature

open Filter MeasureTheory Set

noncomputable section

/-- The finite half-line measure with density `sech^n`. -/
def sechWeightedMeasure (n : ℕ) : Measure ℝ :=
  ((volume : Measure ℝ).restrict (Ioi 0)).withDensity
    (fun x ↦ ENNReal.ofReal (sech x ^ n))

noncomputable instance sechWeightedMeasureOne_isFinite :
    IsFiniteMeasure (sechWeightedMeasure 1) := by
  unfold sechWeightedMeasure
  exact isFiniteMeasure_withDensity_ofReal
    (by simpa using integrableOn_Ioi_sech.hasFiniteIntegral)

noncomputable instance sechWeightedMeasureThree_isFinite :
    IsFiniteMeasure (sechWeightedMeasure 3) := by
  unfold sechWeightedMeasure
  exact isFiniteMeasure_withDensity_ofReal
    integrableOn_Ioi_sech_pow_three.hasFiniteIntegral

/-- Integration against the weighted measure is ordinary weighted
integration on the positive half-line. -/
theorem integral_sechWeightedMeasure (n : ℕ) (g : ℝ → ℝ) :
    ∫ x, g x ∂sechWeightedMeasure n =
      ∫ x in Ioi (0 : ℝ), sech x ^ n * g x := by
  unfold sechWeightedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_sech_pow n).ennreal_ofReal)
    (Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top) g]
  simp only [ENNReal.toReal_ofReal (pow_nonneg (sech_pos _).le _), smul_eq_mul]

theorem sechWeightedMeasureOne_real_univ :
    (sechWeightedMeasure 1).real Set.univ = Real.pi / 2 := by
  have h := integral_sechWeightedMeasure 1 (fun _ ↦ (1 : ℝ))
  simp only [integral_const, smul_eq_mul, mul_one] at h
  simpa [pow_one, integral_Ioi_sech] using h

theorem sechWeightedMeasureThree_real_univ :
    (sechWeightedMeasure 3).real Set.univ = Real.pi / 4 := by
  have h := integral_sechWeightedMeasure 3 (fun _ ↦ (1 : ℝ))
  simp only [integral_const, smul_eq_mul, mul_one] at h
  simpa [integral_Ioi_sech_pow_three] using h

/-- The globally antitone extension of `sech` from the positive half-line. -/
def sechHalf (x : ℝ) : ℝ := sech (max x 0)

theorem continuous_sechHalf : Continuous sechHalf :=
  continuous_sech.comp (continuous_id.max continuous_const)

theorem sechHalf_pos (x : ℝ) : 0 < sechHalf x := sech_pos _

theorem antitone_sechHalf : Antitone sechHalf := by
  intro x y hxy
  unfold sechHalf sech
  have hm : max x 0 ≤ max y 0 := max_le_max_right 0 hxy
  have hc : Real.cosh (max x 0) ≤ Real.cosh (max y 0) := by
    rw [Real.cosh_le_cosh]
    rw [abs_of_nonneg (le_max_right x 0),
      abs_of_nonneg (le_max_right y 0)]
    exact hm
  exact one_div_le_one_div_of_le (Real.cosh_pos _) hc

theorem sechHalf_strict_of_max_lt {x y : ℝ} (hxy : max x 0 < max y 0) :
    sechHalf y < sechHalf x := by
  unfold sechHalf sech
  have hc : Real.cosh (max x 0) < Real.cosh (max y 0) := by
    rw [Real.cosh_lt_cosh]
    rw [abs_of_nonneg (le_max_right x 0),
      abs_of_nonneg (le_max_right y 0)]
    exact hxy
  exact one_div_lt_one_div_of_lt (Real.cosh_pos _) hc

/-- The decreasing test function `g = sech²` in both covariance
applications. -/
def endpointTest (x : ℝ) : ℝ := sechHalf x ^ 2

theorem antitone_endpointTest : Antitone endpointTest := by
  intro x y hxy
  unfold endpointTest
  have h := antitone_sechHalf hxy
  nlinarith [sechHalf_pos x, sechHalf_pos y]

theorem endpointTest_strict_of_max_lt {x y : ℝ} (hxy : max x 0 < max y 0) :
    endpointTest y < endpointTest x := by
  unfold endpointTest
  have h := sechHalf_strict_of_max_lt hxy
  nlinarith [sechHalf_pos x, sechHalf_pos y]

theorem endpointTest_memLp_one : MemLp endpointTest 2 (sechWeightedMeasure 1) := by
  apply MemLp.of_bound (continuous_sechHalf.pow 2).aestronglyMeasurable 1
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h : sechHalf x ≤ 1 := by
    unfold sechHalf sech
    apply (div_le_iff₀ (Real.cosh_pos _)).2
    simpa using Real.one_le_cosh (max x 0)
  nlinarith [sechHalf_pos x]

theorem endpointTest_memLp_three : MemLp endpointTest 2 (sechWeightedMeasure 3) := by
  apply MemLp.of_bound (continuous_sechHalf.pow 2).aestronglyMeasurable 1
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h : sechHalf x ≤ 1 := by
    unfold sechHalf sech
    apply (div_le_iff₀ (Real.cosh_pos _)).2
    simpa using Real.one_le_cosh (max x 0)
  nlinarith [sechHalf_pos x]

theorem endpointTest_reference_one :
    (∫ x, endpointTest x ∂sechWeightedMeasure 1) /
      (sechWeightedMeasure 1).real Set.univ = (1 : ℝ) / 2 := by
  rw [integral_sechWeightedMeasure, sechWeightedMeasureOne_real_univ]
  have hpoint : ∀ x ∈ Ioi (0 : ℝ),
      sech x ^ 1 * endpointTest x = sech x ^ 3 := by
    intro x hx
    have hm : max x 0 = x := max_eq_left hx.le
    simp only [endpointTest, sechHalf, hm, pow_one]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint,
    integral_Ioi_sech_pow_three]
  field_simp [ne_of_gt Real.pi_pos]
  norm_num

theorem endpointTest_reference_three :
    (∫ x, endpointTest x ∂sechWeightedMeasure 3) /
      (sechWeightedMeasure 3).real Set.univ = (3 : ℝ) / 4 := by
  rw [integral_sechWeightedMeasure, sechWeightedMeasureThree_real_univ]
  have hpoint : ∀ x ∈ Ioi (0 : ℝ),
      sech x ^ 3 * endpointTest x = sech x ^ 5 := by
    intro x hx
    have hm : max x 0 = x := max_eq_left hx.le
    simp only [endpointTest, sechHalf, hm]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint,
    integral_Ioi_sech_pow_five]
  field_simp [ne_of_gt Real.pi_pos]
  norm_num

/-- The `1/2` strict covariance estimate, ready for an endpoint transformed
density `f`. -/
theorem endpoint_covariance21 {f : ℝ → ℝ} {I J : Set ℝ}
    (hf₂ : MemLp f 2 (sechWeightedMeasure 1)) (hf : Antitone f)
    (hf_mean : 0 < ∫ x, f x ∂sechWeightedMeasure 1)
    (hI : 0 < sechWeightedMeasure 1 I)
    (hJ : 0 < sechWeightedMeasure 1 J)
    (hf_strict : ∀ x ∈ I, ∀ y ∈ J, f y < f x)
    (hIJ : ∀ x ∈ I, ∀ y ∈ J, max x 0 < max y 0) :
    (1 : ℝ) / 2 <
      (∫ x, f x * endpointTest x ∂sechWeightedMeasure 1) /
        ∫ x, f x ∂sechWeightedMeasure 1 := by
  rw [← endpointTest_reference_one]
  apply strict_covariance_ratio_finite hf₂ endpointTest_memLp_one hf
    antitone_endpointTest
  · rw [sechWeightedMeasureOne_real_univ]
    positivity
  · exact hf_mean
  · exact hI
  · exact hJ
  · exact hf_strict
  · intro x hx y hy
    exact endpointTest_strict_of_max_lt (hIJ x hx y hy)

/-- The `3/4` strict covariance estimate, ready for an endpoint transformed
density `f`. -/
theorem endpoint_covariance32 {f : ℝ → ℝ} {I J : Set ℝ}
    (hf₂ : MemLp f 2 (sechWeightedMeasure 3)) (hf : Antitone f)
    (hf_mean : 0 < ∫ x, f x ∂sechWeightedMeasure 3)
    (hI : 0 < sechWeightedMeasure 3 I)
    (hJ : 0 < sechWeightedMeasure 3 J)
    (hf_strict : ∀ x ∈ I, ∀ y ∈ J, f y < f x)
    (hIJ : ∀ x ∈ I, ∀ y ∈ J, max x 0 < max y 0) :
    (3 : ℝ) / 4 <
      (∫ x, f x * endpointTest x ∂sechWeightedMeasure 3) /
        ∫ x, f x ∂sechWeightedMeasure 3 := by
  rw [← endpointTest_reference_three]
  apply strict_covariance_ratio_finite hf₂ endpointTest_memLp_three hf
    antitone_endpointTest
  · rw [sechWeightedMeasureThree_real_univ]
    positivity
  · exact hf_mean
  · exact hI
  · exact hJ
  · exact hf_strict
  · intro x hx y hy
    exact endpointTest_strict_of_max_lt (hIJ x hx y hy)

/-- Changing from the `sech` reference measure to the `sech³` reference
measure is multiplication by the endpoint test `sech²`. -/
theorem integral_three_eq_one_endpointTest (g : ℝ → ℝ) :
    ∫ x, g x ∂sechWeightedMeasure 3 =
      ∫ x, g x * endpointTest x ∂sechWeightedMeasure 1 := by
  rw [integral_sechWeightedMeasure, integral_sechWeightedMeasure]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hm : max x 0 = x := max_eq_left hx.le
  simp only [endpointTest, sechHalf, hm, pow_one]
  ring

/-- The transformed-density representation of the first three endpoint
moment ratios.  Its strict inequalities are derived below, rather than stored
as scalar assumptions. -/
structure EndpointDensityRatios (m1 m2 m3 : ℝ) where
  f : ℝ → ℝ
  I : Set ℝ
  J : Set ℝ
  fMeasurable : Measurable f
  fPos : ∀ x, 0 < f x
  fAntitone : Antitone f
  fMemLpOne : MemLp f 2 (sechWeightedMeasure 1)
  fMemLpThree : MemLp f 2 (sechWeightedMeasure 3)
  fMeanOnePos : 0 < ∫ x, f x ∂sechWeightedMeasure 1
  fMeanThreePos : 0 < ∫ x, f x ∂sechWeightedMeasure 3
  IPosOne : 0 < sechWeightedMeasure 1 I
  JPosOne : 0 < sechWeightedMeasure 1 J
  IPosThree : 0 < sechWeightedMeasure 3 I
  JPosThree : 0 < sechWeightedMeasure 3 J
  fStrict : ∀ x ∈ I, ∀ y ∈ J, f y < f x
  separated : ∀ x ∈ I, ∀ y ∈ J, max x 0 < max y 0
  ratio21 : m2 / m1 =
    (∫ x, f x * endpointTest x ∂sechWeightedMeasure 1) /
      ∫ x, f x ∂sechWeightedMeasure 1
  ratio32 : m3 / m2 =
    (∫ x, f x * endpointTest x ∂sechWeightedMeasure 3) /
      ∫ x, f x ∂sechWeightedMeasure 3

namespace EndpointDensityRatios

theorem covariance21 {m1 m2 m3 : ℝ} (d : EndpointDensityRatios m1 m2 m3) :
    (1 : ℝ) / 2 < m2 / m1 := by
  rw [d.ratio21]
  exact endpoint_covariance21 d.fMemLpOne d.fAntitone d.fMeanOnePos
    d.IPosOne d.JPosOne d.fStrict d.separated

theorem covariance32 {m1 m2 m3 : ℝ} (d : EndpointDensityRatios m1 m2 m3) :
    (3 : ℝ) / 4 < m3 / m2 := by
  rw [d.ratio32]
  exact endpoint_covariance32 d.fMemLpThree d.fAntitone d.fMeanThreePos
    d.IPosThree d.JPosThree d.fStrict d.separated

/-- Strict log-convexity of the first three endpoint moments.  This is the
strict Cauchy--Schwarz step in the manuscript, proved as positive variance of
`endpointTest` under the measure tilted by the positive transformed density. -/
theorem logConvex {m1 m2 m3 : ℝ} (hm1 : 0 < m1) (hm2 : 0 < m2)
    (d : EndpointDensityRatios m1 m2 m3) : m2 ^ 2 < m1 * m3 := by
  let ν : Measure ℝ := (sechWeightedMeasure 1).withDensity
    (fun x ↦ ENNReal.ofReal (d.f x))
  letI : IsFiniteMeasure ν := by
    unfold ν
    exact isFiniteMeasure_withDensity_ofReal
      (d.fMemLpOne.integrable (by norm_num)).hasFiniteIntegral
  have hν_integral (g : ℝ → ℝ) :
      ∫ x, g x ∂ν = ∫ x, d.f x * g x ∂sechWeightedMeasure 1 := by
    unfold ν
    rw [integral_withDensity_eq_integral_toReal_smul
      d.fMeasurable.ennreal_ofReal
      (Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top) g]
    simp only [ENNReal.toReal_ofReal (d.fPos _).le, smul_eq_mul]
  have hν_mass : ν.real Set.univ = ∫ x, d.f x ∂sechWeightedMeasure 1 := by
    have h := hν_integral (fun _ ↦ (1 : ℝ))
    simpa only [integral_const, smul_eq_mul, mul_one] using h
  have hνI : 0 < ν d.I := by
    rw [pos_iff_ne_zero]
    intro hz
    have hz' := (withDensity_apply_eq_zero d.fMeasurable.ennreal_ofReal).mp hz
    have : sechWeightedMeasure 1 d.I = 0 := by
      simpa [d.fPos] using hz'
    exact d.IPosOne.ne' this
  have hνJ : 0 < ν d.J := by
    rw [pos_iff_ne_zero]
    intro hz
    have hz' := (withDensity_apply_eq_zero d.fMeasurable.ennreal_ofReal).mp hz
    have : sechWeightedMeasure 1 d.J = 0 := by
      simpa [d.fPos] using hz'
    exact d.JPosOne.ne' this
  have hgν : MemLp endpointTest 2 ν := by
    apply MemLp.of_bound (continuous_sechHalf.pow 2).aestronglyMeasurable 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h : sechHalf x ≤ 1 := by
      unfold sechHalf sech
      apply (div_le_iff₀ (Real.cosh_pos _)).2
      simpa using Real.one_le_cosh (max x 0)
    nlinarith [sechHalf_pos x]
  have hνmean : 0 < ∫ x, endpointTest x ∂ν := by
    rw [hν_integral]
    have hthree := d.fMeanThreePos
    rw [integral_three_eq_one_endpointTest] at hthree
    simpa [mul_assoc, mul_comm, mul_left_comm] using hthree
  have hstrict := strict_covariance_ratio_finite hgν hgν
    antitone_endpointTest antitone_endpointTest
    (by rw [hν_mass]; exact d.fMeanOnePos) hνmean hνI hνJ
    (fun x hx y hy ↦ endpointTest_strict_of_max_lt (d.separated x hx y hy))
    (fun x hx y hy ↦ endpointTest_strict_of_max_lt (d.separated x hx y hy))
  rw [hν_mass, hν_integral, hν_integral] at hstrict
  have hratio : m2 / m1 < m3 / m2 := by
    rw [d.ratio21, d.ratio32]
    rw [integral_three_eq_one_endpointTest,
      integral_three_eq_one_endpointTest]
    simpa [endpointTest, pow_two, mul_assoc, mul_comm, mul_left_comm] using hstrict
  simpa [pow_two, mul_comm] using (div_lt_div_iff₀ hm1 hm2).mp hratio

end EndpointDensityRatios

end

end FRSB.PositiveTemperature
