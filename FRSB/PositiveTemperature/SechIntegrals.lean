import FRSB.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Hyperbolic-secant integrals

These are the explicit normalization constants used in the two applications
of `eq:ft-strict-covariance`.
-/

namespace FRSB.PositiveTemperature

open Filter MeasureTheory Set Topology

noncomputable section

/-- The hyperbolic secant, kept local to the endpoint calculation. -/
def sech (x : ℝ) : ℝ := 1 / Real.cosh x

theorem continuous_sech : Continuous sech := by
  unfold sech
  exact continuous_const.div Real.continuous_cosh
    (fun x ↦ ne_of_gt (Real.cosh_pos x))

theorem measurable_sech_pow (n : ℕ) : Measurable (fun x ↦ sech x ^ n) :=
  (continuous_sech.pow n).measurable

theorem sech_pos (x : ℝ) : 0 < sech x :=
  one_div_pos.mpr (Real.cosh_pos x)

theorem tendsto_sinh_atTop : Tendsto Real.sinh atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_id
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact (Real.self_le_sinh_iff.mpr hx)

theorem abs_sinh_lt_cosh (x : ℝ) : |Real.sinh x| < Real.cosh x := by
  have hc := Real.cosh_pos x
  have hs : 0 ≤ |Real.sinh x| := abs_nonneg _
  have hid := Real.cosh_sq_sub_sinh_sq x
  nlinarith [sq_abs (Real.sinh x)]

theorem tendsto_cosh_atTop : Tendsto Real.cosh atTop atTop :=
  tendsto_atTop_mono (fun x ↦ (le_abs_self (Real.sinh x)).trans
    (abs_sinh_lt_cosh x).le) tendsto_sinh_atTop

theorem tendsto_inv_cosh_atTop_zero :
    Tendsto (fun x ↦ (Real.cosh x)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_cosh_atTop

theorem tendsto_sinh_div_cosh_sq_atTop_zero :
    Tendsto (fun x ↦ Real.sinh x / Real.cosh x ^ 2) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun x ↦ norm_nonneg _)
    _ tendsto_inv_cosh_atTop_zero
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (Real.cosh_pos x)]
  have hc := Real.cosh_pos x
  have hs := (abs_sinh_lt_cosh x).le
  rw [div_le_iff₀ (sq_pos_of_pos hc)]
  field_simp [ne_of_gt hc]
  nlinarith

theorem hasDerivAt_arctan_sinh (x : ℝ) :
    HasDerivAt (fun y ↦ Real.arctan (Real.sinh y)) (sech x) x := by
  have h := (Real.hasDerivAt_arctan (Real.sinh x)).comp x
    (Real.hasDerivAt_sinh x)
  convert h using 1
  unfold sech
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  field_simp [hc]
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

theorem hasDerivAt_sinh_div_cosh_sq (x : ℝ) :
    HasDerivAt (fun y ↦ Real.sinh y / Real.cosh y ^ 2)
      (-sech x + 2 * sech x ^ 3) x := by
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have h := (Real.hasDerivAt_sinh x).div
    ((Real.hasDerivAt_cosh x).pow 2) (pow_ne_zero 2 hc)
  simp only [Pi.pow_apply] at h
  convert h using 1
  unfold sech
  field_simp [hc]
  ring_nf
  nlinarith [Real.cosh_sq_sub_sinh_sq x, Real.cosh_pos x]

def sechAntideriv3 (x : ℝ) : ℝ :=
  (Real.sinh x / Real.cosh x ^ 2 + Real.arctan (Real.sinh x)) / 2

theorem hasDerivAt_sechAntideriv3 (x : ℝ) :
    HasDerivAt sechAntideriv3 (sech x ^ 3) x := by
  have h := ((hasDerivAt_sinh_div_cosh_sq x).add
    (hasDerivAt_arctan_sinh x)).div_const 2
  convert h using 1
  ring

theorem tendsto_sechAntideriv3_atTop :
    Tendsto sechAntideriv3 atTop (𝓝 (Real.pi / 4)) := by
  have hatan : Tendsto (fun x ↦ Real.arctan (Real.sinh x)) atTop
      (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right inf_le_left).comp tendsto_sinh_atTop
  change Tendsto
    (fun x ↦ (Real.sinh x / Real.cosh x ^ 2 + Real.arctan (Real.sinh x)) / 2)
    atTop (𝓝 (Real.pi / 4))
  have hpi : Real.pi / 2 / 2 = Real.pi / 4 := by ring
  rw [← hpi]
  simpa only [zero_add] using
    (tendsto_sinh_div_cosh_sq_atTop_zero.add hatan).div_const (2 : ℝ)

/-- `∫₀^∞ sech x dx = π/2`. -/
theorem integral_Ioi_sech :
    ∫ x in Ioi (0 : ℝ), sech x = Real.pi / 2 := by
  have hatan : Tendsto Real.arctan atTop (𝓝 (Real.pi / 2)) :=
    Real.tendsto_arctan_atTop.mono_right inf_le_left
  have hlim : Tendsto (fun x ↦ Real.arctan (Real.sinh x)) atTop
      (𝓝 (Real.pi / 2)) := hatan.comp tendsto_sinh_atTop
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0 : ℝ)) (g := fun x ↦ Real.arctan (Real.sinh x))
    (g' := sech) (l := Real.pi / 2)
    (fun x _ ↦ hasDerivAt_arctan_sinh x)
    (fun x _ ↦ le_of_lt (one_div_pos.mpr (Real.cosh_pos x))) hlim
  simpa [sech] using h

theorem integrableOn_Ioi_sech : IntegrableOn sech (Ioi (0 : ℝ)) := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (g := fun x ↦ Real.arctan (Real.sinh x)) (l := Real.pi / 2)
  · exact fun x _ ↦ hasDerivAt_arctan_sinh x
  · exact fun x _ ↦ le_of_lt (one_div_pos.mpr (Real.cosh_pos x))
  · exact (Real.tendsto_arctan_atTop.mono_right inf_le_left).comp
      tendsto_sinh_atTop

/-- `∫₀^∞ sech³ x dx = π/4`. -/
theorem integral_Ioi_sech_pow_three :
    ∫ x in Ioi (0 : ℝ), sech x ^ 3 = Real.pi / 4 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0 : ℝ)) (g := sechAntideriv3)
    (g' := fun x ↦ sech x ^ 3) (l := Real.pi / 4)
    (fun x _ ↦ hasDerivAt_sechAntideriv3 x)
    (fun x _ ↦ pow_nonneg (le_of_lt (one_div_pos.mpr (Real.cosh_pos x))) 3)
    tendsto_sechAntideriv3_atTop
  simpa [sechAntideriv3] using h

theorem integrableOn_Ioi_sech_pow_three :
    IntegrableOn (fun x ↦ sech x ^ 3) (Ioi (0 : ℝ)) := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (g := sechAntideriv3) (l := Real.pi / 4)
  · exact fun x _ ↦ hasDerivAt_sechAntideriv3 x
  · exact fun x _ ↦ pow_nonneg
      (le_of_lt (one_div_pos.mpr (Real.cosh_pos x))) 3
  · exact tendsto_sechAntideriv3_atTop

theorem tendsto_sinh_div_cosh_pow_four_atTop_zero :
    Tendsto (fun x ↦ Real.sinh x / Real.cosh x ^ 4) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hinvpow : Tendsto (fun x ↦ (Real.cosh x)⁻¹ ^ 3) atTop (𝓝 0) := by
    simpa using tendsto_inv_cosh_atTop_zero.pow 3
  apply squeeze_zero' (Eventually.of_forall fun x ↦ norm_nonneg _)
    _ hinvpow
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (Real.cosh_pos x)]
  have hc := Real.cosh_pos x
  have hs := (abs_sinh_lt_cosh x).le
  rw [div_le_iff₀ (pow_pos hc 4)]
  field_simp [ne_of_gt hc]
  nlinarith [sq_nonneg (Real.cosh x)]

theorem hasDerivAt_sinh_div_cosh_pow_four (x : ℝ) :
    HasDerivAt (fun y ↦ Real.sinh y / Real.cosh y ^ 4)
      (-3 * sech x ^ 3 + 4 * sech x ^ 5) x := by
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have h := (Real.hasDerivAt_sinh x).div
    ((Real.hasDerivAt_cosh x).pow 4) (pow_ne_zero 4 hc)
  simp only [Pi.pow_apply] at h
  convert h using 1
  unfold sech
  field_simp [hc]
  ring_nf
  have hmul :
      (Real.cosh x ^ 2 - Real.sinh x ^ 2 - 1) * Real.cosh x ^ 3 = 0 := by
    rw [Real.cosh_sq_sub_sinh_sq x]
    ring
  ring_nf at hmul
  nlinarith

def sechAntideriv5 (x : ℝ) : ℝ :=
  (Real.sinh x / Real.cosh x ^ 4 + 3 * sechAntideriv3 x) / 4

theorem hasDerivAt_sechAntideriv5 (x : ℝ) :
    HasDerivAt sechAntideriv5 (sech x ^ 5) x := by
  have h := ((hasDerivAt_sinh_div_cosh_pow_four x).add
    ((hasDerivAt_sechAntideriv3 x).const_mul 3)).div_const 4
  convert h using 1
  ring

theorem tendsto_sechAntideriv5_atTop :
    Tendsto sechAntideriv5 atTop (𝓝 (3 * Real.pi / 16)) := by
  change Tendsto
    (fun x ↦ (Real.sinh x / Real.cosh x ^ 4 + 3 * sechAntideriv3 x) / 4)
    atTop (𝓝 (3 * Real.pi / 16))
  have h := (tendsto_sinh_div_cosh_pow_four_atTop_zero.add
    (tendsto_sechAntideriv3_atTop.const_mul 3)).div_const (4 : ℝ)
  convert h using 1
  ring_nf

/-- `∫₀^∞ sech⁵ x dx = 3π/16`. -/
theorem integral_Ioi_sech_pow_five :
    ∫ x in Ioi (0 : ℝ), sech x ^ 5 = 3 * Real.pi / 16 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0 : ℝ)) (g := sechAntideriv5)
    (g' := fun x ↦ sech x ^ 5) (l := 3 * Real.pi / 16)
    (fun x _ ↦ hasDerivAt_sechAntideriv5 x)
    (fun x _ ↦ pow_nonneg (le_of_lt (one_div_pos.mpr (Real.cosh_pos x))) 5)
    tendsto_sechAntideriv5_atTop
  simpa [sechAntideriv5, sechAntideriv3] using h

theorem integrableOn_Ioi_sech_pow_five :
    IntegrableOn (fun x ↦ sech x ^ 5) (Ioi (0 : ℝ)) := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (g := sechAntideriv5) (l := 3 * Real.pi / 16)
  · exact fun x _ ↦ hasDerivAt_sechAntideriv5 x
  · exact fun x _ ↦ pow_nonneg
      (le_of_lt (one_div_pos.mpr (Real.cosh_pos x))) 5
  · exact tendsto_sechAntideriv5_atTop

/-- First normalization ratio in the endpoint covariance calculation. -/
theorem sech_pow_three_ratio :
    (∫ x in Ioi (0 : ℝ), sech x ^ 3) /
      (∫ x in Ioi (0 : ℝ), sech x) = (1 : ℝ) / 2 := by
  rw [integral_Ioi_sech_pow_three, integral_Ioi_sech]
  field_simp [ne_of_gt Real.pi_pos]
  norm_num

/-- Second normalization ratio in the endpoint covariance calculation. -/
theorem sech_pow_five_ratio :
    (∫ x in Ioi (0 : ℝ), sech x ^ 5) /
      (∫ x in Ioi (0 : ℝ), sech x ^ 3) = (3 : ℝ) / 4 := by
  rw [integral_Ioi_sech_pow_five, integral_Ioi_sech_pow_three]
  field_simp [ne_of_gt Real.pi_pos]
  norm_num

end

end FRSB.PositiveTemperature
