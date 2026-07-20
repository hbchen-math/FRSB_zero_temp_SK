import FRSB.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.Covariance

/-!
# Strict covariance for similarly ordered functions

This file begins the measure-theoretic formalization of
`eq:ft-strict-covariance`.  The lemmas below isolate the pointwise order
argument used in the double-integral proof.  Keeping this argument separate
from Fubini and integrability makes it reusable for the two hyperbolic-secant
weights in the positive-temperature endpoint proof.
-/

namespace FRSB.PositiveTemperature

open MeasureTheory
open ProbabilityTheory

/-- Two antitone real functions have nonnegative paired increments.  This is
the pointwise nonnegativity of the integrand in the double-integral identity
for covariance. -/
theorem antitone_difference_mul_difference_nonneg {α : Type*} [LinearOrder α]
    {f g : α → ℝ} (hf : Antitone f) (hg : Antitone g) (x y : α) :
    0 ≤ (f x - f y) * (g x - g y) := by
  rcases le_total x y with hxy | hyx
  · exact mul_nonneg (sub_nonneg.mpr (hf hxy)) (sub_nonneg.mpr (hg hxy))
  · exact mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr (hf hyx)) (sub_nonpos.mpr (hg hyx))

/-- If both decreases are strict between two ordered points, the paired
increment in the covariance integrand is strictly positive. -/
theorem difference_mul_difference_pos_of_lt {α : Type*} [Preorder α]
    {f g : α → ℝ} {x y : α} (hf : f y < f x) (hg : g y < g x) :
    0 < (f x - f y) * (g x - g y) :=
  mul_pos (sub_pos.mpr hf) (sub_pos.mpr hg)

/-- Rectangle form of the strict part of `eq:ft-strict-covariance`: uniform
strict separation of two functions on ordered sets makes the covariance
integrand positive throughout their Cartesian product. -/
theorem difference_mul_difference_pos_on_rectangle {α : Type*} [Preorder α]
    {f g : α → ℝ} {I J : Set α}
    (hf : ∀ x ∈ I, ∀ y ∈ J, f y < f x)
    (hg : ∀ x ∈ I, ∀ y ∈ J, g y < g x) :
    ∀ x ∈ I, ∀ y ∈ J, 0 < (f x - f y) * (g x - g y) := by
  intro x hx y hy
  exact difference_mul_difference_pos_of_lt (hf x hx y hy) (hg x hx y hy)

/-- The double-integral identity behind `eq:ft-strict-covariance`. -/
theorem integral_difference_mul_difference_eq_two_covariance
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ z : α × α, (f z.1 - f z.2) * (g z.1 - g z.2) ∂μ.prod μ) =
      2 * cov[f, g; μ] := by
  have hf1 := hf.comp_fst μ
  have hf2 := hf.comp_snd μ
  have hg1 := hg.comp_fst μ
  have hg2 := hg.comp_snd μ
  have h11 : Integrable (fun z : α × α ↦ f z.1 * g z.1) (μ.prod μ) :=
    hf1.integrable_mul hg1
  have h12 : Integrable (fun z : α × α ↦ f z.1 * g z.2) (μ.prod μ) :=
    hf1.integrable_mul hg2
  have h21 : Integrable (fun z : α × α ↦ f z.2 * g z.1) (μ.prod μ) :=
    hf2.integrable_mul hg1
  have h22 : Integrable (fun z : α × α ↦ f z.2 * g z.2) (μ.prod μ) :=
    hf2.integrable_mul hg2
  rw [show (fun z : α × α ↦ (f z.1 - f z.2) * (g z.1 - g z.2)) =
      fun z ↦ (f z.1 * g z.1 - f z.1 * g z.2) -
        (f z.2 * g z.1 - f z.2 * g z.2) by funext z; ring]
  calc
    _ = (∫ z : α × α, f z.1 * g z.1 - f z.1 * g z.2 ∂μ.prod μ) -
        ∫ z : α × α, f z.2 * g z.1 - f z.2 * g z.2 ∂μ.prod μ :=
      integral_sub (h11.sub h12) (h21.sub h22)
    _ = ((∫ z : α × α, f z.1 * g z.1 ∂μ.prod μ) -
          ∫ z : α × α, f z.1 * g z.2 ∂μ.prod μ) -
        ((∫ z : α × α, f z.2 * g z.1 ∂μ.prod μ) -
          ∫ z : α × α, f z.2 * g z.2 ∂μ.prod μ) := by
      rw [integral_sub h11 h12, integral_sub h21 h22]
    _ = 2 * cov[f, g; μ] := by
      have e11 : (∫ z : α × α, f z.1 * g z.1 ∂μ.prod μ) =
          ∫ x, f x * g x ∂μ := by
        change (∫ z : α × α, (fun x ↦ f x * g x) z.1 ∂μ.prod μ) = _
        calc
          _ = μ.real Set.univ • ∫ x, f x * g x ∂μ :=
            integral_fun_fst (μ := μ) (ν := μ) (fun x ↦ f x * g x)
          _ = _ := by simp
      have e12 : (∫ z : α × α, f z.1 * g z.2 ∂μ.prod μ) =
          (∫ x, f x ∂μ) * ∫ y, g y ∂μ := integral_prod_mul f g
      have e21 : (∫ z : α × α, f z.2 * g z.1 ∂μ.prod μ) =
          (∫ x, f x ∂μ) * ∫ y, g y ∂μ := by
        calc
          _ = ∫ z : α × α, g z.1 * f z.2 ∂μ.prod μ := by
            congr 1
            funext z
            ring
          _ = (∫ x, g x ∂μ) * ∫ y, f y ∂μ := integral_prod_mul g f
          _ = _ := by ring
      have e22 : (∫ z : α × α, f z.2 * g z.2 ∂μ.prod μ) =
          ∫ x, f x * g x ∂μ := by
        change (∫ z : α × α, (fun x ↦ f x * g x) z.2 ∂μ.prod μ) = _
        calc
          _ = μ.real Set.univ • ∫ x, f x * g x ∂μ :=
            integral_fun_snd (μ := μ) (ν := μ) (fun x ↦ f x * g x)
          _ = _ := by simp
      rw [e11, e12, e21, e22]
      rw [covariance_eq_sub hf hg]
      simp only [Pi.mul_apply]
      ring

/-- A positive-mass strict rectangle makes the paired-increment integral
strictly positive.  This is the measure-theoretic strictness step in
`eq:ft-strict-covariance`. -/
theorem integral_difference_mul_difference_pos
    {α : Type*} [MeasurableSpace α] [LinearOrder α] {μ : Measure α}
    [IsFiniteMeasure μ] {f g : α → ℝ} {I J : Set α}
    (hf₂ : MemLp f 2 μ) (hg₂ : MemLp g 2 μ)
    (hf : Antitone f) (hg : Antitone g)
    (hI : 0 < μ I) (hJ : 0 < μ J)
    (hf_strict : ∀ x ∈ I, ∀ y ∈ J, f y < f x)
    (hg_strict : ∀ x ∈ I, ∀ y ∈ J, g y < g x) :
    0 < ∫ z : α × α, (f z.1 - f z.2) * (g z.1 - g z.2) ∂μ.prod μ := by
  let k : α × α → ℝ := fun z ↦ (f z.1 - f z.2) * (g z.1 - g z.2)
  have hk_nonneg : ∀ z, 0 ≤ k z := fun z ↦
    antitone_difference_mul_difference_nonneg hf hg z.1 z.2
  have hk_int : Integrable k (μ.prod μ) := by
    exact (hf₂.comp_fst μ |>.sub (hf₂.comp_snd μ)).integrable_mul
      (hg₂.comp_fst μ |>.sub (hg₂.comp_snd μ))
  apply (integral_pos_iff_support_of_nonneg hk_nonneg hk_int).2
  have hrect : I ×ˢ J ⊆ Function.support k := by
    intro z hz
    exact ne_of_gt (difference_mul_difference_pos_on_rectangle
      hf_strict hg_strict z.1 hz.1 z.2 hz.2)
  calc
    0 < μ I * μ J := ENNReal.mul_pos hI.ne' hJ.ne'
    _ = (μ.prod μ) (I ×ˢ J) := (Measure.prod_prod I J).symm
    _ ≤ (μ.prod μ) (Function.support k) := measure_mono hrect

/-- The paired-increment identity for an arbitrary finite measure.  The
probability version above is the special case `μ.real univ = 1`. -/
theorem integral_difference_mul_difference_eq_finite_covariance
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ z : α × α, (f z.1 - f z.2) * (g z.1 - g z.2) ∂μ.prod μ) =
      2 * (μ.real Set.univ * (∫ x, f x * g x ∂μ) -
        (∫ x, f x ∂μ) * ∫ x, g x ∂μ) := by
  have hf1 := hf.comp_fst μ
  have hf2 := hf.comp_snd μ
  have hg1 := hg.comp_fst μ
  have hg2 := hg.comp_snd μ
  have h11 : Integrable (fun z : α × α ↦ f z.1 * g z.1) (μ.prod μ) :=
    hf1.integrable_mul hg1
  have h12 : Integrable (fun z : α × α ↦ f z.1 * g z.2) (μ.prod μ) :=
    hf1.integrable_mul hg2
  have h21 : Integrable (fun z : α × α ↦ f z.2 * g z.1) (μ.prod μ) :=
    hf2.integrable_mul hg1
  have h22 : Integrable (fun z : α × α ↦ f z.2 * g z.2) (μ.prod μ) :=
    hf2.integrable_mul hg2
  rw [show (fun z : α × α ↦ (f z.1 - f z.2) * (g z.1 - g z.2)) =
      fun z ↦ (f z.1 * g z.1 - f z.1 * g z.2) -
        (f z.2 * g z.1 - f z.2 * g z.2) by funext z; ring]
  calc
    _ = (∫ z : α × α, f z.1 * g z.1 - f z.1 * g z.2 ∂μ.prod μ) -
        ∫ z : α × α, f z.2 * g z.1 - f z.2 * g z.2 ∂μ.prod μ :=
      integral_sub (h11.sub h12) (h21.sub h22)
    _ = ((∫ z : α × α, f z.1 * g z.1 ∂μ.prod μ) -
          ∫ z : α × α, f z.1 * g z.2 ∂μ.prod μ) -
        ((∫ z : α × α, f z.2 * g z.1 ∂μ.prod μ) -
          ∫ z : α × α, f z.2 * g z.2 ∂μ.prod μ) := by
      rw [integral_sub h11 h12, integral_sub h21 h22]
    _ = _ := by
      have e11 : (∫ z : α × α, f z.1 * g z.1 ∂μ.prod μ) =
          μ.real Set.univ * ∫ x, f x * g x ∂μ := by
        change (∫ z : α × α, (fun x ↦ f x * g x) z.1 ∂μ.prod μ) = _
        simpa [smul_eq_mul] using
          (integral_fun_fst (μ := μ) (ν := μ) (fun x ↦ f x * g x))
      have e12 : (∫ z : α × α, f z.1 * g z.2 ∂μ.prod μ) =
          (∫ x, f x ∂μ) * ∫ y, g y ∂μ := integral_prod_mul f g
      have e21 : (∫ z : α × α, f z.2 * g z.1 ∂μ.prod μ) =
          (∫ x, f x ∂μ) * ∫ y, g y ∂μ := by
        calc
          _ = ∫ z : α × α, g z.1 * f z.2 ∂μ.prod μ := by
            congr 1
            funext z
            ring
          _ = (∫ x, g x ∂μ) * ∫ y, f y ∂μ := integral_prod_mul g f
          _ = _ := by ring
      have e22 : (∫ z : α × α, f z.2 * g z.2 ∂μ.prod μ) =
          μ.real Set.univ * ∫ x, f x * g x ∂μ := by
        change (∫ z : α × α, (fun x ↦ f x * g x) z.2 ∂μ.prod μ) = _
        simpa [smul_eq_mul] using
          (integral_fun_snd (μ := μ) (ν := μ) (fun x ↦ f x * g x))
      rw [e11, e12, e21, e22]
      ring

/-- Finite-measure ratio form of strict covariance.  It compares the
`f`-weighted expectation of `g` with the ordinary normalized expectation of
`g`, without bundling the finite measure as a probability measure. -/
theorem strict_covariance_ratio_finite
    {α : Type*} [MeasurableSpace α] [LinearOrder α] {μ : Measure α}
    [IsFiniteMeasure μ] {f g : α → ℝ} {I J : Set α}
    (hf₂ : MemLp f 2 μ) (hg₂ : MemLp g 2 μ)
    (hf : Antitone f) (hg : Antitone g)
    (hμ : 0 < μ.real Set.univ) (hf_mean : 0 < ∫ x, f x ∂μ)
    (hI : 0 < μ I) (hJ : 0 < μ J)
    (hf_strict : ∀ x ∈ I, ∀ y ∈ J, f y < f x)
    (hg_strict : ∀ x ∈ I, ∀ y ∈ J, g y < g x) :
    (∫ x, g x ∂μ) / μ.real Set.univ <
      (∫ x, f x * g x ∂μ) / ∫ x, f x ∂μ := by
  have hpair := integral_difference_mul_difference_pos hf₂ hg₂ hf hg
    hI hJ hf_strict hg_strict
  rw [integral_difference_mul_difference_eq_finite_covariance hf₂ hg₂] at hpair
  apply (div_lt_div_iff₀ hμ hf_mean).2
  nlinarith

/-- Strict covariance in the ratio form used in
`eq:ft-strict-covariance`.  Positive mass on one separated rectangle is the
precise nondegeneracy assumption needed for strictness. -/
theorem strict_covariance_ratio
    {α : Type*} [MeasurableSpace α] [LinearOrder α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f g : α → ℝ} {I J : Set α}
    (hf₂ : MemLp f 2 μ) (hg₂ : MemLp g 2 μ)
    (hf : Antitone f) (hg : Antitone g)
    (hf_mean : 0 < ∫ x, f x ∂μ)
    (hI : 0 < μ I) (hJ : 0 < μ J)
    (hf_strict : ∀ x ∈ I, ∀ y ∈ J, f y < f x)
    (hg_strict : ∀ x ∈ I, ∀ y ∈ J, g y < g x) :
    (∫ x, g x ∂μ) < (∫ x, f x * g x ∂μ) / ∫ x, f x ∂μ := by
  have hpair := integral_difference_mul_difference_pos hf₂ hg₂ hf hg
    hI hJ hf_strict hg_strict
  have hid := integral_difference_mul_difference_eq_two_covariance hf₂ hg₂
  have hcov : 0 < cov[f, g; μ] := by
    rw [hid] at hpair
    linarith
  rw [covariance_eq_sub hf₂ hg₂] at hcov
  apply (lt_div_iff₀ hf_mean).2
  simp only [Pi.mul_apply] at hcov
  nlinarith

end FRSB.PositiveTemperature
