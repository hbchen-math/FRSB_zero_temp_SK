import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The strict weighted-moment step on an internal gap

This file formalizes the real-analysis argument in
`eq:zt-Gamma-weighted-second`--`eq:zt-Gamma-strict-moment`.
It is independent of the Parisi PDE: `f` is the function denoted by
`Γ''` in the paper.  The hypotheses say that its weighted second moment
vanishes and that it has the unique upward crossing supplied by the crossing
proposition.  The conclusion is exactly the strict first-moment inequality.
-/

namespace FRSB.ZeroTemperature.NoInternalGap

open intervalIntegral

/-- **Paper equation `eq:zt-Gamma-strict-moment`, analytic core.**

If a continuous function `f` has one upward sign crossing at `c` and
`∫ (t-a)(b-t)f(t) dt = 0`, then `∫ (b-t)f(t) dt < 0`.

In the paper one substitutes `f = Γ''`.  No PDE or probabilistic input is
used in this step. -/
theorem strictMoment_of_upwardCrossing
    {a b c : ℝ} (f : ℝ → ℝ)
    (hab : a < b) (hac : a < c) (hcb : c < b)
    (hf : ContinuousOn f (Set.uIcc a b))
    (hneg : ∀ t, a < t → t < c → f t < 0)
    (hpos : ∀ t, c < t → t < b → 0 < f t)
    (hweighted : ∫ t in a..b, (t - a) * (b - t) * f t = 0) :
    ∫ t in a..b, (b - t) * f t < 0 := by
  let F : ℝ → ℝ := fun t => (b - t) * f t
  let K : ℝ → ℝ := fun t => ((t - a) * F t) / (c - a)
  have hca : 0 < c - a := sub_pos.mpr hac
  have hfIcc : ContinuousOn f (Set.Icc a b) := by
    simpa only [Set.uIcc_of_le hab.le] using hf
  have hF : ContinuousOn F (Set.uIcc a b) :=
    (continuous_const.sub continuous_id).continuousOn.mul hf
  have hK : ContinuousOn K (Set.uIcc a b) :=
    ((continuous_id.sub continuous_const).continuousOn.mul hF).div_const _
  have hFIcc : ContinuousOn F (Set.Icc a b) :=
    (continuous_const.sub continuous_id).continuousOn.mul hfIcc
  have hKIcc : ContinuousOn K (Set.Icc a b) :=
    ((continuous_id.sub continuous_const).continuousOn.mul hFIcc).div_const _
  have hle : ∀ t ∈ Set.Ioc a b, F t ≤ K t := by
    intro t ht
    rcases ht with ⟨hat, htb⟩
    by_cases htc : t ≤ c
    · by_cases htc' : t = c
      · subst t
        simp [F, K, hca.ne']
      · have hfac : f t ≤ 0 := (hneg t hat (lt_of_le_of_ne htc htc')).le
        dsimp [F, K]
        apply (le_div_iff₀ hca).2
        have hbt : 0 ≤ b - t := sub_nonneg.mpr htb
        have htcsub : t - a ≤ c - a := sub_le_sub_right htc a
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hbt hfac]
    · have hct : c < t := lt_of_not_ge htc
      by_cases htb' : t = b
      · subst t
        simp [F, K]
      · have htb'' : t < b := lt_of_le_of_ne htb htb'
        have hfpos : 0 ≤ f t := (hpos t hct htb'').le
        dsimp [F, K]
        apply (le_div_iff₀ hca).2
        have hbt : 0 ≤ b - t := sub_nonneg.mpr htb
        have hact : c - a ≤ t - a := sub_le_sub_right hct.le a
        nlinarith [mul_nonneg hbt hfpos]
  have hstrict : F ((a + c) / 2) < K ((a + c) / 2) := by
    have ham : a < (a + c) / 2 := by linarith
    have hmc : (a + c) / 2 < c := by linarith
    have hmb : (a + c) / 2 < b := lt_trans hmc hcb
    have hfm : f ((a + c) / 2) < 0 := hneg _ ham hmc
    dsimp [F, K]
    apply (lt_div_iff₀ hca).2
    have hweight : 0 < b - (a + c) / 2 := sub_pos.mpr hmb
    nlinarith [mul_neg_of_pos_of_neg hweight hfm]
  have hmid_mem : (a + c) / 2 ∈ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab.le]
    constructor <;> linarith
  have hint : (∫ t in a..b, F t) < ∫ t in a..b, K t :=
    integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab hFIcc hKIcc hle
      ⟨(a + c) / 2, by simpa only [Set.uIcc_of_le hab.le] using hmid_mem, hstrict⟩
  have hKzero : (∫ t in a..b, K t) = 0 := by
    have hpoint : K = fun t => (1 / (c - a)) * ((t - a) * (b - t) * f t) := by
      funext t
      simp only [K, F]
      field_simp [hca.ne']
    rw [hpoint, integral_const_mul, hweighted, mul_zero]
  simpa [F, hKzero] using hint

end FRSB.ZeroTemperature.NoInternalGap
