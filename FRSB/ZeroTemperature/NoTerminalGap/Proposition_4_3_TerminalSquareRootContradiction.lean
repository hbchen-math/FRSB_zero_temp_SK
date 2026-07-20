import Mathlib

/-!
# Proposition 4.3, Step 4: the terminal square-root contradiction

This file isolates the final deterministic implication in the proof of
`prop:zt-no-terminal-gap`.  Only the positive lower estimate supplied by the asymptotic
`eq:zt-terminal-square-root` is used.
-/

namespace FRSB.ZeroTemperature.NoTerminalGap

open Set
open scoped Interval

/-- A positive square-root deficit of `Gamma` at one makes
`Gamma(t) - t` strictly negative on a terminal interval.  Its integral is therefore negative,
contradicting the variational condition that all such terminal integrals are nonnegative.

The hypothesis `squareRootLower` is the eventual lower bound obtained from
`1 - Gamma(t) ~ c * sqrt (1-t)` with `c > 0`. -/
theorem terminalSquareRoot_contradicts_nonnegative_integral
    (Gamma : ℝ → ℝ) (c : ℝ)
    (hc : 0 < c)
    (hGamma_cont : ContinuousOn Gamma (Icc 0 1))
    (hGamma_one : Gamma 1 = 1)
    (squareRootLower :
      ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
        c / 2 * √ε ≤ 1 - Gamma (1 - ε))
    (G_nonnegative :
      ∀ q : ℝ, 0 ≤ q → q < 1 →
        0 ≤ ∫ t in q..1, (Gamma t - t)) :
    False := by
  obtain ⟨δ, hδ, hsqrt⟩ := squareRootLower
  let d := min δ (min 1 (c ^ 2 / 16)) / 2
  let q := 1 - d
  have hc2 : 0 < c ^ 2 / 16 := by positivity
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hd_le_half : d ≤ 1 / 2 := by
    dsimp [d]
    have hmin : min δ (min 1 (c ^ 2 / 16)) ≤ 1 :=
      (min_le_right δ _).trans (min_le_left _ _)
    linarith
  have hq0 : 0 ≤ q := by
    dsimp [q]
    linarith
  have hq1 : q < 1 := by
    dsimp [q]
    linarith
  have hd_lt_delta : d < δ := by
    dsimp [d]
    have hminpos : 0 < min δ (min 1 (c ^ 2 / 16)) := by positivity
    have hminle : min δ (min 1 (c ^ 2 / 16)) ≤ δ := min_le_left _ _
    linarith
  have hd_lt_csq : d < c ^ 2 / 16 := by
    dsimp [d]
    have hminpos : 0 < min δ (min 1 (c ^ 2 / 16)) := by positivity
    have hminle : min δ (min 1 (c ^ 2 / 16)) ≤ c ^ 2 / 16 :=
      (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hnonpos : ∀ t ∈ Ioc q 1, Gamma t - t ≤ 0 := by
    intro t ht
    by_cases ht1 : t = 1
    · simp [ht1, hGamma_one]
    · have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
      let ε := 1 - t
      have hε : 0 < ε := by dsimp [ε]; linarith
      have hεd : ε < d := by
        dsimp [ε, q]
        dsimp [q] at ht
        linarith [ht.1]
      have hεδ : ε < δ := hεd.trans hd_lt_delta
      have hεc : ε < c ^ 2 / 16 := hεd.trans hd_lt_csq
      have hs := hsqrt ε hε hεδ
      have hsqrt_nonneg : 0 ≤ √ε := Real.sqrt_nonneg _
      have hsqrt_sq : (√ε) ^ 2 = ε := Real.sq_sqrt hε.le
      have hsqrt_lt : √ε < c / 2 := by
        nlinarith [sq_nonneg (√ε - c / 2)]
      have hε_lt : ε < c / 2 * √ε := by
        nlinarith [Real.sqrt_pos.2 hε]
      have hdeficit : ε < 1 - Gamma (1 - ε) := hε_lt.trans_le hs
      have hcancel : 1 - (1 - t) = t := by ring
      dsimp [ε] at hdeficit
      rw [hcancel] at hdeficit
      linarith
  have hstrict : Gamma q - q < 0 := by
    have hs := hsqrt d hd hd_lt_delta
    have hsqrt_nonneg : 0 ≤ √d := Real.sqrt_nonneg _
    have hsqrt_pos : 0 < √d := Real.sqrt_pos.2 hd
    have hsqrt_sq : (√d) ^ 2 = d := Real.sq_sqrt hd.le
    have hsqrt_lt : √d < c / 2 := by
      nlinarith [sq_nonneg (√d - c / 2)]
    have hd_lt : d < c / 2 * √d := by
      nlinarith
    have hdeficit : d < 1 - Gamma (1 - d) := hd_lt.trans_le hs
    dsimp [q]
    linarith
  have hcont_sub : ContinuousOn (fun t ↦ Gamma t - t) (Icc q 1) := by
    apply (hGamma_cont.mono ?_).sub continuousOn_id
    intro t ht
    exact ⟨hq0.trans ht.1, ht.2⟩
  have hintegral_neg : (∫ t in q..1, (Gamma t - t)) < 0 := by
    have hzero_cont : ContinuousOn (fun _ : ℝ ↦ (0 : ℝ)) (Icc q 1) :=
      continuousOn_const
    have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      hq1 hcont_sub hzero_cont hnonpos ⟨q, left_mem_Icc.2 hq1.le, hstrict⟩
    simpa using hlt
  exact (not_lt_of_ge (G_nonnegative q hq0 hq1)) hintegral_neg

end FRSB.ZeroTemperature.NoTerminalGap
