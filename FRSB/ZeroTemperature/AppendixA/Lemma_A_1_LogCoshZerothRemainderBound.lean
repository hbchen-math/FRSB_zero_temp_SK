import Mathlib

/-! # Appendix A, Lemma A.1: zeroth endpoint remainder bound -/

namespace FRSB.ZeroTemperature.AppendixA

/-- **Active Appendix A, Lemma `lem:app-endpoint-expansion`: uniform zeroth
remainder bound.**

For `R(y)=log(1+y)-y+y²/2-y³/3` and `0≤y≤1`,
`R'(y)=-y³/(1+y)`.  Comparing this derivative with the derivative of
`-y⁴/4` gives the sharp alternating-remainder estimate `|R(y)|≤y⁴/4`. -/
theorem logOnePlus_cubicRemainder_abs_le
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |Real.log (1+y)-y+y^2/2-y^3/3| ≤ y^4/4 := by
  let R : ℝ → ℝ := fun t => Real.log (1+t)-t+t^2/2-t^3/3
  let G : ℝ → ℝ := fun t => R t + t^4/4
  have hRderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt R (-t^3/(1+t)) t := by
    intro t ht
    have hne : 1+t ≠ 0 := by linarith [ht.1]
    dsimp [R]
    convert (((hasDerivAt_const t 1).add (hasDerivAt_id t)).log hne).sub
      (hasDerivAt_id t) |>.add ((hasDerivAt_pow 2 t).div_const 2) |>.sub
      ((hasDerivAt_pow 3 t).div_const 3) using 1 <;>
      simp only [Pi.add_apply, id_eq] <;> field_simp [hne] <;> ring
  have hGderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt G (t^4/(1+t)) t := by
    intro t ht
    have hne : 1+t ≠ 0 := by linarith [ht.1]
    dsimp [G]
    convert (hRderiv t ht).add ((hasDerivAt_pow 4 t).div_const 4) using 1 <;>
      (try simp only [Pi.add_apply, id_eq]) <;> field_simp [hne] <;> ring
  have hRcont : ContinuousOn R (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hRderiv t ht).continuousAt.continuousWithinAt
  have hGcont : ContinuousOn G (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hGderiv t ht).continuousAt.continuousWithinAt
  have hnegRmono : MonotoneOn (fun t => -R t) (Set.Icc (0 : ℝ) 1) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hRcont.neg
      (fun t ht => by
        have htio : t ∈ Set.Ioo (0 : ℝ) 1 := by
          simpa only [interior_Icc] using ht
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨htio.1.le, htio.2.le⟩
        exact (hRderiv t ht').neg.hasDerivWithinAt)
      (fun t ht => by
        have htio : t ∈ Set.Ioo (0 : ℝ) 1 := by
          simpa only [interior_Icc] using ht
        have heq : -(-t^3/(1+t)) = t^3/(1+t) := by ring
        rw [heq]
        exact div_nonneg (pow_nonneg htio.1.le 3) (by linarith [htio.1]))
  have hGmono : MonotoneOn G (Set.Icc (0 : ℝ) 1) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hGcont
      (fun t ht => by
        have htio : t ∈ Set.Ioo (0 : ℝ) 1 := by
          simpa only [interior_Icc] using ht
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨htio.1.le, htio.2.le⟩
        exact (hGderiv t ht').hasDerivWithinAt)
      (fun t ht => by
        have htio : t ∈ Set.Ioo (0 : ℝ) 1 := by
          simpa only [interior_Icc] using ht
        exact div_nonneg (pow_nonneg htio.1.le 4) (by linarith [htio.1]))
  have hy : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy0, hy1⟩
  have hRle : R y ≤ 0 := by
    have := hnegRmono (Set.left_mem_Icc.mpr (by norm_num)) hy hy0
    simpa [R] using this
  have hRlower : -(y^4/4) ≤ R y := by
    have := hGmono (Set.left_mem_Icc.mpr (by norm_num)) hy hy0
    have hzero : G 0 = 0 := by norm_num [G, R]
    rw [hzero] at this
    dsimp [G] at this
    linarith
  rw [abs_of_nonpos hRle]
  linarith

end FRSB.ZeroTemperature.AppendixA
