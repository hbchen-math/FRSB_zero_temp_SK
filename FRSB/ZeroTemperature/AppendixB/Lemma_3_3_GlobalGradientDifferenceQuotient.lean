import Mathlib.Analysis.Convex.Deriv

/-!
# Appendix B: global gradient convergence in Lemma 3.3

This file formalizes the difference-quotient estimate used at the end of the
active proof of `lem:zt-parabolic-stability`.
-/

namespace FRSB.ZeroTemperature

/-- The manuscript's global derivative estimate
`|v_{n,x} - v_x| ≤ M h + 2 ε / h`.

Convexity puts each derivative between adjacent secant slopes.  Uniform
`ε`-closeness perturbs a secant numerator by at most `2 ε`, while the four
final hypotheses are the local consequences of the common second-derivative
bound `M` used in the paper. -/
theorem lemma_3_3_global_gradient_difference_quotient
    (f g : ℝ → ℝ) (x f'x g'x M ε h : ℝ)
    (hfconv : ConvexOn ℝ Set.univ f)
    (hgconv : ConvexOn ℝ Set.univ g)
    (hf'x : HasDerivAt f f'x x)
    (hg'x : HasDerivAt g g'x x)
    (hf'plus : ∃ f'plus, HasDerivAt f f'plus (x + h) ∧
      f'plus ≤ f'x + M * h)
    (hg'plus : ∃ g'plus, HasDerivAt g g'plus (x + h) ∧
      g'plus ≤ g'x + M * h)
    (hf'minus : ∃ f'minus, HasDerivAt f f'minus (x - h) ∧
      f'x - M * h ≤ f'minus)
    (hg'minus : ∃ g'minus, HasDerivAt g g'minus (x - h) ∧
      g'x - M * h ≤ g'minus)
    (huniform : ∀ y, |f y - g y| ≤ ε)
    (hh : 0 < h) :
    |f'x - g'x| ≤ M * h + 2 * ε / h := by
  have _hg_differentiable : DifferentiableAt ℝ g x := hg'x.differentiableAt
  obtain ⟨f'plus, hf'plus_deriv, hf'plus_bound⟩ := hf'plus
  obtain ⟨g'plus, hg'plus_deriv, hg'plus_bound⟩ := hg'plus
  obtain ⟨f'minus, hf'minus_deriv, hf'minus_bound⟩ := hf'minus
  obtain ⟨g'minus, hg'minus_deriv, hg'minus_bound⟩ := hg'minus
  have hxh : x < x + h := by linarith
  have hmx : x - h < x := by linarith
  have hfg_y (y : ℝ) : f y ≤ g y + ε := by
    have := (le_abs_self (f y - g y)).trans (huniform y)
    linarith
  have hgf_y (y : ℝ) : g y ≤ f y + ε := by
    have := (neg_le_abs (f y - g y)).trans (huniform y)
    linarith
  have hupper : f'x - g'x ≤ M * h + 2 * ε / h := by
    have hfslope : f'x ≤ slope f x (x + h) :=
      hfconv.le_slope_of_hasDerivAt (Set.mem_univ x)
        (Set.mem_univ (x + h)) hxh hf'x
    have hgslope : slope g x (x + h) ≤ g'plus :=
      hgconv.slope_le_of_hasDerivAt (Set.mem_univ x)
        (Set.mem_univ (x + h)) hxh hg'plus_deriv
    have hnum : f (x + h) - f x ≤
        (g (x + h) - g x) + 2 * ε := by
      have h1 := hfg_y (x + h)
      have h2 := hgf_y x
      linarith
    have hslope_compare : slope f x (x + h) ≤
        slope g x (x + h) + 2 * ε / h := by
      rw [slope_def_field, slope_def_field]
      simp only [add_sub_cancel_left]
      simpa [add_div] using (div_le_div_iff_of_pos_right hh).2 hnum
    linarith
  have hlower : -(M * h + 2 * ε / h) ≤ f'x - g'x := by
    have hgslope : g'minus ≤ slope g (x - h) x :=
      hgconv.le_slope_of_hasDerivAt (Set.mem_univ (x - h))
        (Set.mem_univ x) hmx hg'minus_deriv
    have hfslope : slope f (x - h) x ≤ f'x :=
      hfconv.slope_le_of_hasDerivAt (Set.mem_univ (x - h))
        (Set.mem_univ x) hmx hf'x
    have hnum : g x - g (x - h) ≤
        (f x - f (x - h)) + 2 * ε := by
      have h1 := hgf_y x
      have h2 := hfg_y (x - h)
      linarith
    have hslope_compare : slope g (x - h) x ≤
        slope f (x - h) x + 2 * ε / h := by
      rw [slope_def_field, slope_def_field]
      simp only [sub_sub_cancel]
      simpa [add_div] using (div_le_div_iff_of_pos_right hh).2 hnum
    linarith
  exact abs_le.2 ⟨hlower, hupper⟩

end FRSB.ZeroTemperature
