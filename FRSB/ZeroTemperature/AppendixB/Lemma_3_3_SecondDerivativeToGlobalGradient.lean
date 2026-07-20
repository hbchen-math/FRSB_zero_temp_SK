import FRSB.ZeroTemperature.AppendixB.Lemma_3_3_GlobalGradientDifferenceQuotient
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Appendix B: deriving the gradient estimate from the second-derivative bound

This file discharges the local derivative-change hypotheses in the existing difference-quotient
theorem directly from the common global second-derivative bound in Lemma 3.3.
-/

namespace FRSB.ZeroTemperature

/-- The manuscript estimate
`|f'(x)-g'(x)| ≤ M h + 2 epsilon / h` follows from convexity, uniform function closeness,
and a common global bound `M` on the absolute second derivatives.

The functions `df` and `dg` are explicit first derivatives of `f` and `g`; bounding their
derivatives is exactly the global second-spatial-derivative hypothesis used in Appendix B. -/
theorem lemma_3_3_global_gradient_of_second_derivative_bound
    (f g df dg : ℝ → ℝ) (x M epsilon h : ℝ)
    (hfconv : ConvexOn ℝ Set.univ f)
    (hgconv : ConvexOn ℝ Set.univ g)
    (hfderiv : ∀ y, HasDerivAt f (df y) y)
    (hgderiv : ∀ y, HasDerivAt g (dg y) y)
    (hdfdiff : Differentiable ℝ df)
    (hdgdiff : Differentiable ℝ dg)
    (hdfsecond : ∀ y, |deriv df y| ≤ M)
    (hdgsecond : ∀ y, |deriv dg y| ≤ M)
    (hM : 0 ≤ M)
    (huniform : ∀ y, |f y - g y| ≤ epsilon)
    (hh : 0 < h) :
    |df x - dg x| ≤ M * h + 2 * epsilon / h := by
  let C : NNReal := ⟨M, hM⟩
  have hdfnorm : ∀ y, ‖deriv df y‖₊ ≤ C := by
    intro y
    apply_mod_cast hdfsecond y
  have hdgnorm : ∀ y, ‖deriv dg y‖₊ ≤ C := by
    intro y
    apply_mod_cast hdgsecond y
  have hdfLip : LipschitzWith C df :=
    lipschitzWith_of_nnnorm_deriv_le hdfdiff hdfnorm
  have hdgLip : LipschitzWith C dg :=
    lipschitzWith_of_nnnorm_deriv_le hdgdiff hdgnorm
  have hdfplus : df (x + h) ≤ df x + M * h := by
    have hdist := hdfLip.dist_le_mul x (x + h)
    simp [Real.dist_eq, C, abs_of_pos hh] at hdist
    change |df x - df (x + h)| ≤ M * h at hdist
    rw [abs_sub_comm] at hdist
    have habs := le_abs_self (df (x + h) - df x)
    linarith
  have hdgplus : dg (x + h) ≤ dg x + M * h := by
    have hdist := hdgLip.dist_le_mul x (x + h)
    simp [Real.dist_eq, C, abs_of_pos hh] at hdist
    change |dg x - dg (x + h)| ≤ M * h at hdist
    rw [abs_sub_comm] at hdist
    have habs := le_abs_self (dg (x + h) - dg x)
    linarith
  have hdfminus : df x - M * h ≤ df (x - h) := by
    have hdist := hdfLip.dist_le_mul (x - h) x
    simp [Real.dist_eq, C, abs_of_pos hh] at hdist
    change |df (x - h) - df x| ≤ M * h at hdist
    have habs := (neg_le_abs (df (x - h) - df x)).trans hdist
    linarith
  have hdgminus : dg x - M * h ≤ dg (x - h) := by
    have hdist := hdgLip.dist_le_mul (x - h) x
    simp [Real.dist_eq, C, abs_of_pos hh] at hdist
    change |dg (x - h) - dg x| ≤ M * h at hdist
    have habs := (neg_le_abs (dg (x - h) - dg x)).trans hdist
    linarith
  exact lemma_3_3_global_gradient_difference_quotient
    f g x (df x) (dg x) M epsilon h hfconv hgconv
    (hfderiv x) (hgderiv x)
    ⟨df (x + h), hfderiv (x + h), hdfplus⟩
    ⟨dg (x + h), hgderiv (x + h), hdgplus⟩
    ⟨df (x - h), hfderiv (x - h), hdfminus⟩
    ⟨dg (x - h), hgderiv (x - h), hdgminus⟩
    huniform hh

end FRSB.ZeroTemperature
