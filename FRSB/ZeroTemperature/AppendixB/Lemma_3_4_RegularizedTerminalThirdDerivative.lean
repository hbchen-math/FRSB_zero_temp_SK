import Mathlib

/-!
# Appendix B: third derivative of the regularized terminal datum

This is the explicit initial sign calculation in the proof of
`lem:zt-regularized-terminal-data`.
-/

namespace FRSB.ZeroTemperature.AppendixB

open Real

/-- The smooth terminal approximation from `eq:zt-terminal-regularization`. -/
noncomputable def regularizedTerminal (lambda x : ℝ) : ℝ :=
  lambda⁻¹ * log (cosh (lambda * x))

/-- For positive `lambda` and `x`, the third derivative of
`lambda⁻¹ log cosh(lambda x)` is strictly negative.  The displayed formula is the manuscript's
`-2 lambda² tanh(lambda x) sech²(lambda x)`, written using `sinh/cosh`. -/
theorem regularizedTerminal_thirdDerivative_formula_and_neg
    {lambda x : ℝ} (hlambda : 0 < lambda) (hx : 0 < x) :
    iteratedDeriv 3 (regularizedTerminal lambda) x =
        -2 * lambda ^ 2 * sinh (lambda * x) / cosh (lambda * x) ^ 3 ∧
      iteratedDeriv 3 (regularizedTerminal lambda) x < 0 := by
  have hlambda_ne : lambda ≠ 0 := ne_of_gt hlambda
  have hcosh_ne (y : ℝ) : cosh (lambda * y) ≠ 0 := (cosh_pos _).ne'
  have hfirst (y : ℝ) :
      HasDerivAt (regularizedTerminal lambda) (sinh (lambda * y) / cosh (lambda * y)) y := by
    have hinner : HasDerivAt (fun z : ℝ ↦ lambda * z) lambda y :=
      by simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul lambda
    have hc : HasDerivAt (fun z : ℝ ↦ cosh (lambda * z))
        (sinh (lambda * y) * lambda) y := (hasDerivAt_cosh _).comp y hinner
    have hlog := (hasDerivAt_log (hcosh_ne y)).comp y hc
    convert hlog.const_mul lambda⁻¹ using 1 <;>
      simp only [regularizedTerminal, div_eq_mul_inv, id_eq] <;>
      field_simp [hlambda_ne] <;> ring
  have hsecond (y : ℝ) :
      HasDerivAt (fun z : ℝ ↦ sinh (lambda * z) / cosh (lambda * z))
        (lambda / cosh (lambda * y) ^ 2) y := by
    have hinner : HasDerivAt (fun z : ℝ ↦ lambda * z) lambda y :=
      by simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul lambda
    have hs : HasDerivAt (fun z : ℝ ↦ sinh (lambda * z))
        (cosh (lambda * y) * lambda) y := (hasDerivAt_sinh _).comp y hinner
    have hc : HasDerivAt (fun z : ℝ ↦ cosh (lambda * z))
        (sinh (lambda * y) * lambda) y := (hasDerivAt_cosh _).comp y hinner
    convert hs.div hc (hcosh_ne y) using 1
    field_simp
    rw [cosh_sq_sub_sinh_sq]
  have hthird (y : ℝ) :
      HasDerivAt (fun z : ℝ ↦ lambda / cosh (lambda * z) ^ 2)
        (-2 * lambda ^ 2 * sinh (lambda * y) / cosh (lambda * y) ^ 3) y := by
    have hinner : HasDerivAt (fun z : ℝ ↦ lambda * z) lambda y :=
      by simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul lambda
    have hc : HasDerivAt (fun z : ℝ ↦ cosh (lambda * z))
        (sinh (lambda * y) * lambda) y := (hasDerivAt_cosh _).comp y hinner
    convert (hasDerivAt_const y lambda).div (hc.pow 2) (pow_ne_zero 2 (hcosh_ne y)) using 1
    simp only [Pi.pow_apply]
    field_simp
    ring
  have hderiv1 : deriv (regularizedTerminal lambda) =
      fun y ↦ sinh (lambda * y) / cosh (lambda * y) := by
    funext y
    exact (hfirst y).deriv
  have hderiv2 : deriv (fun y : ℝ ↦ sinh (lambda * y) / cosh (lambda * y)) =
      fun y ↦ lambda / cosh (lambda * y) ^ 2 := by
    funext y
    exact (hsecond y).deriv
  have hformula : iteratedDeriv 3 (regularizedTerminal lambda) x =
      -2 * lambda ^ 2 * sinh (lambda * x) / cosh (lambda * x) ^ 3 := by
    rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ,
      show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one,
      hderiv1, hderiv2]
    exact (hthird x).deriv
  refine ⟨hformula, ?_⟩
  rw [hformula]
  have hsinh_pos : 0 < sinh (lambda * x) :=
    Real.sinh_pos_iff.mpr (mul_pos hlambda hx)
  have hcosh_pos : 0 < cosh (lambda * x) := cosh_pos _
  have hnum : -2 * lambda ^ 2 * sinh (lambda * x) < 0 := by
    have hcoef : -2 * lambda ^ 2 < 0 := by
      nlinarith [sq_pos_of_pos hlambda]
    exact mul_neg_of_neg_of_pos hcoef hsinh_pos
  exact div_neg_iff.mpr (Or.inr ⟨hnum, pow_pos hcosh_pos 3⟩)

end FRSB.ZeroTemperature.AppendixB
