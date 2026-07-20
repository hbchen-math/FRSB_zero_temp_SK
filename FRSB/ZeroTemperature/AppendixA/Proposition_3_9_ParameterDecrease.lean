import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Appendix A, Proposition 3.9: decreasing the cascade parameter

This file formalizes the parameter-replacement argument in the active
completion of Proposition `prop:zt-finite-KJ`, immediately after
`prop:app-fixed-parameter`.
-/

namespace FRSB.ZeroTemperature.AppendixA

/-- **Active Appendix A, completion of Proposition `prop:zt-finite-KJ`.**

Replacing `a` by `b<a` adds the positive constant `a-b` to both `K` and `J`,
leaves their spatial derivatives unchanged, and changes the derivative of
the weighted quantity `W J` by `(a-b) W'`.  Consequently all five inequalities
`K,K_B,J,J_B ≥ 0` and `(WJ)_B ≤ 0` are preserved whenever `W'≤0`.

In the paper `W=c^{3/2}` and `W'=(3/2)c^{1/2}c_B≤0`. -/
theorem parameterDecrease_preserves_fiveInequalities
    {D : Set ℝ} {a b : ℝ}
    (K J KB JB W W' weightedDeriv : ℝ → ℝ)
    (hab : b < a)
    (hWderiv : ∀ x ∈ D, HasDerivAt W (W' x) x)
    (hweightedDeriv : ∀ x ∈ D,
      HasDerivAt (fun y => W y * J y) (weightedDeriv x) x)
    (hineq : ∀ x ∈ D,
      0 ≤ K x ∧ 0 ≤ KB x ∧ 0 ≤ J x ∧ 0 ≤ JB x ∧ weightedDeriv x ≤ 0)
    (hW' : ∀ x ∈ D, W' x ≤ 0) :
    ∀ x ∈ D,
      0 ≤ K x + (a - b) ∧
      0 ≤ KB x ∧
      0 ≤ J x + (a - b) ∧
      0 ≤ JB x ∧
      HasDerivAt (fun y => W y * (J y + (a - b)))
        (weightedDeriv x + (a - b) * W' x) x ∧
      weightedDeriv x + (a - b) * W' x ≤ 0 := by
  intro x hx
  obtain ⟨hK, hKB, hJ, hJB, hweighted⟩ := hineq x hx
  have hdelta : 0 < a - b := sub_pos.mpr hab
  refine ⟨by linarith, hKB, by linarith, hJB, ?_, ?_⟩
  · have hsum : HasDerivAt
        (fun y => W y * J y + (a - b) * W y)
        (weightedDeriv x + (a - b) * W' x) x :=
      HasDerivAt.add (hweightedDeriv x hx) ((hWderiv x hx).const_mul (a - b))
    convert hsum using 1
    funext y
    ring
  · exact add_nonpos hweighted
      (mul_nonpos_of_nonneg_of_nonpos hdelta.le (hW' x hx))

end FRSB.ZeroTemperature.AppendixA
