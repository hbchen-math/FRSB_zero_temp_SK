import Mathlib

/-!
# Proposition 3.9: initialization by `log cosh`

This file verifies the initial-function calculation in the active completion of
`prop:zt-finite-KJ` in Appendix A.
-/

namespace FRSB.ZeroTemperature.AppendixA

open Real Set

/-- For the initial pair `(f,a) = (log cosh,1)`, inverse slope coordinates give
`B = tanh x`, `c(B)=1-B^2`, `z(B)=B`, and hence `K(B)=J(B)=0` on `0<B<1`.

The last two equalities are written directly from the manuscript definitions
`K=z/B-a` and `J=K+B K_B`. -/
theorem initialLogCosh_slope_curvature_KJ
    {B : ℝ} (hB : B ∈ Ioo (0 : ℝ) 1) :
    let f : ℝ → ℝ := fun x => log (cosh x)
    let xB := artanh B
    let c : ℝ → ℝ := fun b => 1 - b ^ 2
    let z : ℝ → ℝ := fun b => -1 / 2 * deriv c b
    let K : ℝ → ℝ := fun _ => 0
    deriv f xB = B ∧ deriv (deriv f) xB = c B ∧
      z B = B ∧ K B = z B / B - 1 ∧ K B = 0 ∧
        K B + B * deriv K B = 0 := by
  dsimp only
  have hcosh_ne (x : ℝ) : cosh x ≠ 0 := (cosh_pos x).ne'
  have hfirst (x : ℝ) :
      HasDerivAt (fun y : ℝ => log (cosh y)) (tanh x) x := by
    simpa [tanh_eq_sinh_div_cosh, div_eq_mul_inv, mul_comm] using
      (hasDerivAt_log (hcosh_ne x)).comp x (hasDerivAt_cosh x)
  have hsecond (x : ℝ) :
      HasDerivAt (fun y : ℝ => tanh y) (1 - tanh x ^ 2) x := by
    have hquot := (hasDerivAt_sinh x).div (hasDerivAt_cosh x) (hcosh_ne x)
    convert hquot using 1
    · funext y
      exact tanh_eq_sinh_div_cosh y
    · rw [tanh_eq_sinh_div_cosh]
      field_simp [hcosh_ne x]
  have hderiv_f : deriv (fun x : ℝ => log (cosh x)) = tanh := by
    funext x
    exact (hfirst x).deriv
  have hslope : deriv (fun x : ℝ => log (cosh x)) (artanh B) = B := by
    rw [hderiv_f, tanh_artanh]
    exact ⟨by linarith [hB.1], hB.2⟩
  have hcurvature :
      deriv (deriv (fun x : ℝ => log (cosh x))) (artanh B) = 1 - B ^ 2 := by
    rw [hderiv_f, (hsecond (artanh B)).deriv, tanh_artanh]
    exact ⟨by linarith [hB.1], hB.2⟩
  have hcderiv : deriv (fun b : ℝ => 1 - b ^ 2) B = -2 * B := by
    simpa [id_eq] using
      ((hasDerivAt_const B (1 : ℝ)).sub ((hasDerivAt_id B).pow 2)).deriv
  have hBne : B ≠ 0 := ne_of_gt hB.1
  refine ⟨hslope, hcurvature, ?_, ?_, rfl, ?_⟩
  · rw [hcderiv]
    ring
  · rw [hcderiv]
    field_simp
    ring
  · simp

end FRSB.ZeroTemperature.AppendixA
