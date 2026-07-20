import Mathlib

/-! # Appendix A, Lemma A.1: uniform differentiated remainder bounds -/

namespace FRSB.ZeroTemperature.AppendixA

/-- **Active Appendix A, Lemma `lem:app-endpoint-expansion`: literal uniform
bounds for spatial derivative orders one through four.**

These are explicit constants for the rational derivatives proved in
`logCosh_remainder_firstFourDerivatives`. -/
theorem logCosh_remainder_derivatives_uniformBounds
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |2*y^4/(1+y)| ≤ 2*y^4 ∧
    |-4*y^4*(4+3*y)/(1+y)^2| ≤ 28*y^4 ∧
    |8*y^4*(16+23*y+9*y^2)/(1+y)^3| ≤ 384*y^4 ∧
    |-16*y^4*(64+131*y+100*y^2+27*y^3)/(1+y)^4| ≤ 5152*y^4 := by
  have hy4 : 0 ≤ y^4 := by positivity
  have hden : 0 < 1+y := by linarith
  have hy2 : y^2 ≤ 1 := pow_le_one₀ (n := 2) hy0 hy1
  have hy3 : y^3 ≤ 1 := pow_le_one₀ (n := 3) hy0 hy1
  have hp2 : 0 ≤ 4+3*y := by linarith
  have hp3 : 0 ≤ 16+23*y+9*y^2 := by positivity
  have hp4 : 0 ≤ 64+131*y+100*y^2+27*y^3 := by positivity
  constructor
  · rw [abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) hy4) hden.le)]
    apply (div_le_iff₀ hden).2
    nlinarith
  constructor
  · rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hy4) hp2)
      (sq_nonneg (1+y)))]
    have heq : -(-4*y^4*(4+3*y)/(1+y)^2) =
        4*y^4*(4+3*y)/(1+y)^2 := by ring
    rw [heq]
    apply (div_le_iff₀ (sq_pos_of_pos hden)).2
    nlinarith [sq_nonneg y, sq_nonneg (1+y)]
  constructor
  · rw [abs_of_nonneg (div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hy4) hp3)
      (pow_nonneg hden.le 3))]
    apply (div_le_iff₀ (pow_pos hden 3)).2
    have hpoly : 16+23*y+9*y^2 ≤ 48 := by nlinarith
    calc
      8*y^4*(16+23*y+9*y^2) ≤ 8*y^4*48 :=
        mul_le_mul_of_nonneg_left hpoly (mul_nonneg (by norm_num) hy4)
      _ = 384*y^4 := by ring
      _ ≤ 384*y^4*(1+y)^3 := by
        apply le_mul_of_one_le_right (mul_nonneg (by norm_num) hy4)
        exact one_le_pow₀ (by linarith)
  · rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hy4) hp4)
      (pow_nonneg hden.le 4))]
    have heq : -(-16*y^4*(64+131*y+100*y^2+27*y^3)/(1+y)^4) =
        16*y^4*(64+131*y+100*y^2+27*y^3)/(1+y)^4 := by ring
    rw [heq]
    apply (div_le_iff₀ (pow_pos hden 4)).2
    have hpoly : 64+131*y+100*y^2+27*y^3 ≤ 322 := by nlinarith
    calc
      16*y^4*(64+131*y+100*y^2+27*y^3) ≤ 16*y^4*322 :=
        mul_le_mul_of_nonneg_left hpoly (mul_nonneg (by norm_num) hy4)
      _ = 5152*y^4 := by ring
      _ ≤ 5152*y^4*(1+y)^4 := by
        apply le_mul_of_one_le_right (mul_nonneg (by norm_num) hy4)
        exact one_le_pow₀ (by linarith)

end FRSB.ZeroTemperature.AppendixA
