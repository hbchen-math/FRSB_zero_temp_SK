import FRSB.Basic

/-!
# Fixed-slope algebra

This file checks the pointwise algebra in `lem:zt-fixed-slope`, after the
chain rule and PDE differentiation identities have been supplied. It covers
the algebra behind `eq:zt-Bt-fixed-x`, `eq:zt-ct-fixed-B`,
`eq:zt-Phi-B`, and `eq:zt-Phi-time`.
-/

namespace FRSB.ZeroTemperature

/-- The first chain of equalities in `eq:zt-Bt-fixed-x`. -/
theorem fixed_x_Bt_chain {m B c D z K : ℝ}
    (hD : D = -2 * c * z) (hKB : K * B = z - m * B) :
    -(1 / 2 : ℝ) * (D + 2 * m * B * c) = c * (z - m * B) ∧
      c * (z - m * B) = c * K * B := by
  constructor
  · rw [hD]
    ring
  · rw [← hKB]
    ring

/-- Cancellation in the fixed-slope computation of `c_t`. -/
theorem fixed_slope_cancellation {c cB K B KB : ℝ} :
    c * (cB * K * B + c * (K + B * KB)) - c * cB * K * B =
      c ^ 2 * (K + B * KB) := by
  ring

/-- The identity `z = (m + K) B` away from `B = 0`. -/
theorem z_eq_m_add_K_mul {m B z K : ℝ}
    (hB : B ≠ 0) (hK : K = z / B - m) :
    z = (m + K) * B := by
  field_simp [hB] at hK
  nlinarith

/-- The second identity in `eq:zt-z-KJ-identities`. -/
theorem zB_eq_m_add_J {m B K KB J zB : ℝ}
    (hJ : J = K + B * KB) (hzB : zB = m + K + B * KB) :
    zB = m + J := by
  rw [hJ]
  simpa [add_assoc] using hzB

/-- Pointwise algebra behind `eq:zt-Phi-B`. -/
theorem phi_B_identity {m cB z zB J phiB : ℝ}
    (hcB : cB = -2 * z) (hzB : zB = m + J)
    (hphiB : phiB = 4 * z * zB - m * cB) :
    phiB = 2 * z * (2 * J + 3 * m) := by
  rw [hphiB, hcB, hzB]
  ring

/-- Pointwise algebra behind the equality in `eq:zt-Phi-time`. -/
theorem phi_t_identity {m c z J JB ct zt phi G phiT : ℝ}
    (hct : ct = c ^ 2 * J)
    (hzt : zt = 2 * c * z * J - (1 / 2 : ℝ) * c ^ 2 * JB)
    (hphi : phi = 2 * z ^ 2 - m * c)
    (hG : G = 2 * c * z * (3 * z * J - c * JB))
    (hphiT : phiT = 4 * z * zt - m * ct) :
    phiT = c * J * phi + G := by
  rw [hphiT, hct, hzt, hphi, hG]
  ring

/-- The five sign inequalities in `eq:zt-zero-temp-five` imply
`G ≥ 0` in `eq:zt-Phi-time`. -/
theorem G_nonnegative {c z J JB : ℝ}
    (hc : 0 ≤ c) (hz : 0 ≤ z)
    (hmain : c * JB ≤ 3 * z * J) :
    0 ≤ 2 * c * z * (3 * z * J - c * JB) := by
  have hfactor : 0 ≤ 3 * z * J - c * JB := sub_nonneg.mpr hmain
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc) hz) hfactor

end FRSB.ZeroTemperature
