import FRSB.PositiveTemperature.EndpointMoments
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Deterministic assembly of the endpoint Itô identities

This file isolates the calculus after the stochastic Itô formulas have been
established.  Self-consistency makes `Gamma(s) = s`; comparing derivatives
gives the second endpoint moment.  The resulting constancy of the curvature
moment, combined with its endpoint derivative formula, gives the atom balance.
-/

namespace FRSB.PositiveTemperature

open Set

noncomputable section

/-- The endpoint differentiability data produced by the two Itô formulas in
`prop:ft-endpoint-identities`. -/
structure EndpointItoData (β q c m2 m3 : ℝ) where
  qPos : 0 < q
  gamma : ℝ → ℝ
  curvatureMoment : ℝ → ℝ
  gammaEq : Set.EqOn gamma id (Icc 0 q)
  gammaDeriv : ∀ s ∈ Icc 0 q,
    HasDerivWithinAt gamma (β ^ 2 * curvatureMoment s) (Icc 0 q) s
  curvatureEndpoint : curvatureMoment q = m2
  curvatureDerivEndpoint :
    HasDerivWithinAt curvatureMoment
      (β ^ 2 * (4 * (m2 - m3) - 2 * (1 - c) * m3)) (Icc 0 q) q

namespace EndpointItoData

theorem betaSq_mul_curvature_eq_one {β q c m2 m3 : ℝ}
    (d : EndpointItoData β q c m2 m3) {s : ℝ} (hs : s ∈ Icc 0 q) :
    β ^ 2 * d.curvatureMoment s = 1 := by
  have hid : HasDerivWithinAt id 1 (Icc 0 q) s :=
    (hasDerivAt_id s).hasDerivWithinAt
  have hgammaOne : HasDerivWithinAt d.gamma 1 (Icc 0 q) s := by
    apply hid.congr_of_mem
    · intro x hx
      exact d.gammaEq hx
    · exact hs
  exact (uniqueDiffOn_Icc d.qPos s hs).eq_deriv (Icc 0 q)
    (d.gammaDeriv s hs) hgammaOne

/-- The second identity `β² E C² = 1`. -/
theorem secondMoment {β q c m2 m3 : ℝ} (d : EndpointItoData β q c m2 m3) :
    β ^ 2 * m2 = 1 := by
  have hq : q ∈ Icc (0 : ℝ) q := ⟨d.qPos.le, le_rfl⟩
  simpa [d.curvatureEndpoint] using d.betaSq_mul_curvature_eq_one hq

theorem curvature_eq_const {β q c m2 m3 : ℝ}
    (hβ : 0 < β) (d : EndpointItoData β q c m2 m3) {s : ℝ}
    (hs : s ∈ Icc 0 q) : d.curvatureMoment s = 1 / β ^ 2 := by
  have h := d.betaSq_mul_curvature_eq_one hs
  apply (eq_div_iff (ne_of_gt (sq_pos_of_pos hβ))).2
  simpa [mul_comm] using h

/-- The endpoint atom balance obtained from the second differentiated moment
identity. -/
theorem balance {β q c m2 m3 : ℝ} (hβ : 0 < β)
    (d : EndpointItoData β q c m2 m3) :
    0 = 4 * (m2 - m3) - 2 * (1 - c) * m3 := by
  let S : Set ℝ := Icc 0 q
  have hq : q ∈ S := ⟨d.qPos.le, le_rfl⟩
  have hconst : HasDerivWithinAt (fun _ : ℝ ↦ 1 / β ^ 2) 0 S q :=
    (hasDerivAt_const q (1 / β ^ 2)).hasDerivWithinAt
  have hcurvZero : HasDerivWithinAt d.curvatureMoment 0 S q := by
    apply hconst.congr_of_mem
    · intro s hs
      exact d.curvature_eq_const hβ hs
    · exact hq
  have heq := (uniqueDiffOn_Icc d.qPos q hq).eq_deriv S
    d.curvatureDerivEndpoint hcurvZero
  have hβsq : 0 < β ^ 2 := sq_pos_of_pos hβ
  nlinarith

end EndpointItoData

end

end FRSB.PositiveTemperature
