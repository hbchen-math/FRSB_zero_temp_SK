import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

/-!
# Appendix A, Lemma A.2: exponential transformation

This is the transformation `w(r,B)=exp(-λr)v(r,B)` used in the printed proof
of the degenerate-strip comparison lemma.
-/

namespace FRSB.ZeroTemperature.AppendixA

/-- **Active Appendix A, Lemma `lem:app-comparison`: exponential transform.**

If `v_r = d v_BB + b v_B + c v + F`, multiplying by `exp (-λr)` and using
`w_r = exp(-λr)(v_r-λv)` produces the transformed equation with zero-order
coefficient `c-λ`.  A strict upper bound `c<λ`, source nonnegativity, and the
sign of `v` are all preserved in the forms required by the transformed
comparison theorem. -/
theorem exponentialTransform_equation_and_signs
    {ι : Type*} (time : ι → ℝ)
    (v vr vB vBB d b c F : ι → ℝ) (lam : ℝ)
    (hpde : ∀ z, vr z = d z * vBB z + b z * vB z + c z * v z + F z)
    (hc : ∀ z, c z < lam)
    (hF : ∀ z, 0 ≤ F z) :
    let factor : ι → ℝ := fun z => Real.exp (-lam * time z)
    let w : ι → ℝ := fun z => factor z * v z
    let wr : ι → ℝ := fun z => factor z * (vr z - lam * v z)
    let wB : ι → ℝ := fun z => factor z * vB z
    let wBB : ι → ℝ := fun z => factor z * vBB z
    let Ft : ι → ℝ := fun z => factor z * F z
    (∀ z, wr z = d z * wBB z + b z * wB z + (c z - lam) * w z + Ft z) ∧
    (∀ z, c z - lam < 0) ∧
    (∀ z, 0 ≤ Ft z) ∧
    (∀ z, 0 ≤ v z → 0 ≤ w z) := by
  dsimp
  constructor
  · intro z
    rw [hpde z]
    ring
  constructor
  · exact fun z => sub_neg.mpr (hc z)
  constructor
  · exact fun z => mul_nonneg (Real.exp_pos _).le (hF z)
  · exact fun z hz => mul_nonneg (Real.exp_pos _).le hz

end FRSB.ZeroTemperature.AppendixA
