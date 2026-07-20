import FRSB.ZeroTemperature.AppendixB.Lemma_3_13_FiniteMomentCombinationRegularity
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Appendix B: interval and endpoint regularity for polynomial moments

This file gives the compact-interval version of the deterministic induction in Lemma 3.13.  All
derivatives are taken within `[0,T]`, so the assertions at zero and `T` are genuinely one-sided.
-/

namespace FRSB.ZeroTemperature

open Set

/-- On `[0,T]`, a finite affine-in-`gamma` combination of `C^r` moments is `C^r`.  If it is the
within-interval derivative of `moment`, then `moment` is `C^(r+1)` on the closed interval, including
the right derivative at zero and left derivative at `T`.

The finite coefficients encode the polynomial generator `L_(gamma(t)) P` in
`eq:zt-polynomial-moment-derivative`. -/
theorem lemma_3_13_interval_moment_generator_regularity
    {n : ℕ} (r : ℕ) {T : ℝ} (hT : 0 < T)
    (gamma moment : ℝ → ℝ)
    (moments : Fin n → ℝ → ℝ) (a b : Fin n → ℝ)
    (hgamma : ContDiffOn ℝ r gamma (Icc 0 T))
    (hmoments : ∀ i, ContDiffOn ℝ r (moments i) (Icc 0 T))
    (hderiv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt moment
        (∑ i : Fin n, (a i + b i * gamma t) * moments i t) (Icc 0 T) t) :
    let generatorMoment := fun t ↦
      ∑ i : Fin n, (a i + b i * gamma t) * moments i t
    ContDiffOn ℝ r generatorMoment (Icc 0 T) ∧
      HasDerivWithinAt moment (generatorMoment 0) (Icc 0 T) 0 ∧
      HasDerivWithinAt moment (generatorMoment T) (Icc 0 T) T ∧
      ContDiffOn ℝ (r + 1) moment (Icc 0 T) := by
  dsimp only
  let generatorMoment : ℝ → ℝ := fun t ↦
    ∑ i : Fin n, (a i + b i * gamma t) * moments i t
  have hterms : ∀ i : Fin n,
      ContDiffOn ℝ r (fun t ↦ (a i + b i * gamma t) * moments i t) (Icc 0 T) := by
    intro i
    have hb : ContDiffOn ℝ r (fun t : ℝ ↦ b i * gamma t) (Icc 0 T) :=
      contDiffOn_const.mul hgamma
    exact (contDiffOn_const.add hb).mul (hmoments i)
  have hgenerator : ContDiffOn ℝ r generatorMoment (Icc 0 T) := by
    exact ContDiffOn.sum fun i _ ↦ hterms i
  have hdiff : DifferentiableOn ℝ moment (Icc 0 T) := by
    intro t ht
    exact (hderiv t ht).differentiableWithinAt
  have hderiv_eq : ∀ t ∈ Icc (0 : ℝ) T,
      derivWithin moment (Icc 0 T) t = generatorMoment t := by
    intro t ht
    exact (hderiv t ht).derivWithin (uniqueDiffOn_Icc hT t ht)
  have hderiv_regular :
      ContDiffOn ℝ r (derivWithin moment (Icc 0 T)) (Icc 0 T) :=
    hgenerator.congr fun t ht ↦ hderiv_eq t ht
  have hmoment : ContDiffOn ℝ (r + 1) moment (Icc 0 T) := by
    rw [contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hT)]
    exact ⟨hdiff, by simp, hderiv_regular⟩
  have hzero_mem : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hT_mem : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  exact ⟨hgenerator, hderiv 0 hzero_mem, hderiv T hT_mem, hmoment⟩

end FRSB.ZeroTemperature
