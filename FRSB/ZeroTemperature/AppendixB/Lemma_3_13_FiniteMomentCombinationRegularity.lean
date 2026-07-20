import FRSB.ZeroTemperature.AppendixB.Lemma_3_13_MomentGeneratorRegularity
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Appendix B: finite moment combinations in the generator

The generator `L_g P` in the active proof of Lemma 3.13 is affine in `g`.
After expectation, its value is therefore a finite sum of ordinary polynomial
moments and `gamma` times polynomial moments.  This file verifies the
regularity closure and composes it with the moment derivative identity.
-/

namespace FRSB.ZeroTemperature

/-- Finite sums of polynomial moments with coefficients affine in a `C^r`
function `gamma` are `C^r`.  If such a sum is the certified derivative of a
moment, that moment is `C^(r+1)`.

This is the deterministic induction step immediately following
`eq:zt-polynomial-moment-derivative`.  The constants `a i` and `b i` encode,
respectively, the diffusion and drift coefficients in `L_g P`. -/
theorem lemma_3_13_finite_moment_generator_contDiff
    {n : ℕ} (r : ℕ) (gamma moment : ℝ → ℝ)
    (moments : Fin n → ℝ → ℝ) (a b : Fin n → ℝ)
    (hgamma : ContDiff ℝ r gamma)
    (hmoments : ∀ i, ContDiff ℝ r (moments i))
    (hderiv : ∀ t, HasDerivAt moment
      (∑ i : Fin n, (a i + b i * gamma t) * moments i t) t) :
    let generatorMoment := fun t =>
      ∑ i : Fin n, (a i + b i * gamma t) * moments i t
    ContDiff ℝ r generatorMoment ∧ ContDiff ℝ (r + 1) moment := by
  dsimp only
  have hterms : ∀ i : Fin n,
      ContDiff ℝ r (fun t => (a i + b i * gamma t) * moments i t) := by
    intro i
    have hb : ContDiff ℝ r (fun t : ℝ => b i * gamma t) :=
      contDiff_const.mul hgamma
    have hab : ContDiff ℝ r (fun t : ℝ => a i + b i * gamma t) :=
      contDiff_const.add hb
    exact hab.mul (hmoments i)
  have hgenerator : ContDiff ℝ r
      (fun t => ∑ i : Fin n, (a i + b i * gamma t) * moments i t) := by
    exact ContDiff.sum fun i _ => hterms i
  exact ⟨hgenerator,
    lemma_3_13_moment_contDiff_succ_of_generator r moment
      (fun t => ∑ i : Fin n, (a i + b i * gamma t) * moments i t)
      hderiv hgenerator⟩

end FRSB.ZeroTemperature
