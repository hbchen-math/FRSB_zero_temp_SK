import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Appendix B: deterministic moment-generator regularity

This file isolates the deterministic calculus implication used to conclude
the active Appendix B proof of `lem:zt-polynomial-moment-regularity`.
-/

namespace FRSB.ZeroTemperature

/-- A moment function is `C^(r+1)` when its derivative is the generator
moment and that generator moment is `C^r`.

In `eq:zt-polynomial-moment-derivative`, `moment` is `M_P` and `generatorMoment`
is the expectation of `L_{gamma(t)} P`.  The probabilistic work establishes
the displayed derivative identity; the final induction in Appendix B shows
that its right-hand side is `C^r`.  This theorem verifies the complete
deterministic implication from those two facts to `M_P ∈ C^(r+1)`. -/
theorem lemma_3_13_moment_contDiff_succ_of_generator
    (r : ℕ) (moment generatorMoment : ℝ → ℝ)
    (hderiv : ∀ t, HasDerivAt moment (generatorMoment t) t)
    (hgenerator : ContDiff ℝ r generatorMoment) :
    ContDiff ℝ (r + 1) moment := by
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun t => (hderiv t).differentiableAt, ?_, ?_⟩
  · simp
  · have hderiv_eq : deriv moment = generatorMoment := by
      funext t
      exact (hderiv t).deriv
    rw [hderiv_eq]
    exact hgenerator

end FRSB.ZeroTemperature
