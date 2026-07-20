import FRSB.ZeroTemperature.Smoothness.Proposition_4_4_BootstrapToSmooth
import FRSB.ZeroTemperature.Smoothness.Proposition_4_4_QuotientRegularity

/-!
# Proposition 4.4: the moment-quotient bootstrap

This file formalizes the complete deterministic induction at the end of
`prop:zt-smoothness`.  The stochastic moment lemma is represented by the
explicit regularity-improvement hypothesis `moments_improve`; it is not hidden
as an axiom.
-/

namespace FRSB.ZeroTemperature.Smoothness

open Set
open scoped ContDiff

/-- Suppose an order parameter is pointwise the quotient of two moment
functions with positive denominator.  If `C^r` regularity of the order
parameter makes both moments `C^(r+1)`, then a continuous order parameter is
smooth.

This is the induction in Proposition `prop:zt-smoothness`, applied in the
paper with numerator `E[D(t,X_t)^2]` and denominator
`2 E[C(t,X_t)^3]` on each compact interval `[0,T]`. -/
theorem contDiffOn_top_of_momentQuotient_bootstrap
    {s : Set ℝ} {gamma numerator denominator : ℝ → ℝ}
    (gamma_eq : ∀ x ∈ s, gamma x = numerator x / denominator x)
    (base : ContDiffOn ℝ 0 gamma s)
    (denominator_pos : ∀ x ∈ s, 0 < denominator x)
    (moments_improve : ∀ r : ℕ,
      ContDiffOn ℝ r gamma s →
        ContDiffOn ℝ (r + 1) numerator s ∧
        ContDiffOn ℝ (r + 1) denominator s) :
    ContDiffOn ℝ ∞ gamma s := by
  apply contDiffOn_top_of_zero_of_succ base
  intro r hgamma
  obtain ⟨hnum, hden⟩ := moments_improve r hgamma
  exact (contDiffOn_div_of_pos hnum hden denominator_pos).congr
    (fun x hx => gamma_eq x hx)

end FRSB.ZeroTemperature.Smoothness
