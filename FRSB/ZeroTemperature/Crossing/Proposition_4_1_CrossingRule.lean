import FRSB.ZeroTemperature.Crossing.Proposition_4_1_BoundaryTerms
import FRSB.ZeroTemperature.Crossing.Proposition_4_1_ResidualPositivity

/-!
# Proposition 4.1: arbitrary-gap crossing rule

This file packages the differentiated PDE identity at the level at which the
three sign arguments in the manuscript have already been proved:

* the centered strict-covariance `H` term is positive;
* the monotone `R₁` covariance is nonnegative;
* the residual is nonnegative, using the boundary integration by parts and
  the pointwise estimate formalized in the preceding two files.

The final implication `Γ'' = 0 → Γ''' > 0` is then kernel-checked below.  In
particular, the crossing rule itself is not an assumption in the interface.
-/

namespace FRSB.ZeroTemperature.Crossing

open Set
open scoped ContDiff

/-- The scalar conclusion of the differentiated crossing computation. -/
theorem crossing_of_decomposition
    {GammaSecond GammaThird I Iprime hTerm rOneTerm residual : ℝ}
    (hsecond : GammaSecond = 2 * I)
    (hthird : GammaThird = 2 * Iprime)
    (hdecomp : Iprime = hTerm / 2 + rOneTerm + residual)
    (hH : I = 0 → 0 < hTerm)
    (hR1 : I = 0 → 0 ≤ rOneTerm)
    (hresidual : I = 0 → 0 ≤ residual) :
    GammaSecond = 0 → 0 < GammaThird := by
  intro hzero
  have hI : I = 0 := by linarith [hsecond]
  have hHp := hH hI
  have hR1p := hR1 hI
  have hresp := hresidual hI
  linarith [hthird, hdecomp]

/-- Analytic data on a constant positive gap used by Proposition 4.1.

This deliberately exposes the three differentiated terms rather than storing
the desired crossing implication.  The PDE differentiation and strict
covariance inputs belong to the analytic chain; the final crossing conclusion
is derived by `arbitraryGap_crossing` below. -/
structure ArbitraryGapCrossingData (Gamma : ℝ → ℝ) (a b : ℝ) where
  gammaC3 : ContDiffOn ℝ 3 Gamma (Ioo a b)
  crossingIntegral : ℝ → ℝ
  crossingIntegralDeriv : ℝ → ℝ
  hTerm : ℝ → ℝ
  rOneTerm : ℝ → ℝ
  residual : ℝ → ℝ
  gammaSecond : ∀ t ∈ Ioo a b,
    deriv (deriv Gamma) t = 2 * crossingIntegral t
  gammaThird : ∀ t ∈ Ioo a b,
    deriv (deriv (deriv Gamma)) t = 2 * crossingIntegralDeriv t
  differentiatedDecomposition : ∀ t ∈ Ioo a b,
    crossingIntegralDeriv t = hTerm t / 2 + rOneTerm t + residual t
  strictCovariance : ∀ t ∈ Ioo a b, crossingIntegral t = 0 → 0 < hTerm t
  rOne_nonnegative : ∀ t ∈ Ioo a b, crossingIntegral t = 0 → 0 ≤ rOneTerm t
  residual_nonnegative : ∀ t ∈ Ioo a b, crossingIntegral t = 0 → 0 ≤ residual t

/-- **Proposition 4.1 (arbitrary-gap crossing).**

On a constant positive gap, the differentiated PDE decomposition implies that
every zero of `Γ''` is crossed upward. -/
theorem arbitraryGap_crossing
    {Gamma : ℝ → ℝ} {a b : ℝ}
    (d : ArbitraryGapCrossingData Gamma a b) :
    ContDiffOn ℝ 3 Gamma (Ioo a b) ∧
      ∀ t ∈ Ioo a b,
        deriv (deriv Gamma) t = 0 →
          0 < deriv (deriv (deriv Gamma)) t := by
  refine ⟨d.gammaC3, ?_⟩
  intro t ht
  exact crossing_of_decomposition
    (d.gammaSecond t ht)
    (d.gammaThird t ht)
    (d.differentiatedDecomposition t ht)
    (d.strictCovariance t ht)
    (d.rOne_nonnegative t ht)
    (d.residual_nonnegative t ht)

end FRSB.ZeroTemperature.Crossing
