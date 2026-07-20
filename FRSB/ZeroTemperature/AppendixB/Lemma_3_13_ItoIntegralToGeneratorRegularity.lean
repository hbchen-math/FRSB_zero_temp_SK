import FRSB.ZeroTemperature.AppendixB.Lemma_3_13_FiniteMomentCombinationRegularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Appendix B: from the Itô expectation identity to moment regularity

After the stochastic integral in Itô's formula is shown to have expectation
zero, the remaining assertion is a deterministic interval-integral identity.
This file formalizes the passage from that identity to the displayed
moment-generator derivative and then to the regularity conclusion.
-/

namespace FRSB.ZeroTemperature

open MeasureTheory

/-- Suppose the expectation of an Itô identity has produced

`moment t - moment 0 = ∫ s in 0..t, generatorMoment s`.

For the polynomial generator in Lemma 3.13, `generatorMoment` is a finite sum
of ordinary moments and `gamma`-weighted moments.  If these data are `C^r`,
then the integral identity implies the exact derivative formula
`eq:zt-polynomial-moment-derivative`, and consequently `moment` is
`C^(r+1)`.

The assumption `hintegral` is the transparent deterministic interface where
the stochastic proof must discharge integrability and the mean-zero
martingale term; no stochastic fact is hidden as an axiom here. -/
theorem lemma_3_13_ito_integral_identity_to_generator_regularity
    {n : ℕ} (r : ℕ) (gamma moment : ℝ → ℝ)
    (moments : Fin n → ℝ → ℝ) (a b : Fin n → ℝ)
    (hgamma : ContDiff ℝ r gamma)
    (hmoments : ∀ i, ContDiff ℝ r (moments i))
    (hintegral : ∀ t,
      moment t - moment 0 =
        ∫ s in (0 : ℝ)..t,
          ∑ i : Fin n, (a i + b i * gamma s) * moments i s) :
    let generatorMoment := fun t =>
      ∑ i : Fin n, (a i + b i * gamma t) * moments i t
    (∀ t, HasDerivAt moment (generatorMoment t) t) ∧
      ContDiff ℝ r generatorMoment ∧ ContDiff ℝ (r + 1) moment := by
  dsimp only
  let generatorMoment : ℝ → ℝ := fun t =>
    ∑ i : Fin n, (a i + b i * gamma t) * moments i t
  have hterms : ∀ i : Fin n,
      ContDiff ℝ r (fun t => (a i + b i * gamma t) * moments i t) := by
    intro i
    have hb : ContDiff ℝ r (fun t : ℝ => b i * gamma t) :=
      contDiff_const.mul hgamma
    exact (contDiff_const.add hb).mul (hmoments i)
  have hgenerator : ContDiff ℝ r generatorMoment := by
    exact ContDiff.sum fun i _ => hterms i
  have hgeneratorContinuous : Continuous generatorMoment := hgenerator.continuous
  have hderiv : ∀ t, HasDerivAt moment (generatorMoment t) t := by
    intro t
    have hint : HasDerivAt
        (fun u => ∫ s in (0 : ℝ)..u, generatorMoment s)
        (generatorMoment t) t :=
      intervalIntegral.integral_hasDerivAt_right
        (hgeneratorContinuous.intervalIntegrable _ _)
        hgeneratorContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter
        hgeneratorContinuous.continuousAt
    have hrepr : moment = fun u => moment 0 +
        ∫ s in (0 : ℝ)..u, generatorMoment s := by
      funext u
      have hu := hintegral u
      change moment u - moment 0 =
        ∫ s in (0 : ℝ)..u, generatorMoment s at hu
      linarith
    rw [hrepr]
    simpa only [Pi.add_apply, zero_add] using
      (hasDerivAt_const t (moment 0)).add hint
  have hregularity := lemma_3_13_finite_moment_generator_contDiff
    r gamma moment moments a b hgamma hmoments hderiv
  exact ⟨hderiv, hregularity.1, hregularity.2⟩

end FRSB.ZeroTemperature
