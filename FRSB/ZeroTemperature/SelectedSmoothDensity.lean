import FRSB.Paper.Definitions
import FRSB.ZeroTemperature.Smoothness.Proposition_4_4_MomentQuotientBootstrap

/-!
# Selected analytic interface for Proposition 4.4

The stochastic moment functions are supplied by the unresolved PDE/Itô
analysis.  The density itself is not a field: it is constructed below as their
quotient.  Its smoothness is then a Lean consequence of the formalized moment
bootstrap.
-/

namespace FRSB.ZeroTemperature.Smoothness

open FRSB.Paper MeasureTheory Set
open scoped ContDiff

noncomputable section

/-- PDE/Itô data used by the selected formalization of Proposition 4.4.

In the manuscript, `numerator = E[D²]` and
`denominator = 2 E[C³]`. The `moments_improve` field is the stochastic
generator regularity step. The last two fields are respectively the
Stieltjes-density identification and the endpoint/interior Itô identity.
They are kept explicit because their analytic derivations are outside the
selected Lean scope. -/
structure AnalyticDensityData (gamma : OrderParameter) where
  numerator : ℝ → ℝ
  denominator : ℝ → ℝ
  denominator_pos : ∀ t ∈ UnitHalfOpen, 0 < denominator t
  quotient_nonnegative : ∀ t ∈ UnitHalfOpen,
    0 ≤ numerator t / denominator t
  quotient_continuous : ∀ T, 0 ≤ T → T < 1 →
    ContDiffOn ℝ 0 (fun t => numerator t / denominator t) (Icc 0 T)
  moments_improve : ∀ T, 0 ≤ T → T < 1 → ∀ r : ℕ,
    ContDiffOn ℝ r (fun t => numerator t / denominator t) (Icc 0 T) →
      ContDiffOn ℝ (r + 1) numerator (Icc 0 T) ∧
      ContDiffOn ℝ (r + 1) denominator (Icc 0 T)
  stieltjes_eq_quotient_density :
    gamma.stieltjesMeasure =
      densityMeasureOnUnitHalfOpen (fun t => numerator t / denominator t)
  quotient_eq_gamma_deriv : ∀ t ∈ UnitHalfOpen,
    HasDerivWithinAt gamma (numerator t / denominator t) UnitHalfOpen t

/-- The constructed smooth density `rho_infinity`. -/
def AnalyticDensityData.rhoInfinity {gamma : OrderParameter}
    (d : AnalyticDensityData gamma) : ℝ → ℝ :=
  fun t => d.numerator t / d.denominator t

/-- The stochastic moment improvement gives `C^∞` regularity of the
constructed quotient on every compact subinterval of `[0,1)`. -/
theorem AnalyticDensityData.rhoInfinity_smooth
    {gamma : OrderParameter} (d : AnalyticDensityData gamma) :
    SmoothOnIco d.rhoInfinity 0 1 := by
  intro T hT0 hT1
  exact contDiffOn_top_of_momentQuotient_bootstrap
    (s := Icc 0 T)
    (gamma := d.rhoInfinity)
    (numerator := d.numerator) (denominator := d.denominator)
    (by intro t _; rfl)
    (d.quotient_continuous T hT0 hT1)
    (by
      intro t ht
      exact d.denominator_pos t ⟨ht.1, ht.2.trans_lt hT1⟩)
    (d.moments_improve T hT0 hT1)

/-- Nonnegativity of the constructed density. -/
theorem AnalyticDensityData.rhoInfinity_nonnegative
    {gamma : OrderParameter} (d : AnalyticDensityData gamma) :
    ∀ t ∈ UnitHalfOpen, 0 ≤ d.rhoInfinity t := by
  intro t ht
  exact d.quotient_nonnegative t ht

end
end FRSB.ZeroTemperature.Smoothness
