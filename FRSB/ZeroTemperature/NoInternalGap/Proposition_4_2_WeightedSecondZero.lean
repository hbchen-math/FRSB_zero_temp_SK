import FRSB.ZeroTemperature.NoInternalGap.Proposition_4_2_WeightedSecond

/-!
# Proposition 4.2: vanishing weighted second moment

This file performs the endpoint and centering substitutions in
`eq:zt-Gamma-weighted-second`.
-/

namespace FRSB.ZeroTemperature.NoInternalGap

open intervalIntegral MeasureTheory

/-- **Paper equation `eq:zt-Gamma-weighted-second`.**

If `Γ(a)=a`, `Γ(b)=b`, and its integral on the gap equals the integral of
the identity function (written without division as the hypothesis `hmean`),
then the weighted integral of `Γ''` vanishes. -/
theorem weightedSecondDerivative_eq_zero
    {a b : ℝ} (Γ Γ' Γ'' : ℝ → ℝ)
    (hΓ : ∀ t, HasDerivAt Γ (Γ' t) t)
    (hΓ' : ∀ t, HasDerivAt Γ' (Γ'' t) t)
    (hΓ''int : IntervalIntegrable Γ'' volume a b)
    (hΓa : Γ a = a) (hΓb : Γ b = b)
    (hmean : 2 * ∫ t in a..b, Γ t = (b - a) * (a + b)) :
    ∫ t in a..b, (t - a) * (b - t) * Γ'' t = 0 := by
  rw [weightedSecondDerivative_identity Γ Γ' Γ'' hΓ hΓ' hΓ''int]
  rw [hΓa, hΓb, hmean]
  ring

end FRSB.ZeroTemperature.NoInternalGap
