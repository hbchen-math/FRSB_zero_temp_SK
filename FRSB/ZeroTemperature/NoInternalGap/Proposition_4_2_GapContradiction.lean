import FRSB.ZeroTemperature.NoInternalGap.Proposition_4_2_StrictMoment

/-!
# Deterministic contradiction excluding an internal gap

This is the last step of paper Proposition `prop:zt-no-internal-gap`.  The
PDE/stochastic work enters only through the hypotheses giving the unique
upward crossing and the two integral identities.  Once those are available,
the contradiction below is purely real analysis.
-/

namespace FRSB.ZeroTemperature.NoInternalGap

open intervalIntegral

/-- **Deterministic core of paper Proposition `prop:zt-no-internal-gap`.**

Here `Γa`, `Γb`, and `Γpa` stand for `Γ(a)`, `Γ(b)`, and `Γ'(a+)`, while
`f` stands for `Γ''`.  The hypotheses reproduce equations
`eq:zt-Gamma-gap-endpoints`, `eq:zt-Gamma-weighted-second`, and the twice
integrated identity immediately preceding `eq:zt-Gamma-strict-moment`.
They are incompatible with the upward-crossing sign pattern. -/
theorem noInternalGap_of_weightedCrossing
    {a b c Γa Γb Γpa : ℝ} (f : ℝ → ℝ)
    (hab : a < b) (hac : a < c) (hcb : c < b)
    (hf : ContinuousOn f (Set.uIcc a b))
    (hneg : ∀ t, a < t → t < c → f t < 0)
    (hpos : ∀ t, c < t → t < b → 0 < f t)
    (hweighted : ∫ t in a..b, (t - a) * (b - t) * f t = 0)
    (hfirstMoment : Γb - Γa - (b - a) * Γpa =
      ∫ t in a..b, (b - t) * f t)
    (hendpointIncrement : Γb - Γa = b - a)
    (hslope : Γpa ≤ 1) : False := by
  have hstrict :=
    strictMoment_of_upwardCrossing f hab hac hcb hf hneg hpos hweighted
  have hgap_pos : 0 < b - a := sub_pos.mpr hab
  have hleft_nonneg : 0 ≤ Γb - Γa - (b - a) * Γpa := by
    rw [hendpointIncrement]
    nlinarith
  rw [hfirstMoment] at hleft_nonneg
  exact (not_lt_of_ge hleft_nonneg) hstrict

end FRSB.ZeroTemperature.NoInternalGap
