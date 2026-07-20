import FRSB.PositiveTemperature.EndpointIto

/-!
# Positive-temperature endpoint algebra

This file formalizes the algebraic part of
`prop:ft-endpoint-identities` and `prop:ft-endpoint-quantitative`.
The stochastic and transformed-density inputs are recorded as fields of
`EndpointData`; proving that the SK endpoint variables construct such data is
a separate analytic task.
-/

namespace FRSB.PositiveTemperature

/-- Algebraic rearrangement used in `eq:ft-endpoint-atom-ratio`. -/
theorem endpoint_ratio_of_balance {c m2 m3 : ℝ}
    (hc : c ≤ 1) (hm2 : 0 < m2)
    (hbalance : 0 = 4 * (m2 - m3) - 2 * (1 - c) * m3) :
    m3 / m2 = 2 / (3 - c) := by
  have hm2ne : m2 ≠ 0 := ne_of_gt hm2
  have hden : 3 - c ≠ 0 := by linarith
  field_simp [hm2ne, hden]
  nlinarith [hbalance]

/-- The strict ratio bound in the proof of
`prop:ft-endpoint-quantitative` implies `c > 1/3`. -/
theorem endpoint_atom_lower_bound {c r : ℝ}
    (hc : c ≤ 1) (hratio : r = 2 / (3 - c))
    (hstrict : (3 : ℝ) / 4 < r) :
    (1 : ℝ) / 3 < c := by
  have hden : 0 < 3 - c := by linarith
  rw [hratio] at hstrict
  have hmul : ((3 : ℝ) / 4) * (3 - c) < 2 :=
    (lt_div_iff₀ hden).mp hstrict
  nlinarith

/-- Strict log-convexity of the first three positive moments, written as
the strict increase of consecutive moment ratios. -/
theorem moment_ratio_strict {m1 m2 m3 : ℝ}
    (hm1 : 0 < m1) (hm2 : 0 < m2)
    (hlog : m2 ^ 2 < m1 * m3) :
    m2 / m1 < m3 / m2 := by
  rw [div_lt_div_iff₀ hm1 hm2]
  nlinarith

/-- Algebraic upper endpoint scale in
`eq:ft-endpoint-quantitative`. -/
theorem endpoint_upper_scale {β q m1 m2 : ℝ}
    (hβ : 0 < β) (hm1 : 0 < m1)
    (hfirst : m1 = 1 - q) (hsecond : β ^ 2 * m2 = 1)
    (hcov : (1 : ℝ) / 2 < m2 / m1) :
    1 - q < 2 / β ^ 2 := by
  have hb2 : 0 < β ^ 2 := sq_pos_of_pos hβ
  have hcross : m1 < 2 * m2 := by
    have h := (lt_div_iff₀ hm1).mp hcov
    nlinarith
  have hm2' : m2 = 1 / β ^ 2 := by
    apply (eq_div_iff (ne_of_gt hb2)).2
    simpa [mul_comm] using hsecond
  calc
    1 - q = m1 := hfirst.symm
    _ < 2 * m2 := hcross
    _ = 2 / β ^ 2 := by rw [hm2']; ring

/-- Algebraic lower endpoint scale in
`eq:ft-endpoint-quantitative`. -/
theorem endpoint_lower_scale {β q c m1 m2 m3 : ℝ}
    (hβ : 0 < β) (hc : c ≤ 1) (hm1 : 0 < m1) (hm2 : 0 < m2)
    (hfirst : m1 = 1 - q) (hsecond : β ^ 2 * m2 = 1)
    (hratio : m3 / m2 = 2 / (3 - c))
    (hlog : m2 ^ 2 < m1 * m3) :
    (3 - c) / (2 * β ^ 2) < 1 - q := by
  have hb2 : 0 < β ^ 2 := sq_pos_of_pos hβ
  have hden : 0 < 3 - c := by linarith
  have hmoment : m2 / m1 < m3 / m2 :=
    moment_ratio_strict hm1 hm2 hlog
  rw [hratio] at hmoment
  have hcross : m2 * (3 - c) < 2 * m1 :=
    (div_lt_div_iff₀ hm1 hden).mp hmoment
  have hm2' : m2 = 1 / β ^ 2 := by
    apply (eq_div_iff (ne_of_gt hb2)).2
    simpa [mul_comm] using hsecond
  calc
    (3 - c) / (2 * β ^ 2) = ((3 - c) * m2) / 2 := by
      rw [hm2']
      field_simp [ne_of_gt hb2]
    _ < m1 := by nlinarith
    _ = 1 - q := hfirst

/-- The exact scalar inputs used by the proof of
`prop:ft-endpoint-quantitative`.

The field `momentRepresentation` identifies the scalar moments with an actual
endpoint probability law and derives the first moment identity from Parisi
self-consistency.
The field `itoIdentities` records the differentiated self-consistency and
curvature-moment formulas; the second moment and endpoint atom balance are
derived from them.
The field `densityRatios` records the transformed-density representation.
The two uses of `eq:ft-strict-covariance` and the strict Cauchy--Schwarz step
for the nonconstant variable `C_beta` are now proved theorems rather than
scalar hypotheses. -/
structure EndpointData (β : ℝ) where
  q : ℝ
  c : ℝ
  m1 : ℝ
  m2 : ℝ
  m3 : ℝ
  betaPos : 0 < β
  atomNonneg : 0 ≤ c
  atomLeOne : c ≤ 1
  momentRepresentation : EndpointMomentRepresentation q m1 m2 m3
  itoIdentities : EndpointItoData β q c m2 m3
  densityRatios : EndpointDensityRatios m1 m2 m3

/-- Conditional Lean assembly of `prop:ft-endpoint-quantitative` from its
exact analytic inputs. -/
theorem endpoint_quantitative {β : ℝ} (d : EndpointData β) :
    (1 : ℝ) / 3 < d.c ∧
      (3 - d.c) / (2 * β ^ 2) < 1 - d.q ∧
      1 - d.q < 2 / β ^ 2 := by
  have hm1 : 0 < d.m1 := d.momentRepresentation.m1Pos
  have hm2 : 0 < d.m2 := d.momentRepresentation.m2Pos
  have hfirst : d.m1 = 1 - d.q := d.momentRepresentation.firstMoment
  have hsecond : β ^ 2 * d.m2 = 1 := d.itoIdentities.secondMoment
  have hbalance :
      0 = 4 * (d.m2 - d.m3) - 2 * (1 - d.c) * d.m3 :=
    d.itoIdentities.balance d.betaPos
  have hratio : d.m3 / d.m2 = 2 / (3 - d.c) :=
    endpoint_ratio_of_balance d.atomLeOne hm2 hbalance
  constructor
  · exact endpoint_atom_lower_bound d.atomLeOne hratio
      d.densityRatios.covariance32
  constructor
  · exact endpoint_lower_scale d.betaPos d.atomLeOne hm1 hm2
      hfirst hsecond hratio
      (d.densityRatios.logConvex hm1 hm2)
  · exact endpoint_upper_scale d.betaPos hm1 hfirst
      hsecond d.densityRatios.covariance21

end FRSB.PositiveTemperature
