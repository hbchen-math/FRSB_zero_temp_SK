import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Proposition 4.2: the twice-integrated weighted identity

This is equation `eq:zt-Gamma-weighted-second` before the endpoint and
centering relations are substituted.  It isolates the integration-by-parts
step from all PDE input.
-/

namespace FRSB.ZeroTemperature.NoInternalGap

open intervalIntegral
open MeasureTheory

/-- **Paper equation `eq:zt-Gamma-weighted-second` (integration identity).**

For a twice differentiable `Γ` whose second derivative is interval
integrable,

`∫ (t-a)(b-t) Γ''(t) dt = (b-a)(Γ(a)+Γ(b)) - 2∫ Γ(t) dt`.

The paper then uses `Γ(a)=a`, `Γ(b)=b`, and its centered integral identity
to show that the right-hand side is zero. -/
theorem weightedSecondDerivative_identity
    {a b : ℝ} (Γ Γ' Γ'' : ℝ → ℝ)
    (hΓ : ∀ t, HasDerivAt Γ (Γ' t) t)
    (hΓ' : ∀ t, HasDerivAt Γ' (Γ'' t) t)
    (hΓ''int : IntervalIntegrable Γ'' volume a b) :
    ∫ t in a..b, (t - a) * (b - t) * Γ'' t =
      (b - a) * (Γ a + Γ b) - 2 * ∫ t in a..b, Γ t := by
  let w : ℝ → ℝ := fun t => (t - a) * (b - t)
  let w' : ℝ → ℝ := fun t => a + b - 2 * t
  have hw : ∀ t, HasDerivAt w (w' t) t := by
    intro t
    convert ((hasDerivAt_id t).sub_const a).mul
      ((hasDerivAt_const t b).sub (hasDerivAt_id t)) using 1 <;>
      simp [w, w'] <;> ring
  have hw' : ∀ t, HasDerivAt w' (-2) t := by
    intro t
    convert ((hasDerivAt_const t (a + b)).sub
      ((hasDerivAt_const t (2 : ℝ)).mul (hasDerivAt_id t))) using 1 <;>
      simp [w']
  have hΓcont : Continuous Γ := continuous_iff_continuousAt.2 fun t => (hΓ t).continuousAt
  have hΓ'cont : Continuous Γ' := continuous_iff_continuousAt.2 fun t => (hΓ' t).continuousAt
  have hΓint : IntervalIntegrable Γ volume a b := hΓcont.intervalIntegrable _ _
  have hΓ'int : IntervalIntegrable Γ' volume a b := hΓ'cont.intervalIntegrable _ _
  have hw'int : IntervalIntegrable w' volume a b :=
    (continuous_const.add continuous_const |>.sub
      (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hconstint : IntervalIntegrable (fun _ : ℝ => (-2 : ℝ)) volume a b :=
    intervalIntegrable_const
  have hparts1 := integral_mul_deriv_eq_deriv_mul
    (fun t _ => hw t) (fun t _ => hΓ' t) hw'int hΓ''int
  have hparts2 := integral_mul_deriv_eq_deriv_mul
    (fun t _ => hw' t) (fun t _ => hΓ t) hconstint hΓ'int
  simp only [w, w'] at hparts1 hparts2 ⊢
  rw [hparts1, hparts2]
  rw [intervalIntegral.integral_const_mul]
  ring

end FRSB.ZeroTemperature.NoInternalGap
