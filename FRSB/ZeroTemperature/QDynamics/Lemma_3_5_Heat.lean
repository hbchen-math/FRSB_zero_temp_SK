import FRSB.ZeroTemperature.Foundations.TransformedDensity
import FRSB.ZeroTemperature.QDynamics.Lemma_3_5_HeatCancellation

/-!
# Lemma 3.5: heat evolution

This file upgrades the scalar cancellation already isolated in
`transformedDensity_heat_cancellation` to a statement with actual derivative
witnesses.  The hypotheses are precisely the classical Parisi PDE and
Fokker--Planck identities at the point under consideration.
-/

namespace FRSB.ZeroTemperature

/-- The heat-equation part of `lem:zt-Q-dynamics`, at a classical point.

Here `rhoX` and `uX` name the spatial first-derivative functions.  Thus the
four spatial `HasDerivAt` hypotheses certify both spatial differentiations,
instead of treating the displayed symbols as unrelated real numbers. -/
theorem lemma_3_5_transformedDensity_heat_at
    (rho u : ℝ → ℝ → ℝ) (rhoX uX : ℝ → ℝ)
    (m t x rhot ut rhoXX uXX : ℝ)
    (hrho_t : HasDerivAt (fun s => rho s x) rhot t)
    (hu_t : HasDerivAt (fun s => u s x) ut t)
    (hrho_x : HasDerivAt (rho t) (rhoX x) x)
    (hu_x : HasDerivAt (u t) (uX x) x)
    (hrho_xx : HasDerivAt rhoX rhoXX x)
    (hu_xx : HasDerivAt uX uXX x)
    (hfp : rhot = (1 / 2 : ℝ) * rhoXX -
      m * (uXX * rho t x + uX x * rhoX x))
    (hpde : ut = -(1 / 2 : ℝ) * (uXX + m * uX x ^ 2)) :
    let Q := fun s y => transformedDensity (rho s) (u s) m y
    let Qx := Real.exp (-m * u t x) *
      (rhoX x - m * uX x * rho t x)
    let Qxx := Real.exp (-m * u t x) *
      (rhoXX - 2 * m * uX x * rhoX x - m * uXX * rho t x +
        m ^ 2 * uX x ^ 2 * rho t x)
    HasDerivAt (fun s => Q s x) ((1 / 2 : ℝ) * Qxx) t ∧
      HasDerivAt (Q t) Qx x ∧
      HasDerivAt
        (fun y => Real.exp (-m * u t y) *
          (rhoX y - m * uX y * rho t y)) Qxx x := by
  dsimp only
  have hexp_t : HasDerivAt (fun s => Real.exp (-m * u s x))
      (Real.exp (-m * u t x) * (-m * ut)) t := by
    convert (hu_t.const_mul (-m)).exp using 1 <;> ring
  have hQ_t := hrho_t.mul hexp_t
  have hexp_x : HasDerivAt (fun y => Real.exp (-m * u t y))
      (Real.exp (-m * u t x) * (-m * uX x)) x := by
    convert (hu_x.const_mul (-m)).exp using 1 <;> ring
  have hQ_x := hrho_x.mul hexp_x
  have hinside_x : HasDerivAt
      (fun y => rhoX y - m * uX y * rho t y)
      (rhoXX - m * (uXX * rho t x + uX x * rhoX x)) x := by
    convert hrho_xx.sub ((hu_xx.mul hrho_x).const_mul m) using 1
    funext y
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  have hQ_xx := hexp_x.mul hinside_x
  have hcancel :
      Real.exp (-m * u t x) *
          (rhot - m * rho t x * ut) =
        (1 / 2 : ℝ) *
          (Real.exp (-m * u t x) *
            (rhoXX - 2 * m * uX x * rhoX x - m * uXX * rho t x +
              m ^ 2 * uX x ^ 2 * rho t x)) := by
    apply transformedDensity_heat_cancellation hfp hpde rfl rfl
  constructor
  · have hQt : HasDerivAt
        (fun s => transformedDensity (rho s) (u s) m x)
        (Real.exp (-m * u t x) * (rhot - m * rho t x * ut)) t := by
      unfold transformedDensity
      convert hQ_t using 1 <;> ring
    rw [hcancel] at hQt
    exact hQt
  constructor
  · unfold transformedDensity
    convert hQ_x using 1 <;> ring
  · convert hQ_xx using 1 <;> ring

end FRSB.ZeroTemperature
