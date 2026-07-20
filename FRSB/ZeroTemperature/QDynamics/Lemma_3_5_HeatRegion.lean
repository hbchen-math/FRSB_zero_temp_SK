import FRSB.ZeroTemperature.QDynamics.Lemma_3_5_Heat

/-!
# Lemma 3.5: heat evolution on a constant-coefficient region

This is the region-level form of the heat part of `lem:zt-Q-dynamics`.
Every derivative occurring in the conclusion is certified by `HasDerivAt`.
-/

namespace FRSB.ZeroTemperature

/-- If the classical Parisi and Fokker--Planck equations hold throughout
`(a,b) × ℝ` with constant coefficient `m`, then the transformed density
`Q = rho * exp (-m u)` satisfies the heat equation throughout that region.

The conclusion includes witnesses for the first and second spatial
derivatives, so the equality of the time derivative with half the displayed
second spatial derivative is not merely a scalar algebraic identity. -/
theorem lemma_3_5_transformedDensity_heat_on_region
    (rho u : ℝ → ℝ → ℝ)
    (rhoT uT rhoX uX rhoXX uXX : ℝ → ℝ → ℝ)
    (m a b : ℝ)
    (hrho_t : ∀ t ∈ Set.Ioo a b, ∀ x,
      HasDerivAt (fun s => rho s x) (rhoT t x) t)
    (hu_t : ∀ t ∈ Set.Ioo a b, ∀ x,
      HasDerivAt (fun s => u s x) (uT t x) t)
    (hrho_x : ∀ t ∈ Set.Ioo a b, ∀ x,
      HasDerivAt (rho t) (rhoX t x) x)
    (hu_x : ∀ t ∈ Set.Ioo a b, ∀ x,
      HasDerivAt (u t) (uX t x) x)
    (hrho_xx : ∀ t ∈ Set.Ioo a b, ∀ x,
      HasDerivAt (rhoX t) (rhoXX t x) x)
    (hu_xx : ∀ t ∈ Set.Ioo a b, ∀ x,
      HasDerivAt (uX t) (uXX t x) x)
    (hfp : ∀ t ∈ Set.Ioo a b, ∀ x,
      rhoT t x = (1 / 2 : ℝ) * rhoXX t x -
        m * (uXX t x * rho t x + uX t x * rhoX t x))
    (hpde : ∀ t ∈ Set.Ioo a b, ∀ x,
      uT t x = -(1 / 2 : ℝ) * (uXX t x + m * uX t x ^ 2)) :
    ∀ t ∈ Set.Ioo a b, ∀ x,
      let Q := fun s y => transformedDensity (rho s) (u s) m y
      let Qx := Real.exp (-m * u t x) *
        (rhoX t x - m * uX t x * rho t x)
      let Qxx := Real.exp (-m * u t x) *
        (rhoXX t x - 2 * m * uX t x * rhoX t x -
          m * uXX t x * rho t x + m ^ 2 * uX t x ^ 2 * rho t x)
      HasDerivAt (fun s => Q s x) ((1 / 2 : ℝ) * Qxx) t ∧
        HasDerivAt (Q t) Qx x ∧
        HasDerivAt
          (fun y => Real.exp (-m * u t y) *
            (rhoX t y - m * uX t y * rho t y)) Qxx x := by
  intro t ht x
  exact lemma_3_5_transformedDensity_heat_at
    rho u (rhoX t) (uX t) m t x (rhoT t x) (uT t x)
    (rhoXX t x) (uXX t x)
    (hrho_t t ht x) (hu_t t ht x)
    (hrho_x t ht x) (hu_x t ht x)
    (hrho_xx t ht x) (hu_xx t ht x)
    (hfp t ht x) (hpde t ht x)

end FRSB.ZeroTemperature
