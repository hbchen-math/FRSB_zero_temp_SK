import Mathlib

/-!
# Appendix A, Lemma A.1: the universal endpoint coefficient

This file isolates the final asymptotic calculation in the active proof of
`lem:app-endpoint-expansion`.
-/

namespace FRSB.ZeroTemperature.AppendixA

open Filter Topology

/-- **Active Appendix A, Lemma `lem:app-endpoint-expansion`, equations
`eq:app-spatial-expansion` and `eq:app-slope-endpoint-expansion`.**

The proof of Lemma A.1 obtains
`δ = 2 d₁ y + O(y²)` and `c = 4 d₁ y + O(y²)`, with `d₁ > 0`.
Equivalently, `y/δ → 1/(2d₁)` and `(c-4d₁y)/δ → 0`.  This theorem proves
that the linear endpoint coefficient is therefore universal:

`c/δ → 2`.
-/
theorem slopeCurvature_linearCoefficient_two
    {ι : Type*} {l : Filter ι} (δ y c : ι → ℝ) {d₁ : ℝ}
    (hd₁ : d₁ ≠ 0)
    (hδ : ∀ᶠ i in l, δ i ≠ 0)
    (hinverse : Tendsto (fun i => y i / δ i) l (𝓝 (1 / (2 * d₁))))
    (hcurvature : Tendsto (fun i => (c i - 4 * d₁ * y i) / δ i) l (𝓝 0)) :
    Tendsto (fun i => c i / δ i) l (𝓝 2) := by
  have hdecomp :
      (fun i => c i / δ i) =ᶠ[l]
        (fun i => (c i - 4 * d₁ * y i) / δ i + (4 * d₁) * (y i / δ i)) := by
    filter_upwards [hδ] with i hδi
    field_simp
    ring
  apply Tendsto.congr' hdecomp.symm
  have hconst : Tendsto (fun _ : ι => (4 * d₁ : ℝ)) l (𝓝 (4 * d₁)) :=
    tendsto_const_nhds
  have hlimit := hcurvature.add (hconst.mul hinverse)
  convert hlimit using 1
  field_simp [hd₁] <;> ring

end FRSB.ZeroTemperature.AppendixA
