import FRSB.ZeroTemperature.Smoothness.Proposition_4_4_RightContinuousRepresentative
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Proposition 4.4: a.e. quotient identity is pointwise on `[0,T]`

This specializes the representative step to real time and supplies the
measure-theoretic fact left abstract in
`rightContinuous_eq_continuous_of_frequently_eq`.
-/

namespace FRSB.ZeroTemperature.Smoothness

open Filter MeasureTheory Set Topology

/-- Let `gamma` be right-continuous at every point of `[0,T]`, and let
`quotient` be continuous there.  If they agree Lebesgue-a.e., then they agree
at every point of `[0,T]`.

The proof approaches each time from the right.  Lebesgue measure is positive
on every nonempty open interval, so an a.e. equality set is dense and has
equality points arbitrarily close from that side.  This is the representative
argument used after `eq:zt-gamma-quotient-ae` in Proposition 4.4. -/
theorem proposition_4_4_rightContinuous_eq_continuous_of_ae_on_Icc
    (gamma quotient : ℝ → ℝ) (T : ℝ)
    (hgamma : ∀ t ∈ Icc (0 : ℝ) T,
      ContinuousWithinAt gamma (Ici t) t)
    (hquotient : ContinuousOn quotient (Ici 0))
    (hae : gamma =ᵐ[(volume : Measure ℝ)] quotient) :
    EqOn gamma quotient (Icc 0 T) := by
  have hdense : Dense {t : ℝ | gamma t = quotient t} :=
    Measure.dense_of_ae (μ := (volume : Measure ℝ)) hae
  intro t ht
  have hrightClosure :
      t ∈ closure (Ioi t ∩ {s : ℝ | gamma s = quotient s}) := by
    have hsubset : Ioi t ⊆
        closure (Ioi t ∩ {s : ℝ | gamma s = quotient s}) :=
      hdense.open_subset_closure_inter isOpen_Ioi
    have hclosureSubset : closure (Ioi t) ⊆
        closure (Ioi t ∩ {s : ℝ | gamma s = quotient s}) :=
      closure_minimal hsubset isClosed_closure
    exact hclosureSubset (by simp)
  have hfrequentRight :
      ∃ᶠ s in 𝓝 t, gamma s = quotient s ∧ s ∈ Ici t := by
    refine (mem_closure_iff_frequently.mp hrightClosure).mono ?_
    intro s hs
    exact ⟨hs.2, show t ≤ s from hs.1.le⟩
  have hfrequentWithin :
      ∃ᶠ s in 𝓝[Ici t] t, gamma s = quotient s :=
    frequently_nhdsWithin_iff.mpr hfrequentRight
  have hIci : Ici t ⊆ Ici (0 : ℝ) := fun _ hs => ht.1.trans hs
  exact tendsto_nhds_unique_of_frequently_eq
    (hgamma t ht)
    ((hquotient t ht.1).mono hIci)
    hfrequentWithin

end FRSB.ZeroTemperature.Smoothness
