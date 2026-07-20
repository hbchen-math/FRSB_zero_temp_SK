import FRSB.ZeroTemperature.AppendixA.Lemma_A_2_DegenerateStripComparison
import FRSB.ZeroTemperature.AppendixA.Lemma_A_2_SpatialFermat
import FRSB.ZeroTemperature.AppendixA.Lemma_A_2_SpatialSecondDerivative
import FRSB.ZeroTemperature.AppendixA.Lemma_A_2_TimeDerivative

/-!
# Appendix A, Lemma A.2: complete degenerate-strip comparison
-/

namespace FRSB.ZeroTemperature.AppendixA

open Filter Set Topology

/-- **Active Appendix A, Lemma `lem:app-comparison` (transformed form).**

This is the complete compact-strip comparison statement with explicit
`C^{1,2}`-style witnesses: a left time derivative (valid also at terminal
time), a spatial derivative, and a Peano second spatial derivative.  The
diffusion coefficient is required to be positive only in the open spatial
strip, exactly as in the paper. -/
theorem degenerateStripComparison_complete
    {R ellMinus ellPlus : ℝ}
    (w wr wB wBB d b cMinus F : ℝ × ℝ → ℝ)
    (hR : 0 ≤ R) (hell : ellMinus < ellPlus)
    (hcontinuous : ContinuousOn w
      (Icc (0 : ℝ) R ×ˢ Icc ellMinus ellPlus))
    (hinitial : ∀ B ∈ Icc ellMinus ellPlus, 0 ≤ w (0, B))
    (hleft : ∀ r ∈ Icc (0 : ℝ) R, 0 ≤ w (r, ellMinus))
    (hright : ∀ r ∈ Icc (0 : ℝ) R, 0 ≤ w (r, ellPlus))
    (hd : ∀ z ∈ Icc (0 : ℝ) R ×ˢ Ioo ellMinus ellPlus, 0 < d z)
    (hcMinus : ∀ z ∈ Icc (0 : ℝ) R ×ˢ Ioo ellMinus ellPlus, cMinus z < 0)
    (hF : ∀ z ∈ Icc (0 : ℝ) R ×ˢ Ioo ellMinus ellPlus, 0 ≤ F z)
    (hpde : ∀ z ∈ Icc (0 : ℝ) R ×ˢ Ioo ellMinus ellPlus,
      wr z = d z * wBB z + b z * wB z + cMinus z * w z + F z)
    (htime : ∀ z ∈ Icc (0 : ℝ) R ×ˢ Ioo ellMinus ellPlus, 0 < z.1 →
      Tendsto (fun h => (w (z.1 + h, z.2) - w z) / h)
        (𝓝[<] (0 : ℝ)) (𝓝 (wr z)))
    (hspace : ∀ z ∈ Icc (0 : ℝ) R ×ˢ Ioo ellMinus ellPlus,
      HasDerivAt (fun x => w (z.1, x)) (wB z) z.2)
    (hspace2 : ∀ z ∈ Icc (0 : ℝ) R ×ˢ Ioo ellMinus ellPlus,
      Tendsto
        (fun h => (w (z.1, z.2 + h) - w z - wB z * h) / h ^ 2)
        (𝓝[≠] (0 : ℝ)) (𝓝 (wBB z / 2))) :
    ∀ z ∈ Icc (0 : ℝ) R ×ˢ Icc ellMinus ellPlus, 0 ≤ w z := by
  apply degenerateStripComparison_of_minimumSigns w wr wB wBB d b cMinus F
    hR hell hcontinuous hinitial hleft hright hd hcMinus hF hpde
  intro z hz hmin hzneg hztime
  have hspatialMin : ∀ᶠ h in 𝓝[≠] (0 : ℝ), w z ≤ w (z.1, z.2 + h) := by
    have hid : Tendsto (fun h : ℝ => h) (𝓝[≠] 0) (𝓝 0) :=
      tendsto_id.mono_left inf_le_left
    have hconst : Tendsto (fun _ : ℝ => z.2) (𝓝[≠] 0) (𝓝 z.2) :=
      tendsto_const_nhds
    have hadd : Tendsto (fun h : ℝ => z.2 + h) (𝓝[≠] 0) (𝓝 z.2) :=
      by simpa only [add_zero] using hconst.add hid
    filter_upwards [hadd.eventually (Ioo_mem_nhds hz.2.1 hz.2.2)] with h hh
    exact hmin (z.1, z.2 + h) ⟨hz.1, hh.1.le, hh.2.le⟩
  have hwBzero := spatialDerivative_eq_zero_at_stripMinimum w hz.2.1 hz.2.2
    hmin hz.1 (hspace z hz)
  have hwBBnonneg := spatialSecondDerivative_nonnegative_at_localMinimum
    (f := fun x => w (z.1, x)) (B := z.2) (fB := w z)
    (wB := wB z) (wBB := wBB z) rfl hwBzero hspatialMin (hspace2 z hz)
  have htimeMin : ∀ᶠ h in 𝓝[<] (0 : ℝ), w z ≤ w (z.1 + h, z.2) := by
    have hlower : ∀ᶠ h in 𝓝[<] (0 : ℝ), -z.1 < h :=
      Filter.Eventually.filter_mono inf_le_left
        (Ioi_mem_nhds (neg_lt_zero.mpr hztime))
    filter_upwards [hlower, self_mem_nhdsWithin] with h hlo hneg
    have hhneg : h < 0 := hneg
    apply hmin (z.1 + h, z.2)
    exact ⟨⟨by linarith, by linarith [hz.1.2]⟩, hz.2.1.le, hz.2.2.le⟩
  have hwrnonpos := timeDerivative_nonpositive_at_terminalMinimum
    (f := fun r => w (r, z.2)) (R := z.1) (fR := w z)
    htimeMin (htime z hz hztime)
  exact ⟨hwrnonpos, hwBzero, hwBBnonneg⟩

end FRSB.ZeroTemperature.AppendixA
