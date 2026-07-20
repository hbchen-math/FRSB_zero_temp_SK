import FRSB.ZeroTemperature.AppendixA.Lemma_A_2_InteriorMinimumContradiction
import Mathlib

/-!
# Appendix A, Lemma A.2: compact-strip comparison

This theorem supplies the compact minimum-attainment and boundary-exclusion
layer of the degenerate-strip comparison argument.
-/

namespace FRSB.ZeroTemperature.AppendixA

/-- **Active Appendix A, Lemma `lem:app-comparison`, transformed form.**

For the exponentially transformed unknown, a continuous negative value on a
compact strip produces a negative global minimum at positive time and in the
open spatial interval.  If the standard `C^{1,2}` minimum derivative signs
hold there, the transformed parabolic equation rules it out.

The hypothesis `hminimumSigns` is exactly the local calculus specialization
of `C^{1,2}` at a global strip minimum; separating it makes this result usable
with one-sided notions of the time derivative at the terminal time. -/
theorem degenerateStripComparison_of_minimumSigns
    {R ellMinus ellPlus : ℝ}
    (w wr wB wBB d b cMinus F : ℝ × ℝ → ℝ)
    (hR : 0 ≤ R) (hell : ellMinus < ellPlus)
    (hcontinuous : ContinuousOn w
      (Set.Icc (0 : ℝ) R ×ˢ Set.Icc ellMinus ellPlus))
    (hinitial : ∀ B ∈ Set.Icc ellMinus ellPlus, 0 ≤ w (0, B))
    (hleft : ∀ r ∈ Set.Icc (0 : ℝ) R, 0 ≤ w (r, ellMinus))
    (hright : ∀ r ∈ Set.Icc (0 : ℝ) R, 0 ≤ w (r, ellPlus))
    (hd : ∀ z ∈ Set.Icc (0 : ℝ) R ×ˢ Set.Ioo ellMinus ellPlus, 0 < d z)
    (hcMinus : ∀ z ∈ Set.Icc (0 : ℝ) R ×ˢ Set.Ioo ellMinus ellPlus,
      cMinus z < 0)
    (hF : ∀ z ∈ Set.Icc (0 : ℝ) R ×ˢ Set.Ioo ellMinus ellPlus, 0 ≤ F z)
    (hpde : ∀ z ∈ Set.Icc (0 : ℝ) R ×ˢ Set.Ioo ellMinus ellPlus,
      wr z = d z * wBB z + b z * wB z + cMinus z * w z + F z)
    (hminimumSigns : ∀ z ∈ Set.Icc (0 : ℝ) R ×ˢ Set.Ioo ellMinus ellPlus,
      (∀ y ∈ Set.Icc (0 : ℝ) R ×ˢ Set.Icc ellMinus ellPlus, w z ≤ w y) →
      w z < 0 → 0 < z.1 → wr z ≤ 0 ∧ wB z = 0 ∧ 0 ≤ wBB z) :
    ∀ z ∈ Set.Icc (0 : ℝ) R ×ˢ Set.Icc ellMinus ellPlus, 0 ≤ w z := by
  intro z hz
  by_contra hn
  have hwz : w z < 0 := lt_of_not_ge hn
  let strip := Set.Icc (0 : ℝ) R ×ˢ Set.Icc ellMinus ellPlus
  have hcompact : IsCompact strip := isCompact_Icc.prod isCompact_Icc
  have hnonempty : strip.Nonempty := by
    exact ⟨(0, ellMinus), ⟨⟨le_rfl, hR⟩, ⟨le_rfl, hell.le⟩⟩⟩
  obtain ⟨q, hq, hqmin⟩ := hcompact.exists_isMinOn hnonempty hcontinuous
  have hq_eta : (q.1, q.2) = q := by cases q; rfl
  have hqneg : w q < 0 := lt_of_le_of_lt (hqmin hz) hwz
  have hqtime : 0 < q.1 := by
    rcases hq.1.1.eq_or_lt with hzero | hpos
    · have := hinitial q.2 hq.2
      have hqnonneg : 0 ≤ w q := by
        rw [← hq_eta]
        rw [← hzero]
        exact this
      exact (not_lt_of_ge hqnonneg hqneg).elim
    · exact hpos
  have hqleft : ellMinus < q.2 := by
    rcases hq.2.1.eq_or_lt with hleftEq | hlt
    · have := hleft q.1 hq.1
      have hqnonneg : 0 ≤ w q := by
        rw [← hq_eta]
        rw [← hleftEq]
        exact this
      exact (not_lt_of_ge hqnonneg hqneg).elim
    · exact hlt
  have hqright : q.2 < ellPlus := by
    rcases hq.2.2.eq_or_lt with hrightEq | hlt
    · have := hright q.1 hq.1
      have hqnonneg : 0 ≤ w q := by
        rw [← hq_eta]
        rw [hrightEq]
        exact this
      exact (not_lt_of_ge hqnonneg hqneg).elim
    · exact hlt
  have hqopen : q ∈ Set.Icc (0 : ℝ) R ×ˢ Set.Ioo ellMinus ellPlus :=
    ⟨hq.1, hqleft, hqright⟩
  obtain ⟨hwr, hwBzero, hwBBnonneg⟩ :=
    hminimumSigns q hqopen hqmin hqneg hqtime
  have hpde' :
      wr q = d q * wBB q + b q * wB q + (cMinus q - 0) * w q + F q := by
    simpa using hpde q hqopen
  exact negativeInteriorMinimum_impossible hqneg hwr hwBzero hwBBnonneg
    (hd q hqopen) (hcMinus q hqopen) (hF q hqopen) hpde'

end FRSB.ZeroTemperature.AppendixA
