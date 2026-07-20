import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

/-!
# Appendix A, Lemma A.2: interior-minimum contradiction

Mathlib currently has no ready-made parabolic comparison principle for a
strip whose diffusion coefficient may degenerate at the spatial boundary.
This file therefore formalizes the decisive interior-minimum calculation in
the active proof of `lem:app-comparison`.
-/

namespace FRSB.ZeroTemperature.AppendixA

/-- **Core of active Appendix A, Lemma `lem:app-comparison`
(degenerate-strip comparison).**

After replacing `v` by `w = exp (-λr) v`, at a negative interior minimum the
calculus conditions are `w_r ≤ 0`, `w_B = 0`, and `w_BB ≥ 0`.  If `d > 0`,
`λ > c`, and the source is nonnegative, the transformed parabolic equation
is incompatible with those conditions.

This is precisely the pointwise contradiction used by the paper.  To obtain
the complete strip theorem one must additionally formalize the compact-strip
minimum-attainment argument and derive the three displayed derivative signs
from the stated `C^{1,2}` regularity; mathlib presently provides no packaged
parabolic-boundary theorem doing that specialization. -/
theorem negativeInteriorMinimum_impossible
    {w wr wB wBB d b c lam F : ℝ}
    (hw : w < 0)
    (hwr : wr ≤ 0)
    (hwB : wB = 0)
    (hwBB : 0 ≤ wBB)
    (hd : 0 < d)
    (hlam : c < lam)
    (hF : 0 ≤ F)
    (hpde : wr = d * wBB + b * wB + (c - lam) * w + F) : False := by
  have hdiff : c - lam < 0 := sub_neg.mpr hlam
  have hdiffw : 0 < (c - lam) * w := mul_pos_of_neg_of_neg hdiff hw
  have hdw : 0 ≤ d * wBB := mul_nonneg hd.le hwBB
  rw [hwB, mul_zero, add_zero] at hpde
  linarith

end FRSB.ZeroTemperature.AppendixA
