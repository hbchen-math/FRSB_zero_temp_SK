import Mathlib

/-! # Appendix A, Lemma A.1: initial endpoint expansion -/

namespace FRSB.ZeroTemperature.AppendixA

open Finset

/-- **Active Appendix A, Lemma `lem:app-endpoint-expansion`, initial
`log cosh` case of `eq:app-spatial-expansion`.**

For `y=e^{-2x}<1`, the exact endpoint representation and a quantitative
fourth-order remainder bound are

`log cosh x = x-log 2 + y-y²/2+y³/3 + R`,
`|R| ≤ y⁴/(1-y)`.

Thus the displayed remainder is `O(e^{-8x})`, with the printed coefficients
`d₁=1`, `d₂=-1/2`, and `d₃=1/3`. -/
theorem logCosh_endpointExpansion_orderSix
    {x : ℝ} (hy : Real.exp (-2 * x) < 1) :
    let y := Real.exp (-2 * x)
    Real.log (Real.cosh x) = x - Real.log 2 + Real.log (1 + y) ∧
    |Real.log (Real.cosh x) -
      (x - Real.log 2 + y - y^2 / 2 + y^3 / 3)| ≤ y^4 / (1-y) := by
  let y := Real.exp (-2 * x)
  have hypos : 0 < y := Real.exp_pos _
  have habs : |-y| < 1 := by simpa [abs_of_pos hypos, y] using hy
  have hseries := Real.abs_log_sub_add_sum_range_le habs 3
  have hcoshpos : 0 < Real.cosh x := Real.cosh_pos x
  have hrepr : Real.log (Real.cosh x) = x - Real.log 2 + Real.log (1 + y) := by
    rw [Real.cosh_eq]
    have hexp : Real.exp (-x) = Real.exp x * y := by
      dsimp [y]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    have heq : (Real.exp x + Real.exp x * y) / 2 =
        (Real.exp x / 2) * (1 + y) := by ring
    rw [heq, Real.log_mul (by positivity) (by positivity), Real.log_div
      (Real.exp_ne_zero x) (by norm_num), Real.log_exp]
  dsimp only
  constructor
  · exact hrepr
  · rw [hrepr]
    change |(x - Real.log 2 + Real.log (1 + y)) -
      (x - Real.log 2 + y - y ^ 2 / 2 + y ^ 3 / 3)| ≤ y ^ 4 / (1 - y)
    have hsum : (∑ i ∈ range 3, (-y) ^ (i + 1) / (i + 1)) =
        -y + y^2 / 2 - y^3 / 3 := by norm_num [sum_range_succ]; ring
    rw [hsum] at hseries
    have heq :
        x - Real.log 2 + Real.log (1 + y) -
            (x - Real.log 2 + y - y ^ 2 / 2 + y ^ 3 / 3) =
          -y + y ^ 2 / 2 - y ^ 3 / 3 + Real.log (1 + y) := by
      ring
    rw [heq]
    simpa [abs_of_pos hypos] using hseries

end FRSB.ZeroTemperature.AppendixA
