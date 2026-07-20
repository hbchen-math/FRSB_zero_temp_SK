import Mathlib

/-! # Appendix A, Lemma A.1: differentiated initial remainder -/

namespace FRSB.ZeroTemperature.AppendixA

/-- **Active Appendix A, Lemma `lem:app-endpoint-expansion`: differentiated
remainder bounds for the initial `log cosh` expansion.**

Writing `y=e^{-2x}` and
`R=log(1+y)-y+y²/2-y³/3`, the first four spatial derivatives are the displayed
rational functions.  Every numerator contains `y⁴` and every denominator is
at least one for `y≥0`; hence each derivative is `O(e^{-8x})`, exactly the
differentiated remainder assertion used for the initial cascade datum. -/
theorem logCosh_remainder_firstFourDerivatives (x : ℝ) :
    let y : ℝ → ℝ := fun t => Real.exp (-2*t)
    let R : ℝ → ℝ := fun t => Real.log (1+y t)-y t+(y t)^2/2-(y t)^3/3
    let R1 : ℝ → ℝ := fun t => 2*(y t)^4/(1+y t)
    let R2 : ℝ → ℝ := fun t => -4*(y t)^4*(4+3*y t)/(1+y t)^2
    let R3 : ℝ → ℝ := fun t =>
      8*(y t)^4*(16+23*y t+9*(y t)^2)/(1+y t)^3
    let R4 : ℝ → ℝ := fun t =>
      -16*(y t)^4*(64+131*y t+100*(y t)^2+27*(y t)^3)/(1+y t)^4
    HasDerivAt R (R1 x) x ∧ HasDerivAt R1 (R2 x) x ∧
      HasDerivAt R2 (R3 x) x ∧ HasDerivAt R3 (R4 x) x := by
  dsimp
  have hy : HasDerivAt (fun t : ℝ => Real.exp (-2*t))
      (-2*Real.exp (-2*x)) x := by
    convert Real.hasDerivAt_exp (-2*x) |>.comp x
      ((hasDerivAt_const x (-2 : ℝ)).mul (hasDerivAt_id x)) using 1 <;> ring
  have hpos : 1 + Real.exp (-2*x) ≠ 0 := by positivity
  constructor
  · convert (((hasDerivAt_const x 1).add hy).log hpos).sub hy |>.add
      ((hy.pow 2).div_const 2) |>.sub ((hy.pow 3).div_const 3) using 1 <;>
      (try funext t) <;>
      simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.div_apply] <;>
      field_simp [hpos] <;> ring
  constructor
  · convert (((hy.pow 4).const_mul 2).div
      ((hasDerivAt_const x 1).add hy) hpos) using 1 <;>
      (try funext t) <;>
      simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.div_apply] <;>
      field_simp [hpos] <;> ring
  constructor
  · convert (((((hy.pow 4).mul
      ((hasDerivAt_const x 4).add (hy.const_mul 3)))).const_mul (-4)).div
      (((hasDerivAt_const x 1).add hy).pow 2) (pow_ne_zero 2 hpos)) using 1 <;>
      (try funext t) <;>
      simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.div_apply] <;>
      field_simp [hpos] <;> ring
  · convert (((((hy.pow 4).mul
      (((hasDerivAt_const x 16).add (hy.const_mul 23)).add
        ((hy.pow 2).const_mul 9)))).const_mul 8).div
      (((hasDerivAt_const x 1).add hy).pow 3) (pow_ne_zero 3 hpos)) using 1 <;>
      (try funext t) <;>
      simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.div_apply] <;>
      field_simp [hpos] <;> ring

end FRSB.ZeroTemperature.AppendixA
