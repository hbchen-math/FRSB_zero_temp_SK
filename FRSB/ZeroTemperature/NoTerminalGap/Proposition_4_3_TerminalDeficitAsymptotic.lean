import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Proposition 4.3: terminal deficit asymptotic from the scaled integral

This file formalizes the final limit algebra in Step 3 of
`prop:zt-no-terminal-gap`, after change of variables and dominated convergence.
-/

namespace FRSB.ZeroTemperature.NoTerminalGap

open Filter Set Topology

/-- If the terminal deficit is `sqrt ε` times a scaled integral `I ε`, and
`I ε → A > 0`, then the deficit is asymptotic to `A sqrt ε`.

In the manuscript, `A = 4 rho₁(0) / sqrt π`; the identity is the display
immediately before `eq:zt-terminal-square-root`, and convergence of `I` is the
dominated-convergence conclusion. -/
theorem terminalDeficit_asymptotic_of_scaledIntegral
    (deficit scaledIntegral : ℝ → ℝ) (A : ℝ)
    (hA : 0 < A)
    (hscaled : Tendsto scaledIntegral (𝓝[>] (0 : ℝ)) (𝓝 A))
    (hidentity : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      deficit ε = √ε * scaledIntegral ε) :
    Tendsto (fun ε => deficit ε / (A * √ε))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hsqrt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), √ε ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (Real.sqrt_pos.2 hε).ne'
  have heq :
      (fun ε => deficit ε / (A * √ε)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun ε => scaledIntegral ε / A) := by
    filter_upwards [hidentity, hsqrt] with ε hid hs
    rw [hid]
    field_simp
  apply Tendsto.congr' heq.symm
  simpa [hA.ne'] using hscaled.div_const A

end FRSB.ZeroTemperature.NoTerminalGap
