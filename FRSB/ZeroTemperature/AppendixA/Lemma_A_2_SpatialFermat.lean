import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Appendix A, Lemma A.2: spatial Fermat condition

This is one of the three calculus signs used at the compact-strip minimizer in
the proof of `lem:app-comparison`.
-/

namespace FRSB.ZeroTemperature.AppendixA

/-- **Active Appendix A, Lemma `lem:app-comparison`: spatial first derivative.**

At a strip minimum whose spatial coordinate is interior, an explicit spatial
derivative must vanish. -/
theorem spatialDerivative_eq_zero_at_stripMinimum
    {R ellMinus ellPlus r B wB : ℝ} (w : ℝ × ℝ → ℝ)
    (hBleft : ellMinus < B) (hBright : B < ellPlus)
    (hmin : ∀ y ∈ Set.Icc (0 : ℝ) R ×ˢ Set.Icc ellMinus ellPlus,
      w (r, B) ≤ w y)
    (hr : r ∈ Set.Icc (0 : ℝ) R)
    (hderiv : HasDerivAt (fun x => w (r, x)) wB B) :
    wB = 0 := by
  have hlocal : IsLocalMin (fun x => w (r, x)) B := by
    filter_upwards [Ioo_mem_nhds hBleft hBright] with x hx
    exact hmin (r, x) ⟨hr, hx.1.le, hx.2.le⟩
  exact hlocal.hasDerivAt_eq_zero hderiv

end FRSB.ZeroTemperature.AppendixA
