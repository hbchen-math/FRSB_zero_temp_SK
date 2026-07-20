import FRSB.Basic

/-!
# Zero-temperature support assembly

This file formalizes the last set-theoretic step of
`thm:zero-temperature`. The analytic content of
`prop:zt-no-internal-gap` and `prop:zt-no-terminal-gap` must eventually
produce `IntervalClosed S` and `CofinalAtOne S`, respectively.
-/

namespace FRSB.ZeroTemperature

/-- Once zero belongs to the support, internal gaps are excluded, and support
points are cofinal below one, the support is exactly `[0,1)`. -/
theorem support_eq_unitInterior {S : Set ℝ}
    (hsub : S ⊆ FRSB.unitInterior)
    (hzero : 0 ∈ S)
    (hinterval : FRSB.IntervalClosed S)
    (hcofinal : FRSB.CofinalAtOne S) :
    S = FRSB.unitInterior := by
  apply Set.Subset.antisymm hsub
  intro x hx
  obtain ⟨y, hyS, hxy⟩ := hcofinal hx.2
  exact hinterval hzero hyS hx.1 hxy

/-- Contract collecting the support conclusions proved in Sections 3 and 4
of the manuscript. It is a structure of hypotheses, not an axiom asserting
that the SK model satisfies them. -/
structure SupportData where
  S : Set ℝ
  subsetUnitInterior : S ⊆ FRSB.unitInterior
  zeroMem : 0 ∈ S
  noInternalGap : FRSB.IntervalClosed S
  noTerminalGap : FRSB.CofinalAtOne S

/-- Conditional assembly of the support conclusion in
`thm:zero-temperature`. -/
theorem supportData_full (d : SupportData) :
    d.S = FRSB.unitInterior :=
  support_eq_unitInterior d.subsetUnitInterior d.zeroMem
    d.noInternalGap d.noTerminalGap

end FRSB.ZeroTemperature
