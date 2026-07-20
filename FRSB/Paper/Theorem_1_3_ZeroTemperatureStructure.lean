import FRSB.Paper.Definitions
import FRSB.Paper.ExternalInputs
import FRSB.ZeroTemperature.SupportAssembly
import FRSB.ZeroTemperature.NoTerminalGap.Proposition_4_3_CofinalFromNoTerminalGap
import FRSB.ZeroTemperature.NoTerminalGap.Proposition_4_3_SupportClosedBelowOne
import FRSB.ZeroTemperature.SelectedGapConsequences

/-!
# Theorem 1.3: zero-temperature structure

This file records the exact conclusion of `thm:zero-temperature` and proves
the final assembly step from the analytic inputs established in the paper.

The structure `Theorem1_3AnalyticInputs` is an explicit formalization
boundary. Its fields corresponding to `prop:zt-smoothness`,
`prop:zt-no-internal-gap`, and `prop:zt-no-terminal-gap` are hypotheses here,
not axioms and not kernel-checked proofs of those analytic results.
Consequently, `theorem1_3_assembly` is a kernel-checked conditional assembly
theorem; this file alone is not a complete verification of Theorem 1.3.
-/

namespace FRSB.Paper

open MeasureTheory Set

noncomputable section

/-- A measure has no singular continuous component if every atomless measure
below it and singular with respect to Lebesgue measure is zero. This is the
last assertion of `thm:zero-temperature`, on the measure space `[0,1)`. -/
def HasNoSingularContinuousPart (μ : Measure UnitHalfOpen) : Prop :=
  ∀ κ : Measure UnitHalfOpen, κ ≤ μ → NoAtoms κ → κ ⟂ₘ volume → κ = 0

/-- The exact conclusion of `thm:zero-temperature`, including
`eq:zero-density-decomposition` and `eq:zero-main`.

The identity involving `OrderParameter.stieltjesMeasure` is the Lean version
of `nu_star(dt) = d gamma_star(t) = rho_infinity(t) dt`. The Stieltjes measure
already includes the paper's convention `d gamma_star({0}) = gamma_star(0)`
from `eq:intro-zero-class`. -/
def Theorem1_3Conclusion (γstar : OrderParameter) : Prop :=
  ∃ rhoInfinity : ℝ → ℝ,
    γstar 0 = 0 ∧
    (∀ t ∈ UnitHalfOpen, 0 ≤ rhoInfinity t) ∧
    SmoothOnIco rhoInfinity 0 1 ∧
    γstar.stieltjesMeasure = densityMeasureOnUnitHalfOpen rhoInfinity ∧
    (∀ t ∈ UnitHalfOpen,
      HasDerivWithinAt γstar (rhoInfinity t) UnitHalfOpen t) ∧
    γstar.stieltjesSupport = Set.univ ∧
    relativeClosure UnitClosed
      (Subtype.val '' γstar.stieltjesSupport) = UnitClosed ∧
    NoAtoms γstar.stieltjesMeasure ∧
    HasNoSingularContinuousPart γstar.stieltjesMeasure

/-- Explicit analytic inputs needed to assemble `thm:zero-temperature`.

The smooth-density fields are the output of `prop:zt-smoothness`. The equality
`isCanonicalMinimizer` identifies the parameter with the externally constructed
zero-temperature minimizer.  Support at zero is then obtained from the
zero-field result cited in the proof of Proposition 3.2.  The remaining support
fields record the outputs of
`prop:zt-no-internal-gap` and `prop:zt-no-terminal-gap`. Packaging unfinished
analytic work as structure fields keeps the formalization boundary visible
and does not add any Lean axiom. -/
structure Theorem1_3AnalyticInputs (γstar : OrderParameter) where
  isCanonicalMinimizer : γstar = zeroTemperatureParisiMinimizer
  rhoInfinity : ℝ → ℝ
  rho_nonnegative : ∀ t ∈ UnitHalfOpen, 0 ≤ rhoInfinity t
  rho_smooth : SmoothOnIco rhoInfinity 0 1
  stieltjes_eq_density :
    γstar.stieltjesMeasure = densityMeasureOnUnitHalfOpen rhoInfinity
  rho_eq_gamma_deriv : ∀ t ∈ UnitHalfOpen,
    HasDerivWithinAt γstar (rhoInfinity t) UnitHalfOpen t
  internalGapAnalytic :
    FRSB.ZeroTemperature.NoInternalGap.AnalyticInputs
      (Subtype.val '' γstar.stieltjesSupport)
  terminalGapAnalytic :
    FRSB.ZeroTemperature.NoTerminalGap.AnalyticInputs
      (Subtype.val '' γstar.stieltjesSupport)

/-- The density identity in `eq:zero-density-decomposition` implies that the
canonical Stieltjes measure is atomless on `[0,1)`. -/
theorem noAtoms_of_stieltjes_eq_density
    {γstar : OrderParameter} {rhoInfinity : ℝ → ℝ}
    (hν : γstar.stieltjesMeasure = densityMeasureOnUnitHalfOpen rhoInfinity) :
    NoAtoms γstar.stieltjesMeasure := by
  letI : NoAtoms (volume : Measure UnitHalfOpen) :=
    { measure_singleton := fun x => by
        rw [Measure.Subtype.volume_def,
          (MeasurableEmbedding.subtype_coe measurableSet_Ico).comap_apply]
        simp }
  rw [hν]
  unfold densityMeasureOnUnitHalfOpen
  infer_instance

/-- Absolute continuity of `d gamma` removes the explicit endpoint atom in
the Stieltjes convention, hence forces `gamma(0)=0`.  Thus the endpoint value
is derived from the density identity rather than supplied independently. -/
theorem gamma_zero_of_stieltjes_eq_density
    {γstar : OrderParameter} {rhoInfinity : ℝ → ℝ}
    (hν : γstar.stieltjesMeasure = densityMeasureOnUnitHalfOpen rhoInfinity) :
    γstar 0 = 0 := by
  haveI : NoAtoms (γstar.stieltjesMeasure) :=
    noAtoms_of_stieltjes_eq_density hν
  have hsingleton : γstar.stieltjesMeasure {unitHalfOpenZero} = 0 :=
    measure_singleton unitHalfOpenZero
  rw [OrderParameter.stieltjesMeasure] at hsingleton
  change
    (ENNReal.ofReal (γstar 0) • Measure.dirac unitHalfOpenZero)
        {unitHalfOpenZero} +
      γstar.toStieltjesFunction.measure {unitHalfOpenZero} = 0
    at hsingleton
  have hmass : ENNReal.ofReal (γstar 0) = 0 := by
    have hfirst :
        (ENNReal.ofReal (γstar 0) • Measure.dirac unitHalfOpenZero)
            {unitHalfOpenZero} = 0 := by
      apply le_antisymm
      · calc
          (ENNReal.ofReal (γstar 0) • Measure.dirac unitHalfOpenZero)
                {unitHalfOpenZero} ≤
              (ENNReal.ofReal (γstar 0) • Measure.dirac unitHalfOpenZero)
                  {unitHalfOpenZero} +
                γstar.toStieltjesFunction.measure {unitHalfOpenZero} :=
            le_add_right (le_refl _)
          _ = 0 := hsingleton
      · exact bot_le
    simpa using hfirst
  have hle : γstar 0 ≤ 0 := ENNReal.ofReal_eq_zero.mp hmass
  exact le_antisymm hle (γstar.nonnegative' unitHalfOpenZero)

/-- The density identity in `eq:zero-density-decomposition` excludes a
singular continuous component on `[0,1)`. -/
theorem noSingularContinuousPart_of_stieltjes_eq_density
    {γstar : OrderParameter} {rhoInfinity : ℝ → ℝ}
    (hν : γstar.stieltjesMeasure = densityMeasureOnUnitHalfOpen rhoInfinity) :
    HasNoSingularContinuousPart γstar.stieltjesMeasure := by
  intro κ hκ _ hsing
  have hνac : γstar.stieltjesMeasure ≪ (volume : Measure UnitHalfOpen) := by
    rw [hν]
    exact withDensity_absolutelyContinuous
      (volume : Measure UnitHalfOpen)
      (fun t => ENNReal.ofReal (rhoInfinity t))
  apply Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular
  · exact hκ.absolutelyContinuous.trans hνac
  · exact hsing

/-- Kernel-checked final proof assembly for `thm:zero-temperature`.

This proves `eq:zero-density-decomposition`, `eq:zero-main`, atomlessness,
and absence of a singular continuous component from the explicitly supplied
analytic inputs. -/
theorem theorem1_3_assembly {γstar : OrderParameter}
    (h : Theorem1_3AnalyticInputs γstar) :
    Theorem1_3Conclusion γstar := by
  let S : Set ℝ := Subtype.val '' γstar.stieltjesSupport
  have hzero : unitHalfOpenZero ∈ γstar.stieltjesSupport := by
    rw [h.isCanonicalMinimizer]
    exact chenHandschyLerman_zeroField_zero_mem_stieltjesSupport
  have hnoInternal : FRSB.IntervalClosed S :=
    FRSB.ZeroTemperature.NoInternalGap.intervalClosed_of_analyticInputs
      h.internalGapAnalytic
  have hnoTerminal :
      ¬ ∃ a : ℝ, a < 1 ∧ a ∈ S ∧
        ∀ t : ℝ, a < t → t < 1 → t ∉ S :=
    FRSB.ZeroTemperature.NoTerminalGap.noTerminalGap_of_analyticInputs
      h.terminalGapAnalytic
  let d : FRSB.ZeroTemperature.SupportData :=
    { S := S
      subsetUnitInterior := by
        rintro x ⟨t, _, rfl⟩
        exact t.property
      zeroMem := by
        exact ⟨unitHalfOpenZero, hzero, rfl⟩
      noInternalGap := hnoInternal
      noTerminalGap := by
        apply FRSB.ZeroTemperature.NoTerminalGap.cofinalAtOne_of_noTerminalGap
        · exact ⟨0, by exact ⟨unitHalfOpenZero, hzero, rfl⟩⟩
        · intro a ha1 haClosure
          exact FRSB.ZeroTemperature.NoTerminalGap.image_closedBelowOne_of_isClosed
            γstar.stieltjesMeasure.isClosed_support ha1 haClosure
        · exact hnoTerminal }
  have hsupport : S = FRSB.unitInterior :=
    FRSB.ZeroTemperature.supportData_full d
  have hsupportSubtype : γstar.stieltjesSupport = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    have ht : (t : ℝ) ∈ S := by
      rw [hsupport]
      exact t.property
    obtain ⟨u, hu, hut⟩ := ht
    have hu_eq : u = t := Subtype.ext hut
    simpa [hu_eq] using hu
  refine ⟨h.rhoInfinity,
    gamma_zero_of_stieltjes_eq_density h.stieltjes_eq_density,
    h.rho_nonnegative, h.rho_smooth,
    h.stieltjes_eq_density, h.rho_eq_gamma_deriv, hsupportSubtype, ?_, ?_, ?_⟩
  · change relativeClosure UnitClosed S = UnitClosed
    rw [hsupport]
    exact relativeClosure_unitHalfOpen
  · exact noAtoms_of_stieltjes_eq_density h.stieltjes_eq_density
  · exact noSingularContinuousPart_of_stieltjes_eq_density
      h.stieltjes_eq_density

/-- The selected formalization of Theorem 1.3 for the canonical
zero-temperature Parisi minimizer.

All unresolved PDE, variational, dominated-convergence, and Itô inputs are the
explicitly named declarations in `ExternalInputs.lean`.  The density is
constructed here as the stochastic moment quotient, while smoothness, both
gap exclusions, the endpoint value, full support, atomlessness, and absence of
a singular-continuous part are derived by Lean. -/
theorem theorem1_3 :
    Theorem1_3Conclusion zeroTemperatureParisiMinimizer := by
  let d := zeroTemperature_smoothDensityAnalyticData
  apply theorem1_3_assembly
  exact
    { isCanonicalMinimizer := rfl
      rhoInfinity := d.rhoInfinity
      rho_nonnegative := d.rhoInfinity_nonnegative
      rho_smooth := d.rhoInfinity_smooth
      stieltjes_eq_density := by
        simpa [FRSB.ZeroTemperature.Smoothness.AnalyticDensityData.rhoInfinity]
          using d.stieltjes_eq_quotient_density
      rho_eq_gamma_deriv := by
        simpa [FRSB.ZeroTemperature.Smoothness.AnalyticDensityData.rhoInfinity]
          using d.quotient_eq_gamma_deriv
      internalGapAnalytic := zeroTemperature_internalGapAnalyticInputs
      terminalGapAnalytic := zeroTemperature_terminalGapAnalyticInputs }

end

end FRSB.Paper
