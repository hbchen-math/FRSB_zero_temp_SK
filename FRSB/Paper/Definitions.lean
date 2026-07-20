import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic.NormNum

/-!
# Definitions for Theorems 1.2 and 1.3

This file records the common measure-theoretic language used by
`thm:finite-temperature`, `thm:zero-temperature`, and their dependencies.
The definitions follow the half-open-interval and Stieltjes conventions in
`eq:intro-zero-class` exactly.
-/

open MeasureTheory Set Filter
open scoped ContDiff

namespace FRSB.Paper

noncomputable section

/-- The time domain `[0,1)` used in `eq:intro-zero-class`. -/
abbrev UnitHalfOpen := Set.Ico (0 : ℝ) 1

/-- The compact interval `[0,1]` in which the closure assertion of
`eq:zero-main` is taken. -/
abbrev UnitClosed := Set.Icc (0 : ℝ) 1

/-- The point zero, regarded as an element of `[0,1)`. -/
def unitHalfOpenZero : UnitHalfOpen := ⟨0, by norm_num⟩

noncomputable instance : MeasureSpace UnitHalfOpen :=
  Measure.Subtype.measureSpace

/-- Closed intervals in `[0,1)` are compact.  Mathlib does not register this
instance automatically for a half-open interval subtype. -/
noncomputable instance : CompactIccSpace UnitHalfOpen where
  isCompact_Icc := by
    intro a b
    apply Subtype.isCompact_iff.mpr
    simpa using (isCompact_Icc :
      IsCompact (Set.Icc (a : ℝ) (b : ℝ)))

/-- Smoothness on a half-open real interval.  This is the meaning assigned in
the manuscript to `C^\infty([a,b))`: smoothness on every compact interval
`[a,T]` with `T < b`, with derivatives at `a` taken from the right.

This definition is used for `rho_beta` in
`thm:finite-temperature-structure` and `rho_infty` in
`thm:zero-temperature`. -/
def SmoothOnIco (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ T, a ≤ T → T < b → ContDiffOn ℝ ∞ f (Set.Icc a T)

/-- Right continuity of a real function after restricting its domain to
`[0,1)`, as required in `eq:intro-zero-class`. -/
def RightContinuousOnUnitHalfOpen (f : ℝ → ℝ) : Prop :=
  ∀ t : UnitHalfOpen,
    ContinuousWithinAt (fun s : UnitHalfOpen ↦ f s) (Set.Ici t) t

/-- The class `U` in `eq:intro-zero-class`.

Values of `toFun` outside `[0,1)` are deliberately ignored.  Keeping an
ambient-real representative makes classical derivatives such as
`gamma_star'` expressible with Mathlib's standard `deriv`, while every field
of this structure concerns only the domain specified in the paper. -/
structure OrderParameter where
  toFun : ℝ → ℝ
  nonnegative' : ∀ t : UnitHalfOpen, 0 ≤ toFun t
  monotoneOn' : MonotoneOn toFun (Set.Ico 0 1)
  rightContinuous' : RightContinuousOnUnitHalfOpen toFun
  integrableOn' : IntegrableOn toFun (Set.Ico 0 1)

instance : CoeFun OrderParameter (fun _ ↦ ℝ → ℝ) :=
  ⟨OrderParameter.toFun⟩

namespace OrderParameter

/-- The restriction of an order parameter to `[0,1)`, bundled as Mathlib's
monotone right-continuous `StieltjesFunction`. -/
def toStieltjesFunction (gamma : OrderParameter) :
    StieltjesFunction UnitHalfOpen where
  toFun := fun t ↦ gamma t
  mono' := by
    intro a b hab
    exact gamma.monotoneOn' a.property b.property hab
  right_continuous' := gamma.rightContinuous'

/-- The Stieltjes measure `d gamma` on `[0,1)` with the manuscript's endpoint
convention `d gamma ({0}) = gamma(0)` from `eq:intro-zero-class`.

Mathlib's Stieltjes measure on a type with a least element assigns zero mass
to that least element.  The explicit Dirac summand is therefore necessary and
is part of the definition, not an additional assumption. -/
def stieltjesMeasure (gamma : OrderParameter) : Measure UnitHalfOpen :=
  ENNReal.ofReal (gamma 0) • Measure.dirac unitHalfOpenZero +
    gamma.toStieltjesFunction.measure

/-- The relative support `supp_[0,1) (d gamma)` used in
`eq:zt-minimizer-notation` and `eq:zero-main`. -/
def stieltjesSupport (gamma : OrderParameter) : Set UnitHalfOpen :=
  gamma.stieltjesMeasure.support

end OrderParameter

/-- The support of a measure relative to a measurable subset `s` of its
ambient space.  It is represented in the subspace topology on `s`, matching
notations such as `supp_[0,q_beta)` in
`thm:finite-temperature-structure`. -/
def relativeSupport {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (mu : Measure X) (s : Set X) : Set s :=
  (mu.comap Subtype.val).support

/-- Closure of `A` in the subspace topology on `ambient`, transported back to
the ambient type.  This expresses the relative closure used in
`thm:finite-temperature-structure` and `eq:zero-main`. -/
def relativeClosure {X : Type*} [TopologicalSpace X]
    (ambient A : Set X) : Set X :=
  Subtype.val '' closure {x : ambient | (x : X) ∈ A}

/-- The closure of `[0,1)` relative to `[0,1]` is all of `[0,1]`, as used in
the second assertion of `eq:zero-main`. -/
theorem relativeClosure_unitHalfOpen :
    relativeClosure UnitClosed UnitHalfOpen = UnitClosed := by
  have hset :
      {x : UnitClosed | (x : ℝ) ∈ UnitHalfOpen} =
        Set.Iio (⊤ : UnitClosed) := by
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨x.property.1, hx⟩
  have hnonempty : (Set.Iio (⊤ : UnitClosed)).Nonempty := by
    refine ⟨⟨0, by norm_num⟩, ?_⟩
    change (0 : ℝ) < 1
    norm_num
  unfold relativeClosure
  rw [hset, closure_Iio' hnonempty]
  simp [UnitClosed]

/-- A nonnegative density on the half-open time interval, interpreted as the
measure `rho(t) dt` on `[0,1)`. -/
def densityMeasureOnUnitHalfOpen (rho : ℝ → ℝ) : Measure UnitHalfOpen :=
  (volume : Measure UnitHalfOpen).withDensity
    (fun t : UnitHalfOpen ↦ ENNReal.ofReal (rho t))

/-- Data in the external positive-temperature structure theorem
`thm:finite-temperature-structure` (`Lopatto2026`, Theorem 1.1).

The measure is represented on the ambient real line and is required to be a
probability measure supported on `[0,q]`. -/
structure PositiveTemperatureStructure (beta : ℝ) where
  mu : Measure ℝ
  q : ℝ
  c : ℝ
  rho : ℝ → ℝ
  q_mem : q ∈ Set.Ioo 0 1
  c_mem : c ∈ Set.Ioo 0 1
  rho_nonnegative : ∀ t ∈ Set.Ico 0 q, 0 ≤ rho t
  rho_smooth : SmoothOnIco rho 0 q
  probability : IsProbabilityMeasure mu
  decomposition :
    mu = ((volume : Measure ℝ).withDensity
        (fun t : ℝ ↦ ENNReal.ofReal (rho t))).restrict
        (Set.Ico 0 q) + ENNReal.ofReal c • Measure.dirac q
  support_eq : mu.support = Set.Icc 0 q
  density_support_closure :
    relativeClosure (Set.Icc 0 q)
        (Subtype.val '' relativeSupport
          ((volume : Measure ℝ).withDensity
            (fun t : ℝ ↦ ENNReal.ofReal (rho t)))
          (Set.Ico 0 q)) = Set.Icc 0 q
  only_atom : ∀ x : ℝ, mu (Set.singleton x) ≠ 0 ↔ x = q

end

end FRSB.Paper
