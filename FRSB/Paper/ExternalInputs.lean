import FRSB.Paper.Definitions
import FRSB.PositiveTemperature.EndpointAlgebra
import FRSB.ZeroTemperature.SelectedGapConsequences
import FRSB.ZeroTemperature.SelectedSmoothDensity

/-!
# External inputs for Theorems 1.2 and 1.3

This file is the explicit trust boundary for analytic results that are not
formalized locally.  Besides the two positive-temperature inputs, it introduces
the zero-temperature minimizer whose construction belongs to the excluded
variational foundations.  The fact that zero belongs to its Stieltjes support
is the external zero-field input used in the proof of Proposition 3.2.
-/

namespace FRSB.Paper

noncomputable section

open MeasureTheory
open FRSB.PositiveTemperature

/-! ## Zero-temperature external inputs -/

/-- The zero-temperature Parisi minimizer `gamma_star`.

Its construction and minimizing property belong to the zero-temperature
variational foundations, which are deliberately treated as external in the
present formalization scope. -/
axiom zeroTemperatureParisiMinimizer : OrderParameter

/-- External zero-field support input used in the proof of Proposition 3.2.

The manuscript cites the zero-field argument in the paragraph preceding
Chen--Handschy--Lerman, Proposition 5, to conclude that the minimum of the
support is zero.  This declaration records exactly the consequence used
downstream; it is not attributed to the local analytic chain. -/
axiom chenHandschyLerman_zeroField_zero_mem_stieltjesSupport :
  unitHalfOpenZero ∈ zeroTemperatureParisiMinimizer.stieltjesSupport

/-- External PDE/variational data that attach the Proposition 4.1--4.2
crossing and weighted-integral contradiction to every alleged internal gap.
The resulting no-gap theorem is proved locally, not asserted here. -/
axiom zeroTemperature_internalGapAnalyticInputs :
  FRSB.ZeroTemperature.NoInternalGap.AnalyticInputs
    (Subtype.val '' zeroTemperatureParisiMinimizer.stieltjesSupport)

/-- External terminal Cole--Hopf, dominated-convergence, and variational data
for every alleged terminal gap. The terminal-gap exclusion is derived locally
from the square-root contradiction. -/
axiom zeroTemperature_terminalGapAnalyticInputs :
  FRSB.ZeroTemperature.NoTerminalGap.AnalyticInputs
    (Subtype.val '' zeroTemperatureParisiMinimizer.stieltjesSupport)

/-- External stochastic moment/PDE/Itô data for Proposition 4.4.  Lean defines
the density as the supplied moment quotient and proves its smoothness through
the local bootstrap theorem. -/
axiom zeroTemperature_smoothDensityAnalyticData :
  FRSB.ZeroTemperature.Smoothness.AnalyticDensityData
    zeroTemperatureParisiMinimizer

/-- External input `thm:finite-temperature-structure`, cited as
`Lopatto2026`, Theorem 1.1: for every inverse temperature `beta > 1`, the
positive-temperature Parisi measure has the interval-density-plus-endpoint-
atom structure recorded in `PositiveTemperatureStructure`.

This is the only external theorem needed to introduce the endpoint variables
`q_beta` and `c_beta` in `thm:finite-temperature`. -/
axiom lopatto_positiveTemperatureStructure (beta : ℝ) (hbeta : 1 < beta) :
  PositiveTemperatureStructure beta

/-- The endpoint `q_beta` introduced by the cited external theorem
`thm:finite-temperature-structure`. -/
def qBeta (beta : ℝ) (hbeta : 1 < beta) : ℝ :=
  (lopatto_positiveTemperatureStructure beta hbeta).q

/-- The endpoint atom mass `c_beta` introduced by the cited external theorem
`thm:finite-temperature-structure`. -/
def cBeta (beta : ℝ) (hbeta : 1 < beta) : ℝ :=
  (lopatto_positiveTemperatureStructure beta hbeta).c

/-- The positive-temperature Parisi measure `mu_beta` supplied by the cited
external theorem `thm:finite-temperature-structure`. -/
def muBeta (beta : ℝ) (hbeta : 1 < beta) : Measure ℝ :=
  (lopatto_positiveTemperatureStructure beta hbeta).mu

/-- The smooth density `rho_beta` supplied by the cited external theorem
`thm:finite-temperature-structure`. -/
def rhoBeta (beta : ℝ) (hbeta : 1 < beta) : ℝ → ℝ :=
  (lopatto_positiveTemperatureStructure beta hbeta).rho

/-- External analytic input for `prop:ft-endpoint-identities` and
`lem:ft-endpoint-density`, aligned with the endpoint variables supplied by
`lopatto_positiveTemperatureStructure`.

The package uses the self-consistency theorem and PDE regularity cited from
`AuffingerChenProperties`, Theorem 5 and Proposition 1(i), as well as the
positive-temperature transformed-density analysis discussed alongside
`Lopatto2026`.  Its target is deliberately `EndpointData`: all strict
covariance, hyperbolic-secant integral, moment log-convexity, and scalar
endpoint algebra downstream of these analytic facts remain kernel-checked in
this repository. -/
axiom cited_positiveTemperatureEndpointData (beta : ℝ) (hbeta : 1 < beta) :
  {d : EndpointData beta // d.q = qBeta beta hbeta ∧ d.c = cBeta beta hbeta}

/-- The range of `q_beta` in `thm:finite-temperature-structure`. -/
theorem qBeta_mem_Ioo (beta : ℝ) (hbeta : 1 < beta) :
    qBeta beta hbeta ∈ Set.Ioo (0 : ℝ) 1 :=
  (lopatto_positiveTemperatureStructure beta hbeta).q_mem

/-- The range of `c_beta` in `thm:finite-temperature-structure`. -/
theorem cBeta_mem_Ioo (beta : ℝ) (hbeta : 1 < beta) :
    cBeta beta hbeta ∈ Set.Ioo (0 : ℝ) 1 :=
  (lopatto_positiveTemperatureStructure beta hbeta).c_mem

end

end FRSB.Paper
