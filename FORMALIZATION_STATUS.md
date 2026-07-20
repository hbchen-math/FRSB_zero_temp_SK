# Formalization status and dependency ledger

Manuscript baseline: `my_paper.tex` (SHA-256
`d48fd8cc23d5004f6fafe13d7850ff3c9b7cb526437ae879f3d92e07d6adcf56`).

Status meanings:

- **Lean proved**: an unconditional Lean theorem exists in this project.
- **Conditional assembly**: Lean proves the conclusion from explicitly named
  analytic inputs that expose the remaining mathematical obligations.
- **External input**: the manuscript cites the result rather than proving it.
- **Open analytic**: no Lean proof has yet been supplied.

## Main results

| LaTeX label | Role | Status | Lean location or next obligation |
|---|---|---|---|
| `thm:finite-temperature-structure` | Positive-temperature support and endpoint atom | External input | `FRSB/Paper/ExternalInputs.lean`; `lopatto_positiveTemperatureStructure`, corresponding to `Lopatto2026`, Theorem 1.1. |
| `thm:finite-temperature` | Quantitative endpoint scale | Lean proved from explicit external analytic inputs | `FRSB/Paper/Theorem1_2.lean`; `theorem1_2 : Theorem1_2Conclusion` has no witness hypothesis. |
| `thm:zero-temperature` | Smooth density and support `[0,1)` | Lean proved from the explicit selected analytic trust boundary | `FRSB/Paper/Theorem_1_3_ZeroTemperatureStructure.lean`; `theorem1_3` proves the conclusion for the canonical minimizer. |

Theorem 1.2 is unconditional at its Lean interface but depends on the two
project-declared analytic axioms in `ExternalInputs.lean`. Theorem 1.3 is now
unconditional at its Lean interface for the canonical minimizer, while its
unformalized PDE/Itô content remains visible in the axiom ledger.

## Positive temperature

| LaTeX label | Depends on | Status | Formalization task |
|---|---|---|---|
| `eq:ft-self-consistency` | Parisi first variation | External analytic input | Packaged by `cited_positiveTemperatureEndpointData`, citing `AuffingerChenProperties`, Theorem 5. |
| `prop:ft-endpoint-identities` | Self-consistency, Itô formulas, endpoint Cole--Hopf formula | External analytic input plus Lean-proved deterministic assembly | The endpoint law and differentiated formulas are packaged externally; `EndpointItoData.secondMoment` and `.balance` perform the deterministic derivation in Lean. |
| `lem:ft-endpoint-density` | Bridge representation, approximation, monotonicity | External analytic input | Its exact downstream ratio interface is packaged by `cited_positiveTemperatureEndpointData`. |
| `eq:ft-strict-covariance` | Product measure and strict monotonicity | Lean proved | `StrictCovariance.lean` proves the product-measure identity and strict finite-measure ratio theorem. `SechIntegrals.lean` proves the `1/2` and `3/4` reference ratios, and `EndpointCovariance.lean` proves both endpoint applications. |
| `prop:ft-endpoint-quantitative` | Moment identities, transformed density, strict Cauchy--Schwarz | Lean proved from external analytic input | `EndpointDensityRatios.logConvex` proves strict Cauchy--Schwarz as positive variance. `endpoint_quantitative` derives every scalar inequality, and `prop_ft_endpoint_quantitative` specializes it to the cited endpoint variables. |
| `prop:ft-endpoint-laws` | Tightness, Prokhorov, weak convergence | Open analytic | Mathlib has weak-convergence and tightness infrastructure, but the half-line probability normalization must be set up. |

## Zero-temperature variational and PDE structure

| LaTeX label | Depends on | Status | Formalization task |
|---|---|---|---|
| `lem:zt-PDE-facts` | Parabolic PDE and diffusion theory | Open analytic | Define the solution concept first; separate viscosity existence from interior classical regularity. |
| `prop:zt-variational-conditions` | Directional derivative and diffusion identities | Open analytic | Formalize the functional, admissible directions, support measure, and endpoint derivatives. |
| `lem:zt-parabolic-stability` | Comparison and interior derivative estimates | Deterministic global-gradient step proved; PDE analysis open | `AppendixB/Lemma_3_3_SecondDerivativeToGlobalGradient.lean` derives the displayed estimate from convexity, uniform closeness, and the paper's common second-derivative bound. Comparison and cited interior estimates supplying those hypotheses remain open. |
| `lem:zt-regularized-terminal-data` | Stability and maximum principle | Third-derivative seed and abstract final sign-limit implication Lean proved; terminal approximation chain and PDE propagation open | Root-imported Lemma 3.4 files prove the explicit negative third derivative and the abstract passage to `eq:zt-D-negative`. The four incomplete terminal/derivative approximation modules are excluded from the root target and omitted from this GitHub bundle. |
| `lem:zt-Q-dynamics` | Fokker--Planck equation and PDE cancellation | Functional heat/jump deductions Lean proved; analytic construction open | Numbered `Lemma_3_5_*` modules prove the jump function identity and heat equation from actual derivative witnesses plus explicit Parisi/Fokker--Planck hypotheses. Define the diffusion density and prove those hypotheses. |
| `lem:zt-bridge-formula` | Step approximation and Brownian-bridge conditioning | Open analytic | Formalize the step-function case before Stieltjes convergence. |
| `prop:zt-H-monotonicity` | Log-concavity, strict total positivity, bridge approximation | Logarithmic-derivative identity Lean proved; monotonicity open | Numbered `Proposition_3_7_*` modules prove `H = r^2 - r_x`, including the functional derivative statement. Log-concavity, TP2 propagation, and strict monotonicity remain open. |
| `lem:zt-Ito-identities-general` | Spatial regularity and Itô formula | Open analytic | Formalize only the derivative orders actually used downstream. |

## Fixed-slope and crossing argument

| LaTeX label | Depends on | Status | Formalization task |
|---|---|---|---|
| `prop:zt-finite-KJ` | Cole--Hopf propagation and maximum principles | Partial | Appendix A proves the `K`-average consequence, parameter-decrease preservation, and `(log cosh,1)` initialization in numbered Proposition 3.9 modules; the finite-cascade object, fixed-parameter PDE propagation, endpoint estimates, and maximum principles remain open. |
| `prop:zt-zero-temp-KJ` | Scaling, inverse maps, local smooth convergence | Open analytic | Formalize the inverse-coordinate stability estimates before taking limits. |
| `lem:zt-fixed-slope` | PDE differentiation, inverse-function chain rule, K/J inequalities | Algebra Lean proved; analytic chain rules open | `FRSB/ZeroTemperature/SlopeAlgebra.lean`. |
| `lem:zt-tails` | Gaussian estimates for PDE derivatives and diffusion density | Deterministic event bracket Lean proved; analytic estimates open | `AppendixB/Lemma_3_12_UniformTailDriftBracket.lean` proves the active Appendix B bounded-drift tail inclusions and probability inequalities. Gaussian/Mills estimates and the full lemma remain open. |
| `lem:zt-polynomial-moment-regularity` | Itô moment generator and derivative bounds | Deterministic generator regularity and exact interval/endpoint specialization Lean proved; stochastic identity open | Correctly numbered `Lemma_3_13_*` files prove the finite affine-in-`gamma` generator closure, the global integrated-identity implication, and the `[0,T]` `ContDiffOn` version with right derivative at zero and left derivative at `T`. Base continuity, any broader repeated polynomial-combination closure, and derivation of the generator identity from Itô/Girsanov and mean-zero martingales remain open. The later `\iffalse` derivation is excluded. |
| `prop:zt-crossing` | All preceding zero-temperature inputs | Crossing conclusion, boundary integration by parts, and residual algebra Lean proved; upstream PDE identities open | `Crossing/Proposition_4_1_*` proves the centered left boundary, the endpoint-free integration-by-parts identity, the exact residual lower bound, and derives `Gamma''=0 -> Gamma'''>0` from the differentiated decomposition. PDE differentiation, the tail limit supplying the right boundary, and strict covariance remain exposed inputs. |
| `prop:zt-no-internal-gap` | Crossing rule and weighted integral identity | Deterministic contradiction Lean proved; PDE crossing input open | Numbered `Proposition_4_2_*` modules prove the twice-integrated weighted identity, its vanishing, the strict-moment comparison, and the final contradiction. Connect Proposition 4.1 and the endpoint identities to those hypotheses. |
| `prop:zt-no-terminal-gap` | Terminal Cole--Hopf asymptotics | Topological bridge, complete Gaussian integral core, DCT/asymptotic core, and Step 4 contradiction Lean proved; earlier analysis open | Numbered `Proposition_4_3_*` modules prove `Φ'=φ`, `φ'=-xφ`, CDF and density boundary limits, the exact primitive derivative and decay, `∫φ²=1/(2√π)`, `∫Φ(1-Φ)=1/√π`, and hence the required boundary factor `4/√π`. Cole--Hopf boundary limits and domination remain open. |
| `prop:zt-smoothness` | Saturated consistency and moment regularity | Exact representative and deterministic quotient bootstrap Lean proved; stochastic input open | Numbered `Proposition_4_4_*` modules prove the Lebesgue-a.e.-to-pointwise right-continuous representative theorem, quotient regularity, the combined induction to `C^∞`, and the interval Stieltjes-density identity. Formalize polynomial-moment regularity for the Parisi diffusion. |
| final support assembly | No internal gap, no terminal gap, `0 in S` | Lean proved | `support_eq_unitInterior`, `supportData_full`, and `theorem1_3_assembly`. |

## Appendices and inactive TeX

The incomplete full `Lemma_A_2_PrintedComparison` and
`Lemma_3_4_TerminalApproximation` development is outside the user-selected
formalization scope and is not imported by the root `FRSB` target. Its source
is retained for future work; the lower deterministic sublemmas used by the
selected chain remain root-checked.

The entire `sec:temperature-convergence` section is inside `\iffalse ... \fi`
and is not part of the compiled manuscript or this verification target.
All theorem-like environments share the aliased theorem counter. Active
Appendix A therefore has Lemmas A.1--A.2 and Proposition A.3 (not
Proposition A.1); the average inequality used in Proposition A.3 is proved in
`AppendixA/Proposition_A_3_KAverage.lean`, and the coefficient-two asymptotic
substep of Lemma A.1 is proved in
`AppendixA/Lemma_A_1_SlopeLinearCoefficient.lean`. For Lemma A.2, the root
target checks the spatial Fermat signs, one-sided time sign, compact-minimum
contradiction, exponential transformation, and transformed-strip comparison;
the full printed wrapper and its reversed-sign wrapper remain incomplete.
Appendix B has partial checked subproofs toward Lemmas 2.2, 3.3, 3.4, 3.12,
and 3.13; it does not verify those Appendix arguments in full. Its bounded-drift event bracket
for compiled Lemma 3.12 is proved in the correctly numbered files
`AppendixB/Lemma_3_12_UniformTailDriftBracket.lean` and
`AppendixB/Lemma_3_12_SignDefectTailBracket.lean`, and the gradient
difference-quotient estimate for compiled Lemma 3.3 is proved from the common
second-derivative bound in
`AppendixB/Lemma_3_3_SecondDerivativeToGlobalGradient.lean`. A detailed derivation
inside a second Appendix B `\iffalse ... \fi` block is excluded.

## Explicit trusted analytic boundary

The following mathematical interfaces prevent an assumption-free proof. They
are represented by the named axioms in `ExternalInputs.lean`, not hidden
structure fields.

1. **Smooth-density analytic data.** Stochastic moment regularity, the
   Stieltjes-density identity, and endpoint/interior Itô derivative identities
   are supplied by `zeroTemperature_smoothDensityAnalyticData`. Lean constructs
   `rho_infinity` as the quotient, proves its smoothness, and derives
   `gamma_star(0)=0`.
2. **Gap analytic data.** Candidate-wise PDE, crossing-sign, terminal
   asymptotic, and variational inputs are supplied by
   `zeroTemperature_internalGapAnalyticInputs` and
   `zeroTemperature_terminalGapAnalyticInputs`. Lean derives both gap
   exclusions and the full-support conclusion.
3. **Support at zero.** This is the explicitly cited external zero-field input
   from Proposition 3.2.

## Immediate next milestone

The next meaningful target is reduction of the trusted analytic base. For
Theorem 1.2, this would replace
`cited_positiveTemperatureEndpointData` with a construction from a formal SK
Parisi minimizer, PDE solution, and optimal diffusion.

## Compiler and axiom audit

The final audit was run with Lean 4.30.0 and Mathlib `v4.30.0`:

- `lake build`: successful, including the root `FRSB` module;
- `scripts/check_placeholders.sh`: no `sorry` or `admit`, and exactly seven
  whitelisted external axioms;
- `scripts/audit_tex_labels.sh`: every tracked TeX theorem, proposition,
  lemma, and equation label occurs in `my_paper.tex`;
- `#print axioms FRSB.Paper.theorem1_2`: `propext`, `Classical.choice`,
  `Quot.sound`, `FRSB.Paper.lopatto_positiveTemperatureStructure`, and
  `FRSB.Paper.cited_positiveTemperatureEndpointData`;
- `#print axioms FRSB.Paper.theorem1_3` includes the five selected
  zero-temperature declarations in `ExternalInputs.lean`.

The first three names in each `#print axioms` result are Lean/Mathlib
foundational principles. The seven declarations in `ExternalInputs.lean` are
the project-declared mathematical axioms: two used by Theorem 1.2 and five in
the selected zero-temperature trust boundary. Successful
compilation certifies all deductions from that explicit trust boundary.
