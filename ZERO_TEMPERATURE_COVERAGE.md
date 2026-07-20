# Zero-temperature Lean coverage audit

This report audits `my_paper.tex` against the current Lean sources.  It is an
inventory, not a claim that the missing analysis has been verified.

## Printed numbering

The TeX source has exactly three theorem environments in Section 1:

| Printed result | TeX label | Content |
|---|---|---|
| Theorem 1.1 | `thm:finite-temperature-structure` | cited positive-temperature structure theorem |
| Theorem 1.2 | `thm:finite-temperature` | quantitative endpoint control |
| Theorem 1.3 | `thm:zero-temperature` | zero-temperature smooth density and full support |

There is **no Theorem 1.4** in this version of `my_paper.tex`.  A later
temperature-convergence draft appears inside a `\iffalse ... \fi` block and
is excluded from the compiled paper.  It is therefore outside the
formalization target.

The theorem-like environments use counters aliased to the `theorem` counter;
lemma and proposition counters are **not independent**.  The active
zero-temperature Section 3 chain is therefore Lemma 3.1, Proposition 3.2,
Lemmas 3.3--3.6, Proposition 3.7, Lemma 3.8, Propositions 3.9--3.10, and
Lemmas 3.11--3.13. Section 4 contains Propositions 4.1--4.4. Active Appendix
A contains Lemmas A.1--A.2 and Proposition A.3. Active Appendix B supplies
proofs of Lemma 2.2 and Lemmas 3.3, 3.4, 3.6, 3.12, and 3.13 rather than
introducing additional numbered results.
A second `\iffalse ... \fi` block inside Appendix B is excluded as well.

## Current status of Theorem 1.3

`FRSB/Paper/Theorem_1_3_ZeroTemperatureStructure.lean` faithfully states the final conclusion as
`Theorem1_3Conclusion`. Lean now proves

```text
Theorem1_3Conclusion zeroTemperatureParisiMinimizer.
```

The unresolved PDE/Itô statements are explicit axioms returning analytic data,
not the final conclusions. Lean constructs `rho_infinity` as a moment quotient,
proves its smoothness, derives both gap exclusions by contradiction, obtains
`gamma_star(0)=0` from the density identity, and performs the final
measure-theoretic/set-theoretic assembly.

## Paper-result coverage

“Algebra only” means Lean proves a scalar identity after its analytic/PDE
identities are supplied as hypotheses; it is not a translation or proof of
the full paper result.

| Result | Citation status in the paper | Current Lean coverage |
|---|---|---|
| Lemma 3.1 `lem:zt-PDE-facts` | assembled from Chen--Handschy--Lerman Prop. 2, Thm. 5 and Auffinger--Chen--Zeng Props. 2--3 | missing; eligible for carefully matched external axioms |
| Proposition 3.2 `prop:zt-variational-conditions` | directional derivative and consistency/stability rely on cited CHL results; support at zero is cited from an external zero-field argument | missing as a proposition; `0 ∈ supp(d gamma_star)` is now an explicitly named external axiom with its CHL provenance |
| Lemma 3.3 `lem:zt-parabolic-stability` | manuscript proof adapts cited interior estimates but includes a local stability argument | partial: the manuscript's global gradient difference-quotient estimate is Lean proved directly from the common second-derivative bound and uniform function convergence. PDE comparison and the cited interior estimates supplying those bounds remain open |
| Lemma 3.4 `lem:zt-regularized-terminal-data` | manuscript proof, using cited regularity/maximum-principle tools | partial: the explicit negative third derivative and abstract final sign-limit implication are Lean proved; the terminal approximation, derivative convergence, parabolic propagation, and higher spatial-derivative convergence remain incomplete |
| Lemma 3.5 `lem:zt-Q-dynamics` | manuscript-original elementary consequence of PDE/Fokker--Planck equations | substantial partial coverage: the jump identity is proved as a function equality, and the heat identity is proved both pointwise and throughout an open time strip with actual time/space derivative witnesses from explicit PDE and Fokker--Planck hypotheses; construction of the density and classical equations remains open |
| Lemma 3.6 `lem:zt-bridge-formula` | manuscript proof; Girsanov idea compared with Lopatto | missing |
| Proposition 3.7 `prop:zt-H-monotonicity` | manuscript-original proof (heat TP2, jumps, approximation) | partial: the quotient identity `H=r^2-r_x`, including its functional derivative form, is proved; positivity, log-concavity, and monotonicity remain open |
| Lemma 3.8 `lem:zt-Ito-identities-general` | semimartingale identities explicitly cited from CHL Lemma 3; regularity/assembly local | missing; cited SDE identities may be axiomatized precisely |
| Proposition 3.9 `prop:zt-finite-KJ` | originates in Lopatto Prop. 3.6, but the paper supplies a self-contained appendix proof | partial: the `K`-average consequence, parameter-decrease preservation, and exact `(log cosh,1)` initialization are Lean proved; the finite-cascade object, Cole--Hopf PDE propagation, endpoint inputs, and maximum-principle proof remain open |
| Proposition 3.10 `prop:zt-zero-temp-KJ` | manuscript scaling/limit argument | missing |
| Lemma 3.11 `lem:zt-fixed-slope` | manuscript-original differentiated PDE evolution and positivity | algebra only: seven small scalar lemmas in `SlopeAlgebra.lean`; no functional statement |
| Lemma 3.12 `lem:zt-tails` | manuscript-original appendix proof using standard Gaussian/Mills estimates | small Appendix B substep proved: bounded drift gives the exact nested lower-tail events and probability bracket; Gaussian estimates and the full lemma remain open |
| Lemma 3.13 `lem:zt-polynomial-moment-regularity` | manuscript-original appendix proof; low-order identities also appear in cited work | substantial deterministic partial coverage: correctly numbered `Lemma_3_13_*` files prove finite affine-in-`gamma` moment closure, the integrated-identity implication, and the exact `[0,T]` `ContDiffOn` conclusion with one-sided endpoint derivatives. Base continuity, any broader repeated polynomial-combination closure, and derivation from Itô/Girsanov and martingale analysis remain open |
| Proposition 4.1 `prop:zt-crossing` | manuscript-original; parallels Lopatto Prop. 9.1 but adds essential new inputs | substantial deterministic core proved: separate modules establish the centered left boundary, boundary-free integration by parts, exact residual inequality, and derive the crossing rule from the differentiated PDE decomposition; PDE/tail/covariance inputs remain open |
| Proposition 4.2 `prop:zt-no-internal-gap` | manuscript-original consequence of crossing and strict moment inequality | substantial deterministic core proved: both integration-by-parts identities, the weighted-zero identity, strict weighted-moment inequality, final contradiction, and the bridge from no empty internal intervals to `IntervalClosed` are Lean theorems; the PDE-derived crossing sign pattern and endpoint identities remain inputs |
| Proposition 4.3 `prop:zt-no-terminal-gap` | manuscript-original boundary analysis | substantial final core proved: relative closedness/cofinality, DCT scaling, ratio asymptotic, the Gaussian CDF-as-integral and derivative, the exact CDF/PDF primitive identity and decay, CDF/density boundary limits, the density-square and whole-line CDF-product integrals, the resulting `4/√π` coefficient, and Step 4 contradiction; Cole--Hopf boundary limits and domination remain open |
| Proposition 4.4 `prop:zt-smoothness` | manuscript-original consequence of saturated consistency and Itô identities | substantial deterministic bootstrap proved: the exact a.e.-to-pointwise representative step on `[0,T]`, quotient regularity, the combined moment-quotient induction to `C^∞`, and interval-level Stieltjes-density identity; stochastic moment regularity and its application to the Parisi diffusion remain open |
| Theorem 1.3 `thm:zero-temperature` | manuscript main theorem | conclusion proved for the canonical minimizer from five explicit zero-temperature axioms; downstream deductions kernel-checked |

## Active appendix coverage

The table records the active manuscript Appendix, but the root Lean target
imports only the verified rows and substeps identified below. Disabled TeX
blocks and incomplete wrapper modules are not part of the passing root target.

| Active appendix result | Current Lean coverage |
|---|---|
| Lemma A.1 `lem:app-endpoint-expansion` | partial: `Lemma_A_1_LogCoshEndpointExpansion.lean` proves the printed initial coefficients `1,-1/2,1/3` and an explicit `O(e^{-8x})` remainder; `Lemma_A_1_LogCoshDifferentiatedRemainder.lean` proves exact first-four derivative formulas with the same `e^{-8x}` factor; and `Lemma_A_1_SlopeLinearCoefficient.lean` proves the ratio-limit coefficient `2`. Preservation through the finite Cole--Hopf cascade and inverse-expansion remainder remain open |
| Lemma A.2 `lem:app-comparison` | partial: spatial first/second derivative signs, the one-sided time sign, interior-minimum contradiction, exponential transformation, and transformed compact-strip comparison are Lean proved; the incomplete `Lemma_A_2_PrintedComparison.lean` is excluded from the root target and omitted from this GitHub bundle |
| Proposition A.3 `prop:app-fixed-parameter` | partial: the `eq:app-K-average` consequence `0 ≤ K(B) ≤ J(B)` is proved in `AppendixA/Proposition_A_3_KAverage.lean`; the Cole--Hopf PDE and maximum-principle propagation remain open |
| Appendix B proof of Lemma 2.2 `lem:ft-endpoint-density` | partial downstream ratio/covariance consequences only; bridge, heat/jump, approximation, and monotonicity proof open |
| Appendix B proof of Lemma 3.3 `lem:zt-parabolic-stability` | partial: `AppendixB/Lemma_3_3_SecondDerivativeToGlobalGradient.lean` derives the displayed gradient estimate from the common global second-derivative bound; obtaining that bound from the cited parabolic estimates remains open |
| Appendix B proof of Lemma 3.4 `lem:zt-regularized-terminal-data` | partial: `Lemma_3_4_RegularizedTerminalThirdDerivative.lean` proves the terminal third-derivative formula/sign seed and `Lemma_3_4_ThirdDerivativeSignLimit.lean` proves the abstract final sign-limit implication; the four-module terminal approximation and derivative-convergence chain is incomplete, excluded from the root target, and omitted from this GitHub bundle |
| Appendix B proof of Lemma 3.6 `lem:zt-bridge-formula` | missing |
| Appendix B proof of Lemma 3.12 `lem:zt-tails` | partial: deterministic bounded-drift event bracket and the sign-defect measure bracket leading toward `eq:zt-B-Gaussian-bracket` are proved in the numbered `Lemma_3_12_*` modules |
| Appendix B proof of Lemma 3.13 `lem:zt-polynomial-moment-regularity` | partial: numbered `Lemma_3_13_*` files prove the global and `[0,T]` finite affine-generator regularity chain, including one-sided endpoint derivatives. They do not prove the stochastic identity, base continuity, or any broader repeated polynomial-combination induction; the local `\iffalse ... \fi` block is excluded |

Current direct zero-temperature declarations also include the foundational
definition `transformedDensity`, the heat cancellation, jump rule,
logarithmic-derivative quotient algebra, fixed-slope scalar algebra, and final
support assembly.  These are useful verified substeps, but none by itself
discharges a paper lemma or proposition in full.

## External-reference boundary

Under the requested workflow, an axiom should state only a theorem actually
supplied by an external reference, with the source and numbering documented.
The following are plausible external inputs after statement-by-statement
comparison with the cited papers:

- zero-temperature minimizer existence/uniqueness (Chen--Handschy--Lerman,
  Theorem 4), and the ground-state Parisi formula (Auffinger--Chen);
- PDE regularity/control/diffusion facts explicitly attributed in Lemma 3.1;
- the directional derivative, consistency, and stability statements explicitly
  attributed to Chen--Handschy--Lerman;
- the semimartingale identities attributed to Chen--Handschy--Lerman Lemma 3;
- the finite Cole--Hopf inequalities, if imported in precisely the form proved
  by Lopatto Proposition 3.6 rather than the broader manuscript formulation;

The transformed-density bridge/monotonicity argument, zero-temperature K--J
limit, fixed-slope evolution, tail and moment regularity lemmas, crossing,
gap exclusions, saturated-consistency smoothness, and Theorem 1.3 itself are
manuscript results.  They must not be replaced by project axioms merely
because their proofs use standard or cited tools.

## Proposed one-paper-result-per-file tree

Foundational definition files may contain related definitions but no paper
propositions.  Each paper lemma/proposition should have its own file:

```text
FRSB/ZeroTemperature/
  Foundations/OrderParameter.lean
  Foundations/ParisiPDE.lean
  Foundations/OptimalDiffusion.lean
  Foundations/TransformedDensity.lean
  External/PDEAndDiffusionFacts.lean          # Lemma 3.1, exact cited inputs
  Variational/VariationalConditions.lean      # Proposition 3.2
  Analysis/ParabolicStability.lean             # Lemma 3.3
  Analysis/TerminalRegularization.lean         # Lemma 3.4
  QDynamics/HeatAndJump.lean                   # Lemma 3.5
  QDynamics/BridgeFormula.lean                 # Lemma 3.6
  QDynamics/HMonotonicity.lean                 # Proposition 3.7
  Stochastic/ItoIdentities.lean                # Lemma 3.8
  ColeHopf/FiniteKJ.lean                       # Proposition 3.9
  ColeHopf/ZeroTemperatureKJ.lean              # Proposition 3.10
  FixedSlope/Evolution.lean                    # Lemma 3.11
  Analysis/TailEstimates.lean                  # Lemma 3.12
  Analysis/PolynomialMomentRegularity.lean     # Lemma 3.13
  Support/ArbitraryGapCrossing.lean            # Proposition 4.1
  Support/NoInternalGap.lean                   # Proposition 4.2
  Support/NoTerminalGap.lean                   # Proposition 4.3
  Regularity/Smoothness.lean                   # Proposition 4.4
FRSB/Paper/Theorem_1_3_ZeroTemperatureStructure.lean  # Theorem 1.3 only
```

For strict adherence to the rule, the existing `SlopeAlgebra.lean` and
`SupportAssembly.lean` should eventually become foundation/helper modules;
the paper-level statements above should remain one per file.  Equation-level
helper lemmas may share a helper file only when they are not themselves
paper propositions.
