# TeX-to-Lean correspondence

The paper snapshot is `my_paper.tex`, dated July 19, 2026, with SHA-256
`d48fd8cc23d5004f6fafe13d7850ff3c9b7cb526437ae879f3d92e07d6adcf56`.
Labels, rather than printed theorem numbers, are used because they remain
stable when the TeX layout changes.

## Labels with direct Lean declarations or explicit input fields

| TeX label | Lean file | Declaration(s) | Status |
|---|---|---|---|
| `thm:finite-temperature-structure` | `FRSB/Paper/Definitions.lean`; `FRSB/Paper/ExternalInputs.lean` | `PositiveTemperatureStructure`; `lopatto_positiveTemperatureStructure` | External axiom |
| `thm:finite-temperature` | `FRSB/Paper/Theorem1_2.lean` | `Theorem1_2Conclusion`; `theorem1_2` | Proved from two external axioms |
| `eq:intro-finite-decomposition` | `FRSB/Paper/Definitions.lean` | fields of `PositiveTemperatureStructure` | External structure data |
| `eq:intro-finite-endpoint-bounds` | `FRSB/Paper/Theorem1_2.lean` | `Theorem1_2Conclusion`; `prop_ft_endpoint_quantitative` | Proved from external endpoint data |
| `eq:ft-self-consistency` | `FRSB/PositiveTemperature/EndpointMoments.lean`; `FRSB/Paper/ExternalInputs.lean` | `EndpointLawData.selfConsistency`; `cited_positiveTemperatureEndpointData` | External analytic input; downstream identity checked |
| `prop:ft-endpoint-identities` | `FRSB/PositiveTemperature/EndpointMoments.lean`; `FRSB/PositiveTemperature/EndpointIto.lean` | `EndpointMomentRepresentation`; `EndpointItoData`; `secondMoment`; `balance` | Analytic data external, deterministic deductions proved |
| `eq:ft-endpoint-first-two` | same as preceding row | `EndpointMomentRepresentation.firstMoment`; `EndpointItoData.secondMoment` | Proved from packaged inputs |
| `eq:ft-endpoint-atom-ratio` | `FRSB/PositiveTemperature/EndpointAlgebra.lean` | `endpoint_ratio_of_balance` | Lean proved |
| `eq:ft-unscaled-Gamma-prime` | `FRSB/PositiveTemperature/EndpointIto.lean` | `EndpointItoData.gammaDerivative`; `betaSq_mul_curvature_eq_one` | Formula supplied as input; deduction proved |
| `eq:ft-unscaled-C-moment` | `FRSB/PositiveTemperature/EndpointIto.lean` | `EndpointItoData.curvatureDerivative`; `balance` | Formula supplied as input; deduction proved |
| `lem:ft-endpoint-density` | `FRSB/PositiveTemperature/EndpointCovariance.lean`; `FRSB/Paper/ExternalInputs.lean` | `EndpointDensityRatios`; `cited_positiveTemperatureEndpointData` | External analytic input |
| `eq:ft-endpoint-f-ratio` | `FRSB/PositiveTemperature/EndpointCovariance.lean` | fields of `EndpointDensityRatios` | Represented as packaged ratio identities |
| `eq:ft-strict-covariance` | `FRSB/PositiveTemperature/StrictCovariance.lean`; `FRSB/PositiveTemperature/EndpointCovariance.lean` | `strict_covariance_ratio`; `endpoint_covariance21`; `endpoint_covariance32` | Lean proved |
| `prop:ft-endpoint-quantitative` | `FRSB/PositiveTemperature/EndpointAlgebra.lean`; `FRSB/Paper/Theorem1_2.lean` | `endpoint_quantitative`; `prop_ft_endpoint_quantitative` | Proved from external endpoint data |
| `eq:ft-endpoint-quantitative` | same as preceding row | same declarations | Proved from external endpoint data |
| `thm:zero-temperature` | `FRSB/Paper/Theorem_1_3_ZeroTemperatureStructure.lean`; `FRSB/Paper/ExternalInputs.lean` | `Theorem1_3Conclusion`; `theorem1_3_assembly`; `theorem1_3` | Proved for the canonical minimizer from five explicit zero-temperature axioms and Lean's standard foundations |
| `eq:intro-zero-class` | `FRSB/Paper/Definitions.lean` | `OrderParameter`; `stieltjesMeasure` | Definitions formalized |
| `eq:zero-density-decomposition` | `FRSB/Paper/Theorem_1_3_ZeroTemperatureStructure.lean`; `FRSB/ZeroTemperature/SelectedSmoothDensity.lean` | `Theorem1_3Conclusion`; `noAtoms_of_stieltjes_eq_density`; `noSingularContinuousPart_of_stieltjes_eq_density`; `AnalyticDensityData.rhoInfinity` | Derived by `theorem1_3` from the explicit smooth-density analytic axiom |
| `eq:zero-main` | `FRSB/Paper/Theorem_1_3_ZeroTemperatureStructure.lean`; `FRSB/ZeroTemperature/SupportAssembly.lean`; `FRSB/ZeroTemperature/SelectedGapConsequences.lean` | `Theorem1_3Conclusion`; `supportData_full`; `theorem1_3_assembly`; `theorem1_3` | Full conclusion kernel checked for the canonical minimizer, conditional on the five stated zero-temperature axioms |
| `lem:zt-Q-dynamics` | `FRSB/ZeroTemperature/QDynamics/Lemma_3_5_Heat.lean`; `Lemma_3_5_Jump.lean` | `lemma_3_5_transformedDensity_heat_at`; `lemma_3_5_transformedDensity_jump` | Functional deductions proved from explicit classical PDE/Fokker--Planck hypotheses |
| `eq:zt-Q-heat` | `FRSB/ZeroTemperature/QDynamics/Lemma_3_5_Heat.lean` | `lemma_3_5_transformedDensity_heat_at` | Lean proved from derivative/PDE hypotheses |
| `eq:zt-Q-heat` (open-strip form) | `FRSB/ZeroTemperature/QDynamics/Lemma_3_5_HeatRegion.lean` | `lemma_3_5_transformedDensity_heat_on_region` | Lean proved from classical PDE/Fokker--Planck hypotheses on the region |
| `eq:zt-Q-jump` | `FRSB/ZeroTemperature/QDynamics/Lemma_3_5_Jump.lean` | `lemma_3_5_transformedDensity_jump` | Lean proved |
| `eq:zt-r-H-identity` | `FRSB/ZeroTemperature/QDynamics/Proposition_3_7_LogDerivativeFunctional.lean` | `hasDerivAt_logSlope_and_curvatureIdentity` | Lean proved |
| `prop:zt-crossing` | `FRSB/ZeroTemperature/Crossing/Proposition_4_1_CrossingRule.lean`; `FRSB/ZeroTemperature/Crossing/Proposition_4_1_BoundaryTerms.lean` | `crossing_of_decomposition`; `arbitraryGap_crossing`; boundary-term lemmas | Crossing conclusion and PDE boundary-term algebra Lean proved from explicit analytic/PDE hypotheses |
| `prop:zt-smoothness` | `FRSB/ZeroTemperature/SelectedSmoothDensity.lean`; `FRSB/ZeroTemperature/Smoothness/Proposition_4_4_*.lean`; `FRSB/Paper/ExternalInputs.lean` | `AnalyticDensityData.rhoInfinity`; `AnalyticDensityData.rhoInfinity_smooth`; exact a.e. representative, quotient, combined `C^∞` bootstrap, and interval-density lemmas | Smooth density is constructed from the explicit analytic-data axiom; deterministic representative and bootstrap chain Lean proved |
| `prop:zt-no-internal-gap` | `FRSB/ZeroTemperature/SelectedGapConsequences.lean`; `FRSB/ZeroTemperature/NoInternalGap/Proposition_4_2_*.lean`; `FRSB/Paper/ExternalInputs.lean` | `intervalClosed_of_analyticInputs`; weighted identities, strict comparison, contradiction; `zeroTemperature_internalGapAnalyticInputs` | Derived in the final theorem from a candidate-wise analytic-chain axiom, rather than supplied as a conclusion field |
| `prop:zt-no-terminal-gap` | `FRSB/ZeroTemperature/SelectedGapConsequences.lean`; `FRSB/ZeroTemperature/NoTerminalGap/Proposition_4_3_*.lean`; `FRSB/Paper/ExternalInputs.lean` | `cofinalAtOne_of_analyticInputs`; Gaussian/Fubini chain; `zeroTemperature_terminalGapAnalyticInputs` | Derived in the final theorem from a candidate-wise analytic-chain axiom; the deterministic and exact Gaussian coefficient chain is Lean proved |
| `lem:zt-fixed-slope` | `FRSB/ZeroTemperature/SlopeAlgebra.lean` | `fixed_x_Bt_chain`; `fixed_slope_cancellation`; `z_eq_m_add_K_mul`; `zB_eq_m_add_J`; `phi_B_identity`; `phi_t_identity`; `G_nonnegative` | Pointwise algebra proved; analytic chain rules not formalized |
| `eq:zt-Bt-fixed-x` | `FRSB/ZeroTemperature/SlopeAlgebra.lean` | `fixed_x_Bt_chain` | Lean proved algebra |
| `eq:zt-ct-fixed-B` | `FRSB/ZeroTemperature/SlopeAlgebra.lean` | `fixed_slope_cancellation` | Lean proved algebra |
| `eq:zt-z-KJ-identities` | `FRSB/ZeroTemperature/SlopeAlgebra.lean` | `z_eq_m_add_K_mul`; `zB_eq_m_add_J` | Lean proved algebra |
| `eq:zt-Phi-B` | `FRSB/ZeroTemperature/SlopeAlgebra.lean` | `phi_B_identity` | Lean proved algebra |
| `eq:zt-Phi-time` | `FRSB/ZeroTemperature/SlopeAlgebra.lean` | `phi_t_identity`; `G_nonnegative` | Lean proved algebra from sign inputs |
| `eq:zt-zero-temp-five` | `FRSB/ZeroTemperature/SlopeAlgebra.lean` | hypotheses of `G_nonnegative` | Sign facts assumed by local algebra theorem |
| `prop:app-fixed-parameter`; `eq:app-K-average` | `FRSB/ZeroTemperature/AppendixA/Proposition_A_3_KAverage.lean` | `K_nonnegative_and_le_endpoint_of_average` | Average-inequality substep Lean proved; full Proposition A.3 open |
| `prop:zt-finite-KJ` (Appendix A parameter-decrease step) | `FRSB/ZeroTemperature/AppendixA/Proposition_3_9_ParameterDecrease.lean` | `parameterDecrease_preserves_fiveInequalities` | Exact preservation calculation Lean proved; fixed-parameter propagation and full finite-cascade proposition open |
| `prop:zt-finite-KJ` (Appendix A initial pair) | `FRSB/ZeroTemperature/AppendixA/Proposition_3_9_InitialLogCosh.lean` | `initialLogCosh_slope_curvature_KJ` | Exact inverse-slope curvature and `K=J=0` initialization Lean proved |
| `lem:app-endpoint-expansion`; `eq:app-slope-endpoint-expansion` | `FRSB/ZeroTemperature/AppendixA/Lemma_A_1_SlopeLinearCoefficient.lean` | `slopeCurvature_linearCoefficient_two` | Equivalent ratio-limit deduction for coefficient `2` Lean proved; full Lemma A.1 open |
| `lem:app-comparison` | `FRSB/ZeroTemperature/AppendixA/Lemma_A_2_InteriorMinimumContradiction.lean` | `negativeInteriorMinimum_impossible` | Interior-minimum PDE contradiction Lean proved; compact-strip specialization open |
| `lem:app-comparison` | `FRSB/ZeroTemperature/AppendixA/Lemma_A_2_DegenerateStripComparison.lean` | `degenerateStripComparison_of_minimumSigns` | Compact minimum and boundary argument Lean proved; derivative-sign specialization open |
| `lem:app-comparison` | `FRSB/ZeroTemperature/AppendixA/Lemma_A_2_SpatialFermat.lean`; `Lemma_A_2_SpatialSecondDerivative.lean` | `spatialDerivative_eq_zero_at_stripMinimum`; `spatialSecondDerivative_nonnegative_at_localMinimum` | Spatial first/second derivative signs Lean proved from explicit derivative witnesses |
| `lem:app-comparison` | `FRSB/ZeroTemperature/AppendixA/Lemma_A_2_TimeDerivative.lean` | `timeDerivative_nonpositive_at_terminalMinimum` | Terminal one-sided time derivative sign Lean proved from the left derivative witness |
| `lem:app-comparison` | `FRSB/ZeroTemperature/AppendixA/Lemma_A_2_DegenerateStripComparisonComplete.lean` | `degenerateStripComparison_complete` | Transformed compact-strip comparison core Lean proved from explicit regularity and boundary hypotheses |
| `lem:app-comparison` | development-only `FRSB/ZeroTemperature/AppendixA/Lemma_A_2_PrintedComparison.lean` | intended printed-sign wrappers | Incomplete, excluded from the root target, and omitted from this GitHub verification bundle |
| `lem:zt-tails` (Appendix B bounded-drift step) | `FRSB/ZeroTemperature/AppendixB/Lemma_3_12_UniformTailDriftBracket.lean` | `boundedDrift_lowerTail_probability_bracket` | Deterministic probability bracket Lean proved; full Lemma 3.12 open |
| `lem:zt-tails`; `eq:zt-B-Gaussian-bracket` | `FRSB/ZeroTemperature/AppendixB/Lemma_3_12_SignDefectTailBracket.lean` | `boundedDrift_signDefect_tail_bracket` | Exact sign-defect measure bracket Lean proved; Gaussian specialization and full Lemma 3.12 open |
| `lem:zt-parabolic-stability`; `eq:zt-global-gradient-convergence` | `FRSB/ZeroTemperature/AppendixB/Lemma_3_3_SecondDerivativeToGlobalGradient.lean` | `lemma_3_3_global_gradient_of_second_derivative_bound` | Displayed global gradient estimate derived from the common second-derivative bound; remaining PDE estimates open |
| `lem:zt-regularized-terminal-data`; `eq:zt-D-negative` | `FRSB/ZeroTemperature/AppendixB/Lemma_3_4_ThirdDerivativeSignLimit.lean` | `lemma_3_4_thirdDerivative_nonpositive_of_regularized_limit` | Final sign-limit implication Lean proved; full Lemma 3.4 open |
| `lem:zt-regularized-terminal-data`; `eq:zt-terminal-regularization` | `FRSB/ZeroTemperature/AppendixB/Lemma_3_4_RegularizedTerminalThirdDerivative.lean` | `regularizedTerminal_thirdDerivative_formula_and_neg` | Exact terminal third-derivative formula and strict sign Lean proved; parabolic propagation and convergence remain open |
| `lem:zt-polynomial-moment-regularity`; `eq:zt-polynomial-moment-derivative` | `FRSB/ZeroTemperature/AppendixB/Lemma_3_13_MomentGeneratorRegularity.lean` | `lemma_3_13_moment_contDiff_succ_of_generator` | Complete deterministic derivative-to-regularity implication Lean proved; stochastic generator identity open |
| `lem:zt-polynomial-moment-regularity`; `eq:zt-polynomial-moment-derivative` | `FRSB/ZeroTemperature/AppendixB/Lemma_3_13_FiniteMomentCombinationRegularity.lean` | `lemma_3_13_finite_moment_generator_contDiff` | Exact finite affine-in-`gamma` generator closure and `C^(r+1)` composition Lean proved |
| `lem:zt-polynomial-moment-regularity`; `eq:zt-polynomial-moment-derivative` | `FRSB/ZeroTemperature/AppendixB/Lemma_3_13_ItoIntegralToGeneratorRegularity.lean` | `lemma_3_13_ito_integral_identity_to_generator_regularity` | Exact FTC chain from the Itô expectation identity to `M'=G` and `C^(r+1)` Lean proved |
| `lem:zt-polynomial-moment-regularity`; `eq:zt-polynomial-moment-derivative` | `FRSB/ZeroTemperature/AppendixB/Lemma_3_13_IntervalMomentRegularity.lean` | `lemma_3_13_interval_moment_generator_regularity` | Exact `[0,T]` deterministic `C^(r+1)` conclusion with right/left endpoint derivatives Lean proved; stochastic generator identity remains open |
| `prop:zt-no-terminal-gap`; `eq:zt-terminal-square-root`; `eq:zt-G-nonnegative` | `FRSB/ZeroTemperature/NoTerminalGap/Proposition_4_3_TerminalSquareRootContradiction.lean` | `terminalSquareRoot_contradicts_nonnegative_integral` | Proposition 4.3 Step 4 Lean proved from the square-root lower bound |
| `prop:zt-no-terminal-gap`; `eq:zt-B-boundary-limit`; `eq:zt-rho-boundary-limit`; `eq:zt-rho-terminal-Gaussian-bound`; `eq:zt-boundary-dominator` | `FRSB/ZeroTemperature/NoTerminalGap/Proposition_4_3_DominatedBoundaryScaling.lean` | `tendsto_terminalDeficitIntegral_of_dominated` | Exact dominated-convergence core toward the terminal square-root asymptotic Lean proved |
| `prop:zt-no-terminal-gap`; `eq:zt-terminal-square-root` | `FRSB/ZeroTemperature/NoTerminalGap/Proposition_4_3_TerminalDeficitAsymptotic.lean` | `terminalDeficit_asymptotic_of_scaledIntegral` | Scaled-integral limit to asymptotic-ratio implication Lean proved |
| `prop:zt-no-terminal-gap`; `eq:zt-terminal-square-root` | `FRSB/ZeroTemperature/NoTerminalGap/Proposition_4_3_GaussianCDFWholeLineIntegral.lean` | `terminalBoundaryIntegral_eq_four_div_sqrt_pi_proved` | Full Gaussian/Fubini calculation, including the exact factor `4/√π`, Lean proved |
| `prop:zt-no-terminal-gap`; `eq:zt-terminal-square-root` | `FRSB/ZeroTemperature/NoTerminalGap/Proposition_4_3_GaussianDensitySquareIntegral.lean` | `integral_standardGaussianPDF_sq` | Exact standard-Gaussian density-square integral Lean proved; CDF integration-by-parts bridge remains open |
| `prop:zt-smoothness`; `eq:zt-gamma-quotient-ae` | `FRSB/ZeroTemperature/Smoothness/Proposition_4_4_AERepresentativeOnInterval.lean` | `proposition_4_4_rightContinuous_eq_continuous_of_ae_on_Icc` | Exact a.e.-to-pointwise representative step Lean proved |

## Exhaustive paper-label inventory

Every theorem, proposition, lemma, and equation label in the included TeX
source appears below. Labels covered by the table above have the stated Lean
mapping. Every other label has **no direct Lean declaration in this
repository** and remains part of the unformalized analytic manuscript unless
it is merely definitional context for one of the mapped interfaces.

```text
eq:app-AKJ
eq:app-Cole-Hopf
eq:app-E-PDE
eq:app-F-PDE
eq:app-F-negative
eq:app-J-PDE
eq:app-J-positive
eq:app-JB-positive
eq:app-K-average
eq:app-KJ-identities
eq:app-VLambda-derivatives
eq:app-c2c3-flow
eq:app-endpoint-flow
eq:app-ft-Gaussian-kernel
eq:app-ft-Ito-u
eq:app-ft-PDE-stability
eq:app-ft-alpha-approximation
eq:app-ft-bridge-representation
eq:app-ft-f-approximation
eq:app-ft-heat-convention
eq:app-ft-r-atom
eq:app-ft-r-heat
eq:app-ft-u-basic-properties
eq:app-initial-inequalities
eq:app-kappa-PDE
eq:app-leading-coefficient
eq:app-slope-endpoint-expansion
eq:app-slope-endpoint-remainder
eq:app-spatial-expansion
eq:app-xC-flow
eq:ft-c-endpoint-law
eq:ft-c-subsequential-limit
eq:ft-endpoint-atom-ratio
eq:ft-endpoint-f
eq:ft-endpoint-f-ratio
eq:ft-endpoint-first-two
eq:ft-endpoint-law
eq:ft-endpoint-law-tail
eq:ft-endpoint-quantitative
eq:ft-eta-subsequential-limit
eq:ft-self-consistency
eq:ft-strict-covariance
eq:ft-terminal-value-at-q
eq:ft-unscaled-C-moment
eq:ft-unscaled-Gamma-prime
eq:intro-finite-decomposition
eq:intro-finite-endpoint-bounds
eq:intro-finite-functional
eq:intro-zero-PDE
eq:intro-zero-class
eq:intro-zero-functional
eq:standard-Gaussian-functions
eq:zero-density-decomposition
eq:zero-main
eq:zt-An-C2-convergence
eq:zt-An-jth
eq:zt-B-Gaussian-bracket
eq:zt-B-boundary-limit
eq:zt-B-epsilon-ratio
eq:zt-BCD-shorthand
eq:zt-Bt-fixed-x
eq:zt-C-Gaussian-tail
eq:zt-C-from-integrated-tail
eq:zt-C-second-moment-one
eq:zt-Cole-Hopf-operator
eq:zt-Cole-Hopf-scaling
eq:zt-Cz-x-relations
eq:zt-D-fixed-slope
eq:zt-D-negative
eq:zt-F-tau-def
eq:zt-Fubini-G
eq:zt-G-nonnegative
eq:zt-Gamma-gap-centered
eq:zt-Gamma-gap-endpoints
eq:zt-Gamma-h-G
eq:zt-Gamma-integrand-Phi
eq:zt-Gamma-prime
eq:zt-Gamma-prime-integral
eq:zt-Gamma-second-I
eq:zt-Gamma-second-x
eq:zt-Gamma-strict-moment
eq:zt-Gamma-weighted-second
eq:zt-Gaussian-Mills-bounds
eq:zt-H-heat-ratio
eq:zt-H-jump
eq:zt-H-monotone
eq:zt-H-term-positive
eq:zt-Hscript-L
eq:zt-Hscript-def
eq:zt-Hx-jump
eq:zt-I-prime-decomposition
eq:zt-Phi-B
eq:zt-Phi-G-def
eq:zt-Phi-centered
eq:zt-Phi-time
eq:zt-Q-C2-convergence
eq:zt-Q-Gaussian-derivative-bound
eq:zt-Q-def
eq:zt-Q-heat
eq:zt-Q-heat-convolution
eq:zt-Q-jump
eq:zt-Q-terminal-limit
eq:zt-R0-integration-by-parts
eq:zt-R1-R0-def
eq:zt-R1-term-nonnegative
eq:zt-Stieltjes-bridge
eq:zt-TP2-ratio
eq:zt-approx-slope-derivatives
eq:zt-approx-spatial-derivatives
eq:zt-boundary-dominator
eq:zt-c0n-convergence
eq:zt-consistency-stability
eq:zt-covariance-identity
eq:zt-crossing-B-parity
eq:zt-crossing-kappa-N-w
eq:zt-crossing-rule
eq:zt-crossing-x-parity
eq:zt-ct-fixed-B
eq:zt-derivative-SDEs
eq:zt-directional-derivative
eq:zt-drift-L1-convergence
eq:zt-finite-slope-variables
eq:zt-fixed-B-evolution
eq:zt-gamma-quotient
eq:zt-gamma-quotient-ae
eq:zt-gamma-weak-Q
eq:zt-gap-endpoint-derivatives
eq:zt-general-C-integral
eq:zt-general-Gamma-integral
eq:zt-general-PDE
eq:zt-global-gradient-convergence
eq:zt-global-parabolic-derivative-bound
eq:zt-inverse-time-chain
eq:zt-lambda-smooth-convergence
eq:zt-logw-R
eq:zt-logw-first
eq:zt-minimizer-notation
eq:zt-optimal-SDE
eq:zt-p-epsilon
eq:zt-p-epsilon-bound
eq:zt-parabolic-Ck-stability
eq:zt-parabolic-uniform-stability
eq:zt-polynomial-moment-derivative
eq:zt-polynomial-moment-derivative-bound
eq:zt-r-H-def
eq:zt-r-H-identity
eq:zt-regularized-D-equation
eq:zt-residual-nonnegative
eq:zt-restarted-optimal-SDE
eq:zt-rho-Gaussian-tail
eq:zt-rho-boundary-limit
eq:zt-rho-density
eq:zt-rho-one
eq:zt-rho-terminal-Gaussian-bound
eq:zt-saturated-consistency
eq:zt-scaling-stationarity
eq:zt-score-tail
eq:zt-slope-curvature
eq:zt-slope-variables
eq:zt-smoothness-conclusion
eq:zt-step-gamma-assumption
eq:zt-strict-TP2-definition
eq:zt-tau-lower
eq:zt-tau-upper
eq:zt-terminal-Cole-Hopf
eq:zt-terminal-constant
eq:zt-terminal-regularization
eq:zt-terminal-square-root
eq:zt-ulambda-D-negative
eq:zt-un-smooth-Q
eq:zt-wB-NB
eq:zt-wCz-boundary
eq:zt-weighted-polynomial-integrability
eq:zt-weighted-uniform-tail
eq:zt-xt-fixed-B
eq:zt-y-differential-bracket
eq:zt-z-KJ-identities
eq:zt-z-time-fixed-B
eq:zt-zero-temp-five
lem:app-comparison
lem:app-endpoint-expansion
lem:ft-endpoint-density
lem:zt-Ito-identities-general
lem:zt-PDE-facts
lem:zt-Q-dynamics
lem:zt-bridge-formula
lem:zt-fixed-slope
lem:zt-parabolic-stability
lem:zt-polynomial-moment-regularity
lem:zt-regularized-terminal-data
lem:zt-tails
prop:app-fixed-parameter
prop:ft-endpoint-identities
prop:ft-endpoint-laws
prop:ft-endpoint-quantitative
prop:zt-H-monotonicity
prop:zt-crossing
prop:zt-finite-KJ
prop:zt-no-internal-gap
prop:zt-no-terminal-gap
prop:zt-smoothness
prop:zt-variational-conditions
prop:zt-zero-temp-KJ
thm:finite-temperature
thm:finite-temperature-structure
thm:zero-temperature
```
