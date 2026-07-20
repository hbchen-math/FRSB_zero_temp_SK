# Project-declared axioms

The project declares exactly seven mathematical axioms, all isolated in
`FRSB/Paper/ExternalInputs.lean`:

| Lean declaration | TeX source | External source | Purpose |
|---|---|---|---|
| `FRSB.Paper.lopatto_positiveTemperatureStructure` | `thm:finite-temperature-structure` | `Lopatto2026`, Theorem 1.1 | Supplies the positive-temperature density, endpoint `q_beta`, endpoint atom `c_beta`, support, and atom structure for `beta > 1`. |
| `FRSB.Paper.cited_positiveTemperatureEndpointData` | `eq:ft-self-consistency`, `prop:ft-endpoint-identities`, `lem:ft-endpoint-density` | `AuffingerChenProperties`, Theorem 5 and Proposition 1(i), together with the positive-temperature transformed-density analysis discussed alongside `Lopatto2026` | Supplies the endpoint probability-law, differentiated-Itô, and transformed-density data, aligned with the cited `q_beta` and `c_beta`. |
| `FRSB.Paper.zeroTemperatureParisiMinimizer` | `eq:zt-minimizer-notation` | Zero-temperature variational foundations | Supplies the canonical minimizer while those foundations are outside the selected scope. |
| `FRSB.Paper.chenHandschyLerman_zeroField_zero_mem_stieltjesSupport` | Proposition 3.2 | Zero-field argument in the paragraph preceding Chen--Handschy--Lerman, Proposition 5 | Supplies exactly `0 ∈ supp(d gamma_star)`, as cited by the manuscript. |
| `FRSB.Paper.zeroTemperature_internalGapAnalyticInputs` | Propositions 4.1--4.2 | Unformalized PDE, covariance, endpoint, and variational analysis | Supplies candidate-wise crossing and integral data; Lean derives no internal gap. |
| `FRSB.Paper.zeroTemperature_terminalGapAnalyticInputs` | Proposition 4.3 | Unformalized terminal Cole--Hopf, domination, and variational analysis | Supplies candidate-wise square-root data; Lean derives no terminal gap. |
| `FRSB.Paper.zeroTemperature_smoothDensityAnalyticData` | Proposition 4.4 | Unformalized stochastic moment, PDE, and Itô analysis | Supplies numerator/denominator moment data and analytic identities; Lean constructs the quotient density and proves its smoothness. |

The second declaration is intentionally a broad analytic trust boundary.  It
does not assert the quantitative conclusion of Theorem 1.2 directly: the
strict covariance inequalities, exact hyperbolic-secant integrals, strict
moment log-convexity, endpoint algebra, and squeeze limit are Lean proved.
Neither gap exclusion nor the smooth-density conclusion is axiomatized
directly. The axioms expose candidate-wise analytic data, and the final
conclusions are deductions checked by Lean.

This ledger concerns project-declared mathematical axioms.  Lean's ordinary
logical foundations and noncomputable choice are a separate matter and are
reported by `#print axioms` when auditing individual declarations.
