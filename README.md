# Lean verification workspace for the FRSB manuscript

This directory is the formalization workspace associated with
`my_paper.tex`. The TeX manuscript
and this directory are intentionally independent, so later cosmetic changes to
the paper do not perturb the Lean project.

The project is pinned to Lean and Mathlib `v4.30.0`. The pin follows the stable
release convention: `lean-toolchain` and the Mathlib revision in
`lakefile.toml` use the same tag.

## Current verification boundary

The current files transcribe the exact conclusions of Theorems 1.2 and 1.3 in
separate Lean modules and formally check the following deterministic parts of
their proofs:

1. the algebra converting the positive-temperature endpoint moment inputs into
   the bounds in `prop:ft-endpoint-quantitative`;
2. the fixed-slope algebra in `lem:zt-fixed-slope`, including the formulas for
   `Phi_B`, `Phi_t`, and the sign of `G`;
3. the final set-theoretic assembly of full support from zero in the support,
   exclusion of internal gaps, and exclusion of a terminal gap.

This is a conditional, not assumption-free, formal verification. The selected
Theorem 1.3 chain is proved for the canonical minimizer, but unresolved PDE,
stochastic, variational, convergence, and Itô inputs are seven explicit axioms
listed in `AXIOMS.md`. The final crossing, gap-exclusion, smoothness-bootstrap,
and support-assembly conclusions are derived in Lean rather than asserted as
axioms. The project contains no `sorry` or `admit` in the root verification
target.

The root target does not claim complete verification of every Appendix result.
In particular, the full printed comparison of Lemma A.2 and the terminal-data
approximation chain for Lemma 3.4 remain incomplete and are excluded from the
root imports; their lower deterministic sublemmas are retained and checked.
See `FORMALIZATION_STATUS.md` and `ZERO_TEMPERATURE_COVERAGE.md`.

For a clean verification release, this GitHub bundle omits the five unfinished,
non-imported development modules: the printed Appendix A.2 wrapper and the four
dependent Lemma 3.4 terminal-approximation modules. Their omission changes no
root import and no declaration reported as verified here.

## Build

Install `elan` first. From this directory, run:

```text
lake update
lake exe cache get
make check
```

The cache command downloads precompiled Mathlib files. `make check` builds the
project, rejects `sorry` and `admit`, and enforces the exact external-axiom
whitelist in `scripts/check_placeholders.sh`.

Run `make audit-tex` after editing the manuscript. It checks that every LaTeX
label tracked by the Lean project still occurs in `my_paper.tex`. To check a
different source explicitly, run

```text
bash scripts/audit_tex_labels.sh ../name-of-later-version.tex
```

## Traceability convention

Lean docstrings name the stable LaTeX labels, for example
`prop:ft-endpoint-quantitative` and `eq:zt-Phi-time`. Do not refer to printed
numbers such as “Proposition 2.3,” since those will change when the TeX file is
edited. When a manuscript statement changes mathematically, update
`FORMALIZATION_STATUS.md` before modifying the corresponding Lean declaration.

## Possible future reduction of the trusted base

1. Build a reusable analytic API for the zero-temperature PDE, its spatial
   derivatives away from terminal time, and the optimal diffusion.
2. Formalize heat evolution and the jump rule for `Q`, followed by the bridge
   formula and monotonicity of `Q_xx / Q`.
3. Formalize the finite Cole--Hopf inequalities and their scaling limit.
4. Formalize the tail estimates and the differentiation of the crossing
   integral. This is the largest single analytic block.
5. Replace the selected zero-temperature analytic axioms one by one with these
   constructions, preserving the already checked downstream proof chain.

The detailed dependency ledger is in `FORMALIZATION_STATUS.md`.
