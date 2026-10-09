# Lean working guide

Durable working agreements for the Lean formalisation of *On exponential separation of analytic
self-conformal sets on the real line*. [README.md](README.md) holds scope, differences and build
instructions. Current proof differences and manuscript issues belong in
`paper-correspondence.yaml` and `formalization.yaml`. The cited source is arXiv:2509.07888v2;
the working manuscript `../analytic.tex` is ahead of it, and differences are recorded relative
to v2.
Historical plans are preserved locally under `Archive/RepositoryReview-2026-10-05/`, outside
the upload. Keep development history in git and verification evidence in CI logs.

## Repositories

- `lean/` is its own git repository. The outer repository (the manuscript) ignores it.
- Run git from the relevant repository. Do not commit, push or publish unless authorised.
- Never invoke `latexmk`, a TeX engine or any document build command for the manuscript; read
  the generated logs instead.

## Toolchain and dependencies

- `.lake/packages` is a local symlink to `~/Documents/lean/mathematics_in_lean/.lake/packages`,
  shared with other projects. Never download a separate Mathlib here.
- Do not run `lake update` or change `lean-toolchain`, `lakefile.toml` or `lake-manifest.json` in
  routine work: dependency resolution can alter the shared checkouts. An upgrade must coordinate
  all projects sharing the packages.
- Every Lean source begins with `module` on its own line and uses `public import`; check with
  `python3 scripts/check_module_headers.py`.
- Code copied from other projects records its source in the module
  docstring and is adapted to the module system.

## Library

- The library is `AnalyticESC`, rooted at `AnalyticESC.lean`, which imports every finished
  module. Modules imported by the root, and `Solution`, must be free of `sorry`. Unfinished work
  stays in modules outside the root's imports.
- Only `propext`, `Classical.choice` and `Quot.sound` are permitted. Introducing a literature
  axiom requires the authors' explicit decision. The agreed literature inputs are the named
  hypotheses `BowenGibbsStatement`, `RapaportMeasureStatement` and `RapaportSetStatement`,
  repeated in Challenge, Solution and `Dimension/Defs.lean`.
- Where the Lean proof departs from the paper's proof or statement, record it in the
  manifest note and in `formalization.yaml` under `fidelity.divergences`.

## Challenge and solution files

- Treat `Challenge.lean` as the human-facing problem statement, never as a proof-audit ledger or
  development log.
- Put only the minimal definitions required to state the headline results in `Challenge.lean`,
  any explicitly agreed and precisely stated literature results used as permitted axioms, and the
  headline declarations with `sorry`.
- Every permitted literature axiom must be conspicuously named and cited, identically declared in
  Challenge and Solution, and individually whitelisted in `comparator.json`.
- Prefer named hypotheses to literature axioms: the con-ron kernel, which the CI audit and
  Palomar run, rejects every non-standard axiom. A cited result the authors agree to assume is a
  named, cited `Prop` in Challenge and Solution, stated as in its source, and an explicit
  hypothesis of the endpoints that use it. These endpoints are the only permitted conditional
  statements in `Challenge.lean`.
- Never put proof bodies, proved helper lemmas, internal reductions, conditional variants or
  audit endpoints in `Challenge.lean`.
- Put all proof infrastructure in `Solution.lean` or the library. `Solution.lean` repeats the
  challenge vocabulary without importing `Challenge.lean`.
- Before handing off a challenge, list its endpoints and audit the file for non-hole theorem
  bodies and for definitions the endpoints do not need.
- Preserve the twelve headline endpoints listed in `comparator.json`. Their scope is fixed by
  the authors. If it is unclear whether a result is a headline, ask rather than expanding the
  challenge.

## Correspondence

- `paper-correspondence.yaml` has one entry per statement environment of the paper. Keep it in
  step with the Lean sources and run `python3 scripts/check_paper_correspondence.py` from this
  directory before committing.
- An endpoint becomes audited by adding it to `comparator.json`, to the `alignment` list in
  `formalization.yaml`, and to its manifest entry with status `formalized`.
- Do not change the paper to match the Lean development. Report mismatches to the authors.
