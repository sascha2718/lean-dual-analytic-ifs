# Exponential separation of analytic self-conformal sets on the real line

This repository contains the Lean 4 formalisation of *On exponential separation of analytic
self-conformal sets on the real line* by Balázs Bárány, István Kolossváry and Sascha Troscheit.

**Status:** the statements of the paper without open issues are formalised, with no `sorry`
and only the axioms `propext`, `Classical.choice` and `Quot.sound`. Theorem 1.5 is audited by the
comparator. [PLAN.md](PLAN.md) lists what is formalised, the issues found in the paper and the
remaining work.

## Results

- **Sufficient condition (Theorem 1.5, formalised and audited):** an analytic IFS whose dual
  natural projections of equal length are pairwise distinct satisfies the strong exponential
  separation condition (SESC). The library also proves Theorem 2.2 (strong separation of the
  dual IFS implies the SESC) and the lemmas of Sections 2 to 4 that have no open issue.
- **Explicit criterion (Proposition 1.8, formalised and audited):** distortions `f_i''/f_i'` that
  are far apart at some point, compared with the contraction ratios, give the SESC. The
  three-map example of Section 1.2.2 satisfies it (audited).
- **Linearisation (Lemma 5.1, formalised):** the linearising map of a single map of the class.
- **Genericity (Theorem 1.4):** the openness half (Lemma 2.6) and Lemma 4.1 are formalised. The
  density half is not, pending issue I1 of PLAN.md.

Not yet formalised, pending the decisions recorded in PLAN.md: the characterisation of conjugacy to
self-similar systems (Theorem 1.12 and Theorem 2.3).

## Statements and proofs

[Challenge.lean](Challenge.lean) states the headline results using Mathlib alone, with an
intentional `sorry` per theorem; it contains Theorem 1.5, Proposition 1.8 and the example.
[Solution.lean](Solution.lean) proves them from the `AnalyticESC` library. The comparator check
verifies that the solution proves the same statements with the same definitions, using only
`propext`, `Classical.choice` and `Quot.sound`.
[comparator.json](comparator.json) lists the audited declarations.

[paper-correspondence.yaml](paper-correspondence.yaml) records, for every numbered statement of
the paper, whether it is planned, formalised or intentionally left out, and
[formalization.yaml](formalization.yaml) records provenance in the mathlib-initiative format.

## Building

The toolchain is `leanprover/lean4:v4.35.0-rc2` with Mathlib `v4.35.0-rc2`.

```bash
lake exe cache get
lake build
```

On a machine that already holds a built Mathlib at that revision, link its packages instead of
fetching a second copy (`.lake` is not tracked):

```bash
mkdir -p .lake
ln -sfn /path/to/other/project/.lake/packages .lake/packages
```

## Checks

| Command | Checks |
|---|---|
| `python3 scripts/check_module_headers.py` | Every Lean source begins with `module` (Palomar requirement) |
| `python3 scripts/check_paper_correspondence.py` | Manifest against the paper's labels, the Lean sources, `comparator.json`, `Challenge.lean`, `Solution.lean` and `formalization.yaml` (needs the manuscript in the parent directory) |
| `./comparator-audit.sh` | The comparator audit in a `bwrap` sandbox (Linux), skipped while no endpoints are listed |

The [build workflow](.github/workflows/build.yml) builds the library and runs the comparator
audit; the [Palomar preflight](.github/workflows/palomar-preflight.yml) runs Palomar's verifier
on demand.

## Licence

The Lean development is distributed under the [Apache License 2.0](LICENSE).
