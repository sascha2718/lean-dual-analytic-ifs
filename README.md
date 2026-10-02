# Exponential separation of analytic self-conformal sets on the real line

This repository contains the Lean 4 formalisation of *On exponential separation of analytic
self-conformal sets on the real line* by Balázs Bárány, István Kolossváry and Sascha Troscheit.

**Status:** every numbered statement of the paper is formalised, with no `sorry` and only the
axioms `propext`, `Classical.choice` and `Quot.sound`. Three cited results, Bowen's theorem on
Gibbs measures and Rapaport's Theorem 1.2 and Corollary 1.3, are stated as in their sources and
are explicit hypotheses of the theorems that use them. Twelve statements, covering Theorems 1.4,
1.5, 1.6 and 1.12, Corollary 1.7, Proposition 1.8 and the example of Section 1.2.2, are audited by
the comparator. [PLAN.md](PLAN.md) lists what is formalised, the issues found in the paper and the
remaining work.

## Results

- **Sufficient condition (Theorem 1.5, formalised and audited):** an analytic IFS whose dual
  natural projections of equal length are pairwise distinct satisfies the strong exponential
  separation condition (SESC). The library also proves Theorem 2.2 (strong separation of the
  dual IFS implies the SESC) and the lemmas of Sections 2 to 4.
- **Explicit criterion (Proposition 1.8, formalised and audited):** distortions `f_i''/f_i'` that
  are far apart at some point, compared with the contraction ratios, give the SESC. The
  three-map example of Section 1.2.2 satisfies it (audited).
- **Dimension (Theorem 1.6 and Corollary 1.7, formalised and audited, assuming Rapaport's
  results):**
  Rapaport's Theorem 1.2 and Corollary 1.3, stated for real analytic maps as in his paper, give
  Theorem 1.6 in the class of the paper, and with Theorem 1.4 the open and dense set of
  Corollary 1.7 (for `N ≥ 2`). In the example, `dim_H Λ = s(Φ) < 1` and `dim μ_p = H(p)/χ < 1`
  (audited).
- **Local dimension of the example (remark at the end of Section 1.2.2, formalised and
  audited):** by Bowen's theorem the potential `s(Φ) log|f'_{ω₀}(π(σω))|` has a Gibbs measure
  `ν`, and the natural measure `μ = ν ∘ π⁻¹` has local dimension `s(Φ) - 1/3` at `0`. Hence its
  `L^q` dimensions satisfy `D_μ(q) ≤ q(s(Φ) - 1/3)/(q - 1) < s(Φ)` for `q > 3s(Φ)` (audited).
- **Linearisation (Lemma 5.1, formalised):** the linearising map of a single map of the class.
- **Genericity (Theorem 1.4, formalised and audited):** the systems satisfying the SESC contain
  an open and dense subset of the space of analytic IFSs in the `𝒞²` metric. The space is the
  union over `ε > 0` of the classes `𝔖_N(ε)`, as in the manuscript.
- **Conjugation (Theorem 1.12, formalised and audited; Theorem 2.3, formalised):** an analytic IFS
  is conjugated, or sub-conjugated, to a self-similar system exactly when the corresponding dual
  natural projections coincide.

## Statements and proofs

[Challenge.lean](Challenge.lean) states the headline results using Mathlib alone, with an
intentional `sorry` per theorem; it contains Theorem 1.5, Proposition 1.8, the example and
Theorem 1.12.
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
