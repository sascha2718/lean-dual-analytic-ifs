# Exponential separation of analytic self-conformal sets on the real line

Lean 4 formalisation of *On exponential separation of analytic self-conformal sets on the real line*
by Balázs Bárány, István Kolossváry and Sascha Troscheit
([arXiv:2509.07888](https://arxiv.org/abs/2509.07888)). The theorem numbers and correspondence below
refer to the revised working manuscript `analytic.tex` of 5 October 2026, which includes corrections
made after arXiv v2.

## Formalised results

- **Genericity (Theorem 1.4):** systems satisfying the strong exponential separation condition
  (SESC) contain an open and dense subset in the `𝒞²` topology, in the union over admissible
  complex neighbourhoods.
- **Separation (Theorem 1.5 and Proposition 1.8):** distinct dual projections imply SESC;
  an explicit distortion criterion applies to the three-map example of Section 1.2.2.
- **Conjugation (Theorem 1.12):** linearisation of an individual map and characterisations of
  conjugacy and sub-conjugacy to self-similar systems through the dual projections.
- **Dimensions (Theorem 1.6, Corollary 1.7 and the example):** the expected set and measure
  dimensions under ESC, and generically for `N ≥ 2`, assuming Rapaport's results.
- **Natural measure of the example:** local dimension `s(Φ) - 1/3` at `0` and
  `D_μ(q) ≤ q(s(Φ) - 1/3)/(q - 1)`, assuming Bowen's Gibbs-measure theorem.

The library also proves the supporting statements of Sections 2–5. Five of the twelve headline
statements have explicit literature hypotheses. These results are stated and cited in the challenge,
not proved here. The precise references are:

- **Bowen:** Rufus Bowen,
  [*Equilibrium states and the ergodic theory of Anosov diffeomorphisms*](https://doi.org/10.1007/BFb0081279),
  Lecture Notes in Mathematics **470**, Springer-Verlag, 1975, **Theorem 1.4**.
  Its one-sided full-shift specialisation is `BowenGibbsStatement`.
- **Feng–Hu:** De-Jun Feng and Huyi Hu,
  [*Dimension theory of iterated function systems*](https://doi.org/10.1002/cpa.20276),
  *Communications on Pure and Applied Mathematics* **62** (2009), no. 11, 1435–1500,
  **Theorem 2.8**. Its exact-dimensionality conclusion is used together with Rapaport's
  Theorem 1.2 in `RapaportMeasureStatement`.
- **Rapaport:** Ariel Rapaport,
  [*Dimension of self-conformal measures associated to an exponentially separated analytic IFS on ℝ*](https://arxiv.org/abs/2412.16753v2),
  arXiv:2412.16753v2, 10 January 2025, **Theorem 1.2** and **Corollary 1.3**.
  These supply the dimension formulae in `RapaportMeasureStatement` and `RapaportSetStatement`,
  respectively.

## Statements and correspondence

[Challenge.lean](Challenge.lean) contains twelve headline theorems, each with an intentional
`sorry`, and their definitions over Mathlib alone. [Solution.lean](Solution.lean) repeats that
vocabulary and proves the theorems from [AnalyticESC](AnalyticESC.lean). The solution and library
are free of `sorry`. [comparator.json](comparator.json) selects the twelve theorems and permits
only `propext`, `Classical.choice` and `Quot.sound`; there are no literature axioms.

[paper-correspondence.yaml](paper-correspondence.yaml) maps 26 theorem, lemma, proposition,
corollary and definition environments to Lean and records the precise qualifications.
[formalization.yaml](formalization.yaml) records the sources, authorship and use of AI, and
summarises the differences.
The main differences are:

- Corollary 1.7 is formalised for `N ≥ 2`; its trivial `N = 1` case is omitted.
- Several proof routes differ slightly: Cauchy derivative estimates, the condensation dichotomy,
  direct construction of the dual attractor, and construction of the linearising map by a limit.
  Theorem 1.12(a) follows the manuscript's periodic-point argument.
- Proposition 4.2 uses the manuscript's multiplicative perturbation but additionally proves the two omitted
  second-derivative estimates. Lean handles empty `𝒵` by enlarging the constants; the manuscript
  adjoins an auxiliary point to `𝒵`.

## Build and verification

Lean and Mathlib are pinned to `v4.35.0-rc2`. On a fresh checkout:

```bash
lake exe cache get
lake build AnalyticESC Challenge Solution
python3 scripts/check_module_headers.py
```

The warnings about `sorry` in Challenge are intentional. The source check enforces the module
headers, the Palomar file-size limits and the exclusion of Lean symlinks. Locally,
`python3 scripts/check_paper_correspondence.py` also checks the manifest against `../analytic.tex`.
The workstation shares `.lake/packages` with another project; do not run `lake update` there.

On Linux, `./comparator-audit.sh` runs the sandboxed Comparator with the bundled NanoDa and
con-ron kernels. The [build workflow](.github/workflows/build.yml) runs this audit from fresh
project build directories. The [Palomar preflight](.github/workflows/palomar-preflight.yml)
runs the registry's verifier on demand. A local Lean build is not a Palomar acceptance verdict.

## Attribution and licence

The paper and formalisation are developed by the same authors, with AI assistance in the Lean
development and review. The Lean sources are distributed under the [Apache License 2.0](LICENSE).
