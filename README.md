# Exponential separation of analytic self-conformal sets on the real line

Lean 4 formalisation of the paper by Balázs Bárány, István Kolossváry and Sascha Troscheit.
The [preprint](https://arxiv.org/abs/2509.07888) is on arXiv; the theorem numbers and
correspondence below refer to the revised working manuscript `analytic.tex` of 5 October 2026,
which includes corrections made after arXiv v2.

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
statements have explicit literature hypotheses: Bowen's Theorem 1.4 (one-sided full-shift
specialisation), Rapaport's Theorem 1.2 together with Feng–Hu exact dimensionality, and Rapaport's
Corollary 1.3. These results are stated and cited in the challenge, not proved here.

## Statements and correspondence

[Challenge.lean](Challenge.lean) contains twelve headline theorems, each with an intentional
`sorry`, and their definitions over Mathlib alone. [Solution.lean](Solution.lean) repeats that
vocabulary and proves the theorems from [AnalyticESC](AnalyticESC.lean). The solution and library
are free of `sorry`. [comparator.json](comparator.json) selects the twelve theorems and permits
only `propext`, `Classical.choice` and `Quot.sound`; there are no literature axioms.

[paper-correspondence.yaml](paper-correspondence.yaml) maps 26 theorem, lemma, proposition,
corollary and definition environments to Lean and records the precise qualifications.
[formalization.yaml](formalization.yaml) gives
provenance and a summary of the differences. The main limitations are:

- Corollary 1.7 is formalised for `N ≥ 2`; its trivial `N = 1` case is omitted.
- The internal analytic function space omits continuity on the closed complex neighbourhood.
  Thus Lemmas 2.1, 2.4 and 5.1 use a different space from the manuscript.
- Several proof routes differ: Cauchy derivative estimates, the condensation dichotomy,
  direct construction of the dual attractor, and construction of the linearising map by a limit.
  Theorem 1.12(a) follows the manuscript's periodic-point argument.
- Proposition 4.2 uses the manuscript's multiplicative perturbation and supplies the two omitted
  second-derivative estimates. Lean handles empty `𝒵` by enlarging the constants; the manuscript
  adjoins an auxiliary point to `𝒵`.

These qualifications prevent describing the development as a literal verification of every
proof as printed. Automated correspondence checks do not replace mathematical review.

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
