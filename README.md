# Exponential separation of analytic self-conformal sets on the real line

Lean 4 formalisation of *On exponential separation of analytic self-conformal sets on the real line*
by Balázs Bárány, István Kolossváry and Sascha Troscheit,
[arXiv:2509.07888v2](https://arxiv.org/abs/2509.07888v2) (26 March 2026). The theorem, section and
equation numbers below and in the Lean sources refer to arXiv v2. Where a Lean statement or
proof differs from the printed text, the difference is listed under
[Relation to arXiv v2](#relation-to-arxiv-v2) and recorded in the correspondence files.

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
statements have explicit literature hypotheses. The external results used as hypotheses are stated
and cited in the challenge but are not proved here. Their precise references are:

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

[paper-correspondence.yaml](paper-correspondence.yaml) maps the 26 theorem, lemma, proposition,
corollary and definition environments of arXiv v2 to Lean and records the precise qualifications.
[formalization.yaml](formalization.yaml) records the sources, authorship and use of AI, and
summarises the differences.

## Relation to arXiv v2

The Lean statements differ from the printed statements of arXiv v2 at the following points.

- **The space `𝔖_N`.** Section 1.1 of v2 fixes `ε > 0` and takes `𝔖_N` to be the IFSs with maps
  in `S^ω_ε(I)`. The Lean space `𝔖_N` (`InUnionClass`) consists of the IFSs whose maps lie in
  `S^ω_ε(I)` for some `ε > 0` depending on the system, with the `𝒞²` metric `d₂`. Theorem 1.4 and
  Corollary 1.7 are stated for this space, and their open and dense sets are relative to it.
  Theorems 1.5, 1.6 and 1.12 and Proposition 1.8 are stated for a fixed `ε`, as printed.
- **Proposition 1.8** assumes `N ≥ 2`; v2 does not impose this restriction.
- **Corollary 1.7** is formalised for `N ≥ 2`; its `N = 1` case is omitted.
- **The example of Section 1.2.2.** v2 deduces `dim_H Λ = s(Φ)` and `dim μ_p = H(p)/χ` from
  Corollary 1.7. Lean deduces them from Theorem 1.6, after proving that the attractor is not a
  singleton, `s(Φ) < 1` and `H(p) < χ`, which the endpoint records.
- **Theorem 1.12, first claim.** v2 states that `Φ` is conjugated to an analytic IFS with at least
  one similarity map. Lean states this as follows: for every `i` there is an analytic invertible
  `g` with `g' ≠ 0` on `[0,1]` such that `g ∘ f_i ∘ g⁻¹` is a contracting similarity on `g([0,1])`.
- **Theorem 2.3 (b)** is stated for distinct words `i, j` of the same length; v2 omits
  distinctness.
- **Lemma 2.5.** Items (a), (b) and (c) are formalised. Item (d) of v2, the uniform separation of
  `H_i` and `H_j` over finite words `i, j ∈ Σ_*` with `i₁ ≠ j₁`, is not formalised.
- **Lemma 2.10** is proved for all distinct words `i, j ∈ Σ ∪ Σ_*`; v2 assumes
  `|i ∧ j| < min{|i|, |j|}`.
- **Lemma 4.1** assumes that compositions along distinct finite words differ on `[0,1]`, which
  follows from the absence of exact overlaps assumed in v2.
- **Proposition 4.2** assumes `f([0,1]) ⊆ (0,1)` and produces `g ∈ S^ω_{ε'}(I)` for some `ε' > 0`;
  v2 states `g ∈ S^ω_ε(I)` with the `ε` of `f` and does not assume `f([0,1]) ⊆ (0,1)`. Lean
  chooses equal widths, pads an empty `𝒵` by a point of `[0,1] \ 𝒴`, and proves the two
  second-derivative estimates that v2 leaves to the reader.
- **Lemma 5.1** assumes `b ≠ 0`; v2 states the lemma for all `a, b ∈ ℝ`.
- **The function space `C^ω_ε([0,1])`** of Section 2.1 is represented by the maps holomorphic on
  `B_ε`, continuous on its closure and real on `I`; v2 does not require continuity on the closure.
- **Complex derivatives.** Maps are given by holomorphic extensions, and derivatives at real points
  are complex derivatives, which agree with the real ones.
- **Constants** may be larger than the printed constants.

Some Lean proofs depart from the printed proofs.

- Theorem 2.2 is proved first, and Theorem 1.5 is deduced from it by compactness and Lemma 2.5 (c),
  using only the infinite-word part of (1.5). v2 proves Theorem 1.5 directly and deduces
  Theorem 2.2. The Lean proof of Theorem 2.2 treats the case of finite limit words, which v2 does
  not, and uses (3.3) with the absolute value `|f'_u|^k` in the denominator.
- In the density proof of Theorem 1.4, v2 asserts that exact overlaps can be removed by an
  arbitrarily small perturbation. Lean proves this by an interpolation lemma, which also makes the
  maps send `[0,1]` into `(0,1)`, and fixes the strictly invariant cylinder of Lemma 2.5 (b)
  together with a `d₂`-neighbourhood in which its inclusions persist before choosing `δ` and the
  word length, so that Lemma 2.5 (b) applies to the perturbed system.
- Lemma 2.6 controls the perturbed system with the constants `c_min/2` and a constant in
  `(c_max, 1)`; v2 uses `c_min` and `c_max`.
- Theorem 1.12 (b) treats a common fixed point of `f_i` and `f_j` by commutation, and Theorem 2.3
  treats a singleton attractor separately; the proofs in v2 apply Theorem 1.12 (a) in both cases.

## Build and verification

Lean and Mathlib are pinned to `v4.35.0-rc2`. On a fresh checkout:

```bash
lake exe cache get
lake build AnalyticESC Challenge Solution
python3 scripts/check_module_headers.py
```

The warnings about `sorry` in Challenge are intentional. The source check enforces the module
headers, the Palomar file-size limits and the exclusion of Lean symlinks. Locally,
`python3 scripts/check_paper_correspondence.py` also checks the manifest against the statement
environments and labels in the local file `../analytic.tex`.
The workstation shares `.lake/packages` with another project; do not run `lake update` there.

On Linux, `./comparator-audit.sh` runs the sandboxed Comparator with the bundled NanoDa and
con-ron kernels. The [build workflow](.github/workflows/build.yml) runs this audit from fresh
project build directories. The [Palomar preflight](.github/workflows/palomar-preflight.yml)
runs the registry's verifier on demand. A local Lean build is not a Palomar acceptance verdict.

## Attribution and licence

The paper and formalisation are developed by the same authors, with AI assistance in the Lean
development and review. The Lean sources are distributed under the [Apache License 2.0](LICENSE).
