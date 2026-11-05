# Exponential separation of analytic self-conformal sets on the real line

Lean 4 formalisation of *On exponential separation of analytic self-conformal sets on the real line*
by Balázs Bárány, István Kolossváry and Sascha Troscheit
([arXiv:2509.07888](https://arxiv.org/abs/2509.07888)). 


## Scope

The library formalises the following results for analytic iterated function systems on the real line, together with their supporting results in Sections 2–5:

- **Generic separation (Theorem 1.4):** the strong exponential separation condition (SESC) holds on an open and dense subset of the paper’s analytic class in the relative `𝒞²` topology.
- **Separation criteria (Theorem 1.5 and Proposition 1.8):** a sufficient condition for SESC in terms of dual projections, and an explicit criterion using derivative and distortion bounds.
- **Dimension formulas (Theorem 1.6 and Corollary 1.7):** the dimensions of attractors and self-conformal measures under exponential separation, and an open and dense family with no dimension drop.
- **Conjugacy (Theorem 1.12):** individual-map linearisation and characterisations of analytic conjugacy and sub-conjugacy to self-similar systems through the dual system.

Both examples of Section 1.2.2 are formalised. For the polynomial example, this includes the attractor and measure dimensions, the natural measure’s local dimension at zero, and the resulting drop in its `L^q` dimensions. The library also proves independence of the admissible radius for the dual construction and the properties used in the paper. The required results of Bowen, Rapaport and Feng–Hu are proved within the development.

Corollary 1.7 omits the trivial `N = 1` case, and Proposition 1.8 explicitly assumes `N ≥ 2`. Remark 2.4 on Schwarzian derivatives and Möbius conjugacy, and the background comparison with smooth conjugacy, are outside scope. Maps are represented by holomorphic extensions; detailed correspondence and formulation differences are recorded in `paper-correspondence.yaml`.

## Statements

[Challenge.lean](Challenge.lean) contains twelve headline statements, each with an
intentional `sorry`, and their minimal vocabulary over Mathlib. [Solution.lean](Solution.lean)
repeats that vocabulary and proves the statements from [AnalyticESC](AnalyticESC.lean).
The library and solution have no proof holes. The non-polynomial example and radius-independence
results are proved in the library and are outside the twelve Challenge endpoints.

The dimension statements use three cited results, stated in `AnalyticESC/Dimension/Defs.lean` and
proved in [AnalyticESC/Literature.lean](AnalyticESC/Literature.lean): Bowen's existence theorem
for Gibbs measures ([LNM 470, Theorem 1.4](https://doi.org/10.1007/BFb0081279)), Rapaport's
Theorem 1.2 ([arXiv:2412.16753](https://arxiv.org/abs/2412.16753)) with the exact dimensionality
of [Feng and Hu](https://doi.org/10.1002/cpa.20276), and Rapaport's Corollary 1.3. The proofs in
`AnalyticESC/Literature/` are copied from the library `FractalGeometry` of the third author; they
include Hochman's entropy growth theorem and use the inverse theorem for entropy of the
Kittle–Kogler library [`ExactOverlaps`](https://github.com/ckkogler/exact-overlaps-one-dim-lean),
copied to `AnalyticESC/Literature/ExactOverlaps`.

The file [comparator.json](comparator.json) lists the twelve endpoints in the Challenge file
and permits only the standard `propext`, `Classical.choice` and `Quot.sound` axioms.

The file [paper-correspondence.yaml](paper-correspondence.yaml) maps statements, remarks and selected prose
to Lean or an explicit exclusion. In [formalization.yaml](formalization.yaml) the
scope, qualifications, literature sources, authorship and AI assistance are recorded.

## Build and verification

Lean and Mathlib are pinned to `v4.35.0-rc2`:

```bash
lake build AnalyticESC Challenge Solution
python3 scripts/check_module_headers.py
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_paper_correspondence.py
```

Challenge's `sorry` warnings are intentional. The correspondence check needs `../analytic.tex`;
its regression tests also run in CI without the manuscript. The workstation shares `.lake/packages`
with another project; do not run `lake update` or download a separate Mathlib there.
On a fresh independent checkout, obtain the dependencies with `lake exe cache get` before building.

On Linux, `./comparator-audit.sh` runs the sandboxed Comparator with NanoDa and con-ron.
The [build workflow](.github/workflows/build.yml) performs this audit, and the
[Palomar preflight](.github/workflows/palomar-preflight.yml) runs the registry verifier on demand.
A local build is not a Palomar acceptance verdict.

## Attribution and licence

The paper and formalisation are developed by the same authors, with AI assistance in Lean
development and review. The Lean sources use the [Apache License 2.0](LICENSE). The modules of
`AnalyticESC/Literature/ExactOverlaps` are copied from the Kittle–Kogler library
[`ExactOverlaps`](https://github.com/ckkogler/exact-overlaps-one-dim-lean) under the
[BSD Zero Clause License](AnalyticESC/Literature/ExactOverlaps/LICENSE); the notice of the adapted
`LpSelfSimilar` code is in
[LpSelfSimilar-LICENSE](AnalyticESC/Literature/ExactOverlaps/LpSelfSimilar-LICENSE).
