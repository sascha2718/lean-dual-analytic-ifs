# Exponential separation of analytic self-conformal sets on the real line

Lean 4 formalisation of *On exponential separation of analytic self-conformal sets on the real line*
by Balázs Bárány, István Kolossváry and Sascha Troscheit
([arXiv:2509.07888](https://arxiv.org/abs/2509.07888)). The reference text is `../analytic.tex`,
identified by the source fingerprints in [paper-correspondence.yaml](paper-correspondence.yaml).
Theorem numbers in the Lean declarations and documentation follow this manuscript.

## Scope

The library proves genericity of SESC in the relative `𝒞²` topology, the dual-projection and
explicit distortion criteria, conjugacy characterisations, and supporting results of Sections 2–5.
It includes both examples of Section 1.2.2 and the independence of the admissible radius for the
dual operators, attractor, SSC, singleton property and common fixed points of dual compositions.

The dimension consequences use explicit literature hypotheses. The polynomial example includes
local dimension `s(Φ) - 1/3` at zero and the bound `D_μ(q) ≤ q(s(Φ) - 1/3)/(q - 1)`.
The non-polynomial example proves SESC with `α = 1/4`, `β = 1/2` and an admissible radius
with `c_max < 1/5`.

**Excluded:** Remark 2.4 on Schwarzian derivatives and Möbius conjugacy, by author instruction,
and the background remark comparing smooth and analytic conjugacy. Corollary 1.7 is formalised
for `N ≥ 2`, omitting its trivial `N = 1` case. Proposition 1.8 explicitly assumes `N ≥ 2` in Lean.
Maps are represented by holomorphic extensions; proof constants may be larger than those displayed.
The correspondence manifest records the remaining representation and proof differences.

## Statements and literature inputs

[Challenge.lean](Challenge.lean) contains twelve headline statements, each with an
intentional `sorry`, and their minimal vocabulary over Mathlib. [Solution.lean](Solution.lean)
repeats that vocabulary and proves the statements from [AnalyticESC](AnalyticESC.lean).
The library and solution have no proof holes. The non-polynomial example and radius-independence
results are proved in the library and are outside the twelve Challenge endpoints.

Five headline statements have named literature hypotheses:

- `BowenGibbsStatement`: Bowen, *Equilibrium states and the ergodic theory of Anosov
  diffeomorphisms*, LNM 470 (1975), [Theorem 1.4](https://doi.org/10.1007/BFb0081279),
  specialised to the one-sided full shift.
- `RapaportMeasureStatement`: Rapaport, [arXiv:2412.16753v2](https://arxiv.org/abs/2412.16753v2),
  Theorem 1.2, together with exact dimensionality from Feng–Hu,
  [*Dimension theory of iterated function systems*](https://doi.org/10.1002/cpa.20276), Theorem 2.8.
- `RapaportSetStatement`: Rapaport, the same paper, Corollary 1.3.

These are hypotheses, not axioms. [comparator.json](comparator.json) selects the twelve endpoints
and permits only `propext`, `Classical.choice` and `Quot.sound`.

[paper-correspondence.yaml](paper-correspondence.yaml) maps statements, remarks and selected prose
to Lean or an explicit exclusion. Fingerprints detect changes even when labels and counts stay
fixed; a manuscript fingerprint also flags additions outside mapped passages. Update fingerprints
only after reviewing the changed mathematics and its coverage. These checks detect source drift;
they do not establish mathematical equivalence. [formalization.yaml](formalization.yaml) records
scope, qualifications, literature sources, authorship and AI assistance.

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
development and review. The Lean sources use the [Apache License 2.0](LICENSE).
