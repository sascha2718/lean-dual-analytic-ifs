# ExactOverlaps

This directory contains 164 modules of the Lean library of Samuel Kittle and Constantin Kogler,
*The exact overlaps conjecture for self-similar measures on the real line*,
arXiv:2610.10511v1 (2026): the dependency closure of the modules used by
`AnalyticESC/Literature/Hochman`, `AnalyticESC/Literature/SelfConformal/FengHu` and
`AnalyticESC/Literature/SelfSimilar/FengHu`, chiefly the inverse theorem for entropy
`ExactOverlaps.Entropy.exists_sufficient_inverse_entropy` and the dyadic entropy toolkit.

- [Public source](https://github.com/ckkogler/exact-overlaps-one-dim-lean)
- Revision: `99c43adec5c5127ff9a65663641fe51f57c8f7d3`, taken from the vendored copy in the
  library `FractalGeometry`.
- Every file is unchanged apart from the module names of its imports (prefixed by
  `AnalyticESC.Literature`), the position of the `module` line, the file-level option
  `maxSynthPendingDepth 3` (the library's Lake option) and a provenance paragraph in its docstring.
- The namespaces are those of the source (`ExactOverlaps.*`).
- The BSD Zero Clause licence is in [LICENSE](LICENSE); the adapted `LpSelfSimilar` code's notice
  is retained in [LpSelfSimilar-LICENSE](LpSelfSimilar-LICENSE).
