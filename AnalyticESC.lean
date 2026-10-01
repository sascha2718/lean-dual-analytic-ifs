module

public import AnalyticESC.Defs
public import AnalyticESC.Basic
public import AnalyticESC.Words
public import AnalyticESC.Analysis
public import AnalyticESC.Separation
public import AnalyticESC.Dual.Projection
public import AnalyticESC.Dual.Derivatives
public import AnalyticESC.Dual.Attractor
public import AnalyticESC.Main.Closeness
public import AnalyticESC.Main.Dichotomy
public import AnalyticESC.Main.Criterion
public import AnalyticESC.Main.Example
public import AnalyticESC.Generic.Continuity
public import AnalyticESC.Generic.Points
public import AnalyticESC.Conjugation.Koenigs
public import AnalyticESC.Conjugation.Linearisation

/-!
# Exponential separation of analytic self-conformal sets on the real line

Lean formalisation of B. Bárány, I. Kolossváry and S. Troscheit, *On exponential separation of
analytic self-conformal sets on the real line*.

* `Defs`: the vocabulary: the class `S^ω_ε(I)`, IFSs, words, the separation conditions, the dual
  natural projection, the dual IFS and the `𝒞²` metric.
* `Basic`: the neighbourhoods `B_δ`, the constants `c_min` and `c_max`, compositions, and real
  restrictions of holomorphic maps.
* `Words`: finite and infinite words, common prefixes and the compactness of `Σ_* ∪ Σ`.
* `Analysis`: Lemma 3.1 and its iterate, the identity theorem on `B_ε`, and the bound (4.3).
* `Separation`: Definition 1.2 (failure of SESC is weak super-exponential condensation),
  SESC ⇒ ESC, the natural projection and the attractor.
* `Dual.Projection`: the dual natural projection, the cocycle identity, (2.7), Lemma 2.4 (a), (b).
* `Dual.Derivatives`: Lemma 2.8, Corollary 2.9 and Lemma 2.10, by Cauchy estimates.
* `Dual.Attractor`: Lemma 2.1, Lemma 2.4 (c) and Lemma 2.5, (a) ⇔ (c).
* `Main.Closeness`: the estimates (3.2) and (3.3).
* `Main.Dichotomy`: Theorem 1.5 and Theorem 2.2.
* `Main.Criterion`: Proposition 1.8.
* `Main.Example`: the example of Section 1.2.2.
* `Generic.Continuity`: the estimate (2.6) and Lemma 2.6.
* `Generic.Points`: Lemma 4.1.
* `Conjugation.Koenigs`: `Ĥ_f` of (5.1) and the linearising map of (5.2).
* `Conjugation.Linearisation`: the fixed point of a map of the class and Lemma 5.1.
-/
