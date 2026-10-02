module

public import AnalyticESC.Defs
public import AnalyticESC.Basic
public import AnalyticESC.Words
public import AnalyticESC.Analysis
public import AnalyticESC.Separation
public import AnalyticESC.Dual.Projection
public import AnalyticESC.Dual.Derivatives
public import AnalyticESC.Dual.HigherDerivatives
public import AnalyticESC.Dual.Attractor
public import AnalyticESC.Dual.Cylinders
public import AnalyticESC.Main.Closeness
public import AnalyticESC.Main.Dichotomy
public import AnalyticESC.Main.Criterion
public import AnalyticESC.Main.Example
public import AnalyticESC.Main.LocalDimension
public import AnalyticESC.Generic.Continuity
public import AnalyticESC.Generic.Points
public import AnalyticESC.Generic.Class
public import AnalyticESC.Generic.Coincidences
public import AnalyticESC.Generic.Bump
public import AnalyticESC.Generic.Agreement
public import AnalyticESC.Generic.Density
public import AnalyticESC.Generic.OpenDense
public import AnalyticESC.Conjugation.Koenigs
public import AnalyticESC.Conjugation.Linearisation
public import AnalyticESC.Conjugation.Basic
public import AnalyticESC.Conjugation.Uniqueness
public import AnalyticESC.Conjugation.Composite
public import AnalyticESC.Conjugation.Zeros
public import AnalyticESC.Conjugation.Characterisation
public import AnalyticESC.Conjugation.DualConj
public import AnalyticESC.Conjugation.ExactOverlaps
public import AnalyticESC.Dimension.Defs
public import AnalyticESC.Dimension.Pressure
public import AnalyticESC.Dimension.NaturalMeasure
public import AnalyticESC.Dimension.Rapaport
public import AnalyticESC.Dimension.OpenDense
public import AnalyticESC.Dimension.Example
public import AnalyticESC.Dimension.Lq

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
* `Dual.HigherDerivatives`: the identity (2.10) and Lemma 2.7.
* `Dual.Attractor`: Lemma 2.1, Lemma 2.4 (c) and Lemma 2.5, (a) ⇔ (c).
* `Dual.Cylinders`: the cylinder sets of Section 2.1 and Lemma 2.5.
* `Main.Closeness`: the estimates (3.2) and (3.3).
* `Main.Dichotomy`: Theorem 1.5 and Theorem 2.2.
* `Main.Criterion`: Proposition 1.8.
* `Main.Example`: the example of Section 1.2.2.
* `Main.LocalDimension`: the local dimension `s(Φ) - 1/3` at `0` of the natural measure of the
  example, for a measure with the Gibbs property.
* `Generic.Continuity`: the estimate (2.6) and Lemma 2.6.
* `Generic.Points`: Lemma 4.3.
* `Generic.Class`: Lemma 4.1, the classes `S^ω_ε(I)` and their union `S^ω(I)`.
* `Generic.Coincidences`: Lemma 4.2.
* `Generic.Bump`: Proposition 4.4.
* `Generic.Agreement`: dual compositions of two systems that agree along an orbit.
* `Generic.Density`: the density step of the proof of Theorem 1.4.
* `Generic.OpenDense`: Theorem 1.4.
* `Conjugation.Koenigs`: `Ĥ_f` of (5.1) and the linearising map of (5.2).
* `Conjugation.Linearisation`: the fixed point of a map of the class and Lemma 5.1.
* `Conjugation.Basic`: conjugacy and sub-conjugacy to self-similar systems (Definition 1.9).
* `Conjugation.Uniqueness`: uniqueness of linearisations of a single map.
* `Conjugation.Composite`: compositions along words and periodic dual projections.
* `Conjugation.Zeros`: conjugacies by injective analytic maps.
* `Conjugation.Characterisation`: Theorem 1.12.
* `Conjugation.DualConj`: Theorem 2.3.
* `Conjugation.ExactOverlaps`: the remark after the conjecture of Section 1, exact overlaps
  and sub-conjugation.
* `Dimension.Defs`: entropy, Lyapunov exponents, self-conformal measures, equality in (1.6),
  Gibbs measures, and the statements of the cited results of Bowen and Rapaport.
* `Dimension.Pressure`: the pressure and its unique zero, the conformality dimension `s(Φ)`.
* `Dimension.NaturalMeasure`: the natural measure from Bowen's theorem, and its local dimension
  `s(Φ) - 1/3` at `0` in the example.
* `Dimension.Rapaport`: Theorem 1.6 from Rapaport's results, and the remark after it.
* `Dimension.OpenDense`: Corollary 1.7.
* `Dimension.Example`: the dimensions of the attractor and of the self-conformal measures of the
  example of Section 1.2.2.
* `Dimension.Lq`: the `L^q` dimensions of the natural measure of the example.
-/
