module

public import AnalyticESC.Literature.Rapaport.Analytic.Main.Main
public import AnalyticESC.Literature.Rapaport.Analytic.Main.Assembly

@[expose] public section

/-!
# Rapaport's Theorem 1.2

A. Rapaport, *Dimension of self-conformal measures associated to an exponentially separated
analytic IFS on ℝ*, arXiv:2412.16753v2, Theorem 1.2, with the exact dimensionality of D.-J. Feng
and H. Hu, *Dimension theory of iterated function systems*, Comm. Pure Appl. Math. 62 (2009),
Theorem 2.8, in the form `AnalyticESC.RapaportMeasureStatement`: for an analytic system
satisfying `AnalyticESC.RapaportHyp` and a positive probability vector `p`, the self-conformal
measure has local dimension `min {1, H(p)/χ}` at almost every point.

The theorem is deduced from two results proved elsewhere and taken here as hypotheses:

* `EntropyIncreasePoly`: Rapaport's Theorem 3.1 (entropy increase for measures on polynomials),
  which rests on Hochman's entropy growth theorem;
* `FengHuInterface`: Feng–Hu, Theorem 2.8 and Proposition 4.10 (exact dimensionality and the
  entropy of the fibres of the coding map).

Section 4 of Rapaport (`fibreEntropyVanishes`) shows that the fibre entropy vanishes when
`dim μ < 1`; together with Feng–Hu this gives `dim μ = min {1, H(p)/χ}`
(`rapaportMeasure_of_vanishes`).

## Main declarations

* `rapaportMeasure`: `AnalyticESC.RapaportMeasureStatement` from `EntropyIncreasePoly` and
  `FengHuInterface`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Main.RapaportMeasure`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic

/-- Rapaport's Theorem 1.2 (arXiv:2412.16753v2), with the exact dimensionality of Feng and Hu,
in the form `AnalyticESC.RapaportMeasureStatement`, from the entropy increase theorem
(Rapaport's Theorem 3.1) and the Feng–Hu interface for all systems satisfying
`AnalyticESC.RapaportHyp`. -/
theorem rapaportMeasure
    (hEI : ∀ {N : ℕ} [NeZero N] (φ : Fin N → ℝ → ℝ), AnalyticESC.RapaportHyp φ →
      ∀ (p : Fin N → ℝ) (hp : AnalyticESC.IsProbVec p), EntropyIncreasePoly φ p hp)
    (hFH : ∀ {N : ℕ} [NeZero N] (φ : Fin N → ℝ → ℝ), AnalyticESC.RapaportHyp φ →
      ∀ (p : Fin N → ℝ) (hp : AnalyticESC.IsProbVec p), FengHuInterface φ p hp) :
    AnalyticESC.RapaportMeasureStatement :=
  rapaportMeasure_of_vanishes hFH fun φ hφ p hp => fibreEntropyVanishes hφ hp (hEI φ hφ p hp)

end FractalGeometry.Rapaport.Analytic
