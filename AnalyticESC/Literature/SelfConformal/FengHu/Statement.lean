module

public import AnalyticESC.Literature.SelfConformal.Vocabulary

@[expose] public section

/-!
# Feng–Hu for self-conformal measures on the line: the interface statement

The statement of D.-J. Feng and H. Hu, *Dimension theory of iterated function systems*,
Comm. Pure Appl. Math. 62 (2009), 1435–1500, Theorem 2.8 (exact dimensionality and the dimension
formula for conformal systems) and Proposition 4.10 (entropy of the conditional measures on the
fibres of the coding map), for a self-conformal measure on the line, in the form used in Section 4
of A. Rapaport, *Dimension of self-conformal measures associated to an exponentially separated
analytic IFS on ℝ*, arXiv:2412.16753v2.

## Main declarations

* `FengHuInterface φ p hp`: the self-conformal measure `μ = Π β` is exact dimensional with
  dimension `d ∈ [0, 1]`, and for `μ`-a.e. `x` the fibre measure `β_x` has cylinder entropy rate
  `H(p) - χ d`, where `χ` is the Lyapunov exponent (in nats).

Copied from the library `FractalGeometry` (module `FractalGeometry.SelfConformal.FengHu.Statement`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.SelfConformal.FengHu

open MeasureTheory Filter Topology

/-- Feng–Hu, Theorem 2.8 and Proposition 4.10, for a self-conformal measure on the line, in the
form used in Section 4 of Rapaport (arXiv:2412.16753v2): `μ` is exact dimensional with dimension
`d ∈ [0, 1]`, and the fibre measures have cylinder entropy rate `H(p) - χ d` (so `d ≤ H(p)/χ`). -/
def FengHuInterface {N : ℕ} [NeZero N] (φ : Fin N → ℝ → ℝ) (p : Fin N → ℝ)
    (hp : AnalyticESC.IsProbVec p) : Prop :=
  ∃ d : ℝ, 0 ≤ d ∧ d ≤ 1 ∧ FractalGeometry.IsExactDim (selfConformal φ p hp) d ∧
    ∀ᵐ x ∂(selfConformal φ p hp),
      Tendsto (fun l : ℕ => cylEntropy (fibre φ p hp x) l / l) atTop
        (𝓝 (AnalyticESC.entropy p -
          (-∑ i, p i * ∫ y, Real.log |deriv (φ i) y| ∂(selfConformal φ p hp)) * d))

end FractalGeometry.SelfConformal.FengHu
