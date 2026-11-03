module

public import AnalyticESC.Literature.Rapaport.Analytic.Poly

@[expose] public section

/-!
# Interface statements for Rapaport's dimension theorem

Statements, as `Prop`-valued definitions, of the results that connect the parts of the
formalisation of A. Rapaport, *Dimension of self-conformal measures associated to an exponentially
separated analytic IFS on ℝ*, arXiv:2412.16753v2.

## Main declarations

* `HochmanEntropyGrowth`: Theorem 3.2 of Rapaport, which is M. Hochman, *On self-similar sets with
  overlaps and inverse theorems for entropy*, Ann. of Math. 180 (2014), Theorem 2.8, in the form of
  B. Bárány, M. Hochman and A. Rapaport, *Hausdorff dimension of planar self-affine sets and
  measures*, Invent. Math. 216 (2019), Section 4.1.
* `FengHuInterface`: D.-J. Feng and H. Hu, *Dimension theory of iterated function systems*,
  Comm. Pure Appl. Math. 62 (2009), Theorem 2.8 and Proposition 4.10, for self-conformal measures
  on the line, in the form used in Section 4 of Rapaport.
* `EntropyIncreasePoly`: Theorem 3.1 of Rapaport, entropy increase for measures on polynomials
  acting on `C¹` images of a self-conformal measure of dimension less than `1`.

Entropies of measures on `ℝ` and on `𝒫_k` are dyadic entropies in bits; the entropy of a weight
vector, cylinder entropies and the Lyapunov exponent use natural logarithms.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Statements`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic

open MeasureTheory Set Filter Topology FractalGeometry.SelfConformal
open scoped MeasureTheory

/-- Hochman's entropy growth under convolution, in the form of Theorem 3.2 of Rapaport
(arXiv:2412.16753v2): for `0 < ε < 1` there is `η₀(ε) > 0` such that for `m ≥ 1` and
`0 < η < η₀` there are `δ > 0` and `N₀` with the following property for `n ≥ N₀` and `i ≥ 1`.
If `ξ, θ` are probability measures on `ℝ` carried by intervals of length `ε⁻¹ 2^{-i}`, if
`H(ξ, 𝒟_{i+n}) / n > ε`, and if `ℙ_{i ≤ j ≤ i+n}( H(θ_{x,j}, 𝒟_{j+m}) / m < 1 - ε ) > 1 - η`,
then `H(ξ ∗ θ, 𝒟_{i+n}) / n ≥ H(θ, 𝒟_{i+n}) / n + δ`. -/
def HochmanEntropyGrowth : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ m : ℕ, 1 ≤ m → ∀ η : ℝ, 0 < η → η < η₀ →
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ i : ℕ, 1 ≤ i →
    ∀ ξ θ : Measure ℝ, IsProbabilityMeasure ξ → IsProbabilityMeasure θ →
      (∃ a : ℝ, ξ (Set.Icc a (a + ε⁻¹ / 2 ^ i))ᶜ = 0) →
      (∃ b : ℝ, θ (Set.Icc b (b + ε⁻¹ / 2 ^ i))ᶜ = 0) →
      ε < dyadicEntropy ξ (i + n) / n →
      1 - η < levelProb θ i n (fun j x => dyadicEntropy (component θ j x) (j + m) / m < 1 - ε) →
      dyadicEntropy θ (i + n) / n + δ ≤ dyadicEntropy (ξ ∗ θ) (i + n) / n

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

/-- Theorem 3.1 of Rapaport (arXiv:2412.16753v2): entropy increase for measures on polynomials of
bounded degree acting on `C¹` images of `μ`, when `dim μ < 1`.

Let `μ` be the self-conformal measure of `φ` and `p`, exact dimensional with dimension `d < 1`.
For `k ≥ 1` and `0 < ε < 1` there are `ρ > 0` and `N₀` such that for `n ≥ N₀` the following
holds. If `ν` is a probability measure on `𝒫_k` such that `ν`-a.e. `q` has `‖q‖₂ ≤ ε⁻¹` and
`|q'(x)| ≥ ε` on `I`, if `H(ν, 𝒟_n) / n ≥ ε`, and if `ψ : I → I` is differentiable with
`ε ≤ |ψ'| ≤ ε⁻¹` on `I`, then `H(ν.(ψμ), 𝒟_n) / n ≥ d + ρ`.

The map `ψ` is a map `ℝ → ℝ` with `ψ(I) ⊆ I`; the hypotheses on its derivative only concern
`deriv ψ x` for `x ∈ I`. Since `|deriv ψ x| ≥ ε > 0`, they force `ψ` to be differentiable at each
point of `I`. Continuity of `ψ'`, part of Rapaport's `ψ ∈ C¹(I, I)`, is not assumed. -/
def EntropyIncreasePoly {N : ℕ} (φ : Fin N → ℝ → ℝ) (p : Fin N → ℝ)
    (hp : AnalyticESC.IsProbVec p) : Prop :=
  ∀ d : ℝ, FractalGeometry.IsExactDim (selfConformal φ p hp) d → d < 1 →
  ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ ρ : ℝ, 0 < ρ ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
  ∀ ν : Measure (Poly k), IsProbabilityMeasure ν →
    (∀ᵐ q ∂ν, ‖q‖ ≤ ε⁻¹ ∧ ∀ x ∈ AnalyticESC.I, ε ≤ |Poly.derivEval q x|) →
    ε ≤ dyadicEntropyVec ν n / n →
  ∀ ψ : ℝ → ℝ, Set.MapsTo ψ AnalyticESC.I AnalyticESC.I →
    (∀ x ∈ AnalyticESC.I, HasDerivWithinAt ψ (deriv ψ x) AnalyticESC.I x) →
    (∀ x ∈ AnalyticESC.I, ε ≤ |deriv ψ x| ∧ |deriv ψ x| ≤ ε⁻¹) →
    d + ρ ≤ dyadicEntropy (act ν ((selfConformal φ p hp).map ψ)) n / n

end FractalGeometry.Rapaport.Analytic
