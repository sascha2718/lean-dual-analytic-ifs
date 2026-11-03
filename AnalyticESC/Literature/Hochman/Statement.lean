module

public import AnalyticESC.Literature.SelfConformal.Vocabulary

@[expose] public section

/-!
# Hochman's entropy growth theorem on the line: the statement

The interface `HochmanEntropyGrowth` between the formalisation of Hochman's entropy growth
theorem and its use in Rapaport's entropy increase theorem. It is Theorem 3.2 of Rapaport,
*Dimension of self-conformal measures associated to an exponentially separated analytic IFS on
`ℝ`* (arXiv:2412.16753v2), which follows from Hochman, *On self-similar sets with overlaps and
inverse theorems for entropy* (Ann. of Math. 180 (2014), arXiv:1212.1873), Theorem 2.8, in the
scale-shifted form of Bárány–Hochman–Rapaport, *Hausdorff dimension of planar self-affine sets
and measures* (Invent. Math. 216 (2019), arXiv:1712.07353), Theorem 4.1.

Entropies are dyadic entropies in bits (`FractalGeometry.SelfConformal.dyadicEntropy`),
components are raw components (`FractalGeometry.SelfConformal.component`), and the level
probability is `FractalGeometry.SelfConformal.levelProb`.

## Main declarations

* `FractalGeometry.Hochman.HochmanEntropyGrowth`: the statement, as a `Prop`.

The proof is `FractalGeometry.Hochman.hochmanEntropyGrowth` in `FractalGeometry/Hochman/Main.lean`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Hochman.Statement`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Hochman

open MeasureTheory FractalGeometry.SelfConformal
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

end FractalGeometry.Hochman
