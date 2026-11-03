module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.WassersteinUniformity
public import AnalyticESC.Literature.ExactOverlaps.Entropy.DyadicDilation

set_option maxSynthPendingDepth 3

/-!
# Gaussian approximation at any dyadic normalization scale

The scale parameter is an arbitrary integer. A single Gaussian approximation
tolerance gives component uniformity for the original law at the correctly
shifted level, with all entropy-deficiency losses accounted for explicitly.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.DilationUniformity`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ExactOverlaps.Entropy

theorem exists_wasserstein_uniformity_after_dilation {σ V δ : ℝ}
    (hσ : 0 < σ) (hV : 0 < V) (hδ : 0 < δ) {m : ℕ} (hm : 0 < m) :
    ∃ p : ℕ, ∃ η > 0, ∀ (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
      (s : ℤ) (b : ℝ) (v : ℝ≥0), σ ≤ (v : ℝ) → (v : ℝ) ≤ V →
      GaussianApproximation.wasserstein1 (μ.map (componentRescale s 0)) (gaussianProbability b v)
        (integrable_id_of_hasBoundedSupport _ (componentRescale_hasBoundedSupport μ hμ s 0))
        (gaussianProbability_integrable_id b v) ≤ η →
      componentEntropyLowerTailMass μ hμ (s + p) m δ < δ := by
  have he : 0 < δ ^ 2 / 4 := by positivity
  obtain ⟨p, η, hη, hp⟩ := exists_wasserstein_component_uniformity hσ hV he hm
  refine ⟨p, η, hη, ?_⟩
  intro μ hμ s b v hvσ hvV hW
  have hbad := hp (μ.map (componentRescale s 0))
    (componentRescale_hasBoundedSupport μ hμ s 0) b v hvσ hvV hW
  have hscale := component_lowerTail_dilation_le μ hμ s p hm he.le δ
  have hprod : δ * componentEntropyLowerTailMass μ hμ (s + p) m δ < δ * δ := by
    nlinarith [sq_pos_of_pos hδ]
  exact (mul_lt_mul_iff_right₀ hδ).1 hprod

end ExactOverlaps.Entropy
