module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.RescaleConvolution
public import AnalyticESC.Literature.ExactOverlaps.Entropy.MixtureUniformity

set_option maxSynthPendingDepth 3

/-!
# Exact entropy increments under dyadic dilation

Multiplication by an integer power of two shifts every integer dyadic level
exactly, including negative levels. This transfers component entropy bounds
from a normalized convolution law back to its original scale.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.DyadicDilation`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.Entropy

lemma dyadicQuantize_componentRescale_zero (s i : ℤ) (x : ℝ) :
    dyadicQuantize i (componentRescale s 0 x) = dyadicQuantize (s + i) x := by
  unfold dyadicQuantize componentRescale
  simp only [Int.cast_zero, sub_zero]
  congr 1
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

lemma dyadicLaw_dilate (μ : ProbabilityMeasure ℝ) (s i : ℤ) :
    dyadicLaw (μ.map (componentRescale s 0)) i = dyadicLaw μ (s + i) := by
  apply PMF.toMeasure_injective
  rw [dyadicLaw_toMeasure, dyadicLaw_toMeasure]
  change ((μ : Measure ℝ).map (componentRescale s 0)).map (dyadicQuantize i) = _
  rw [Measure.map_map (measurable_dyadicQuantize i) (measurable_componentRescale s 0)]
  congr 1
  funext x
  exact dyadicQuantize_componentRescale_zero s i x

lemma dyadicEntropy_dilate (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (s i : ℤ) :
    dyadicEntropy (μ.map (componentRescale s 0))
      (componentRescale_hasBoundedSupport μ hμ s 0) i = dyadicEntropy μ hμ (s + i) := by
  simp only [dyadicEntropy, dyadicLaw_dilate]

lemma averageComponentEntropy_dilate (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (s i : ℤ) (m : ℕ) :
    averageComponentEntropy (μ.map (componentRescale s 0))
      (componentRescale_hasBoundedSupport μ hμ s 0) i m =
        averageComponentEntropy μ hμ (s + i) m := by
  rw [averageComponentEntropy_eq_increment, averageComponentEntropy_eq_increment,
    dyadicEntropy_dilate, dyadicEntropy_dilate, add_assoc]

theorem component_lowerTail_dilation_le (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (s i : ℤ) {m : ℕ} (hm : 0 < m)
    {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) :
    a * componentEntropyLowerTailMass μ hμ (s + i) m a ≤
      δ + componentEntropyLowerTailMass (μ.map (componentRescale s 0))
        (componentRescale_hasBoundedSupport μ hμ s 0) i m δ := by
  have h := component_entropy_deficiency_le_lowerTail (μ.map (componentRescale s 0))
    (componentRescale_hasBoundedSupport μ hμ s 0) i m hδ
  rw [averageComponentEntropy_dilate μ hμ s i m] at h
  exact (mul_componentEntropyLowerTailMass_le μ hμ (s + i) hm a).trans h

end ExactOverlaps.Entropy
