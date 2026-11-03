module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.GaussianCDF
public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.WassersteinTests
public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.GaussianScaling

set_option maxSynthPendingDepth 3

/-!
# Translation of Gaussian Wasserstein comparisons

Translation preserves the genuine dual distance up to the stated comparison.
The translated centered Gaussian is exactly the Gaussian with that mean.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.WassersteinTranslation`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ExactOverlaps.Entropy

open GaussianApproximation

lemma integrable_id_map_add (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ)) (b : ℝ) :
    Integrable (fun x : ℝ ↦ x) (μ.map (fun x ↦ x + b) : Measure ℝ) := by
  rw [ProbabilityMeasure.toMeasure_map]
  exact (integrable_map_measure measurable_id.aestronglyMeasurable
    (measurable_id.add_const b).aemeasurable).mpr (hμ.add (integrable_const b))

lemma wasserstein1_map_add_le (μ ν : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    (hν : Integrable (fun x : ℝ ↦ x) (ν : Measure ℝ)) (b : ℝ) :
    wasserstein1 (μ.map (fun x ↦ x + b)) (ν.map (fun x ↦ x + b))
      (integrable_id_map_add μ hμ b) (integrable_id_map_add ν hν b) ≤
        wasserstein1 μ ν hμ hν := by
  apply wasserstein1_le
  intro f hf
  rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
    integral_map (φ := fun x : ℝ ↦ x + b) (by fun_prop) hf.1.continuous.aestronglyMeasurable,
    integral_map (φ := fun x : ℝ ↦ x + b) (by fun_prop) hf.1.continuous.aestronglyMeasurable]
  apply abs_integral_sub_le_wasserstein1_of_lipschitz
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, add_sub_add_right_eq_sub] using hf.1.dist_le_mul (x + b) (y + b)

lemma gaussianProbability_map_add (a b : ℝ) (v : ℝ≥0) :
    (gaussianProbability a v).map (fun x ↦ x + b) = gaussianProbability (a + b) v := by
  apply ProbabilityMeasure.toMeasure_injective
  exact gaussianReal_map_add_const b

lemma centeredGaussian_map_add (b : ℝ) (v : ℝ≥0) :
    (centeredGaussian v).map (fun x ↦ x + b) = gaussianProbability b v := by
  apply ProbabilityMeasure.toMeasure_injective
  change (gaussianReal 0 v).map (fun x ↦ x + b) = gaussianReal b v
  simpa only [zero_add] using (gaussianReal_map_add_const (μ := 0) (v := v) b)

lemma map_center_add (μ : ProbabilityMeasure ℝ) (b : ℝ) :
    (μ.map (fun x ↦ x - b)).map (fun x ↦ x + b) = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((μ : Measure ℝ).map (fun x ↦ x - b)).map (fun x ↦ x + b) = _
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun x : ℝ ↦ x + b) ∘ (fun x ↦ x - b) = id := by
    funext x
    simp only [Function.comp_def, sub_add_cancel, id_eq]
  rw [he, Measure.map_id]

lemma wasserstein1_le_centered_comparison (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ)) (b : ℝ) (v : ℝ≥0)
    (hc : Integrable (fun x : ℝ ↦ x) (μ.map (fun x ↦ x - b) : Measure ℝ)) :
    wasserstein1 μ (gaussianProbability b v) hμ (gaussianProbability_integrable_id b v) ≤
      wasserstein1 (μ.map (fun x ↦ x - b)) (centeredGaussian v) hc
        (integrable_id_centeredGaussian v) := by
  have h := wasserstein1_map_add_le (μ.map (fun x ↦ x - b)) (centeredGaussian v) hc
    (integrable_id_centeredGaussian v) b
  unfold wasserstein1 at h ⊢
  rw [map_center_add, centeredGaussian_map_add] at h
  exact h

end ExactOverlaps.Entropy
