module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.RescaleConvolution
public import Mathlib.Probability.Moments.Variance

set_option maxSynthPendingDepth 3

/-!
# Actual variance of real convolution and component normalization

Bounded support proves the required second moments. Convolution variance
additivity follows from the genuine product law, and affine normalization
has the exact squared scaling factor.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.RealConvolutionVariance`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ExactOverlaps.Entropy

lemma memLp_id_of_hasBoundedSupport (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (p : ℝ≥0∞) : MemLp (id : ℝ → ℝ) p (μ : Measure ℝ) := by
  obtain ⟨a, b, hab⟩ := hμ
  exact memLp_of_bounded hab measurable_id.aestronglyMeasurable p

theorem variance_realConvolution (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν) :
    variance (id : ℝ → ℝ) (realConvolution μ ν : Measure ℝ) =
      variance (id : ℝ → ℝ) (μ : Measure ℝ) + variance (id : ℝ → ℝ) (ν : Measure ℝ) := by
  change variance (id : ℝ → ℝ)
    (((μ : Measure ℝ).prod (ν : Measure ℝ)).map (fun z : ℝ × ℝ ↦ z.1 + z.2)) = _
  rw [variance_map measurable_id.aemeasurable measurable_add.aemeasurable]
  simpa only [Function.comp_def, id_eq] using
    (variance_add_prod (X := (id : ℝ → ℝ)) (Y := (id : ℝ → ℝ))
      (μ := (μ : Measure ℝ)) (ν := (ν : Measure ℝ))
      (memLp_id_of_hasBoundedSupport μ hμ 2) (memLp_id_of_hasBoundedSupport ν hν 2))

theorem variance_map_componentRescale (μ : ProbabilityMeasure ℝ) (i k : ℤ) :
    variance (id : ℝ → ℝ) (μ.map (componentRescale i k) : Measure ℝ) =
      ((2 : ℝ) ^ i) ^ 2 * variance (id : ℝ → ℝ) (μ : Measure ℝ) := by
  rw [ProbabilityMeasure.toMeasure_map,
    variance_map measurable_id.aemeasurable (measurable_componentRescale i k).aemeasurable]
  change variance (fun x : ℝ ↦ (2 : ℝ) ^ i * x - (k : ℝ)) (μ : Measure ℝ) = _
  have hmeas : AEStronglyMeasurable (fun x : ℝ ↦ (2 : ℝ) ^ i * x) (μ : Measure ℝ) :=
    (measurable_const.mul measurable_id).aestronglyMeasurable
  rw [variance_sub_const hmeas, variance_const_mul]
  rfl

noncomputable def componentVariance (μ : ProbabilityMeasure ℝ) (i : ℤ)
    (k : (dyadicLaw μ i).support) : ℝ :=
  variance (id : ℝ → ℝ) (rescaledComponent μ i k : Measure ℝ)

lemma componentVariance_nonneg (μ : ProbabilityMeasure ℝ) (i : ℤ)
    (k : (dyadicLaw μ i).support) : 0 ≤ componentVariance μ i k := variance_nonneg _ _

lemma componentVariance_le_quarter (μ : ProbabilityMeasure ℝ) (i : ℤ)
    (k : (dyadicLaw μ i).support) : componentVariance μ i k ≤ 1 / 4 := by
  have hunit : ∀ᵐ x ∂(rescaledComponent μ i k : Measure ℝ), (id : ℝ → ℝ) x ∈ Icc 0 1 := by
    filter_upwards [ae_rescaledComponent_mem_Ico μ i k] with x hx
    exact ⟨hx.1, hx.2.le⟩
  have h := variance_le_sq_of_bounded hunit measurable_id.aemeasurable
  norm_num only [sub_zero, one_div, inv_pow] at h
  exact h

end ExactOverlaps.Entropy
