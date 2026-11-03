module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.Wasserstein

set_option maxSynthPendingDepth 3

/-!
# Scalar transport of the dual Wasserstein distance

Positive dilation transports every unit Lipschitz test to a unit Lipschitz
test after division by the same factor. The actual pushforward expectations
therefore give the corresponding scaling bound on the distance.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.ScalarTransport`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped NNReal

namespace ExactOverlaps.GaussianApproximation

lemma rescaled_mem_unitTests {h : ℝ → ℝ} (hh : h ∈ unitTests) {a : ℝ} (ha : 0 < a) :
    (fun x ↦ h (a * x) / a) ∈ unitTests := by
  refine ⟨?_, by simp only [mul_zero, hh.2, zero_div]⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  rw [← sub_div, abs_div, abs_of_pos ha]
  apply (div_le_iff₀ ha).mpr
  have ht := hh.1.dist_le_mul (a * x) (a * y)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, ← mul_sub, abs_mul, abs_of_pos ha] at ht
  simpa only [mul_comm] using ht

lemma integrable_id_map_mul (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ)) (a : ℝ) :
    Integrable (fun x : ℝ ↦ x) (μ.map (fun x ↦ a * x) : Measure ℝ) := by
  rw [ProbabilityMeasure.toMeasure_map]
  exact (integrable_map_measure measurable_id.aestronglyMeasurable
    (measurable_const.mul measurable_id).aemeasurable).mpr (hμ.const_mul a)

lemma integral_map_mul_eq_rescaled (μ : ProbabilityMeasure ℝ)
    {h : ℝ → ℝ} (hh : h ∈ unitTests) {a : ℝ} (ha : 0 < a) :
    (∫ x, h x ∂(μ.map (fun x ↦ a * x) : Measure ℝ)) =
      a * ∫ x, h (a * x) / a ∂(μ : Measure ℝ) := by
  have hm : Measurable (fun x : ℝ ↦ a * x) := measurable_const.mul measurable_id
  rw [ProbabilityMeasure.toMeasure_map, integral_map
    hm.aemeasurable hh.1.continuous.aestronglyMeasurable,
    ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x ↦ by field_simp [ha.ne'])

theorem wasserstein1_map_mul_le (μ ν : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    (hν : Integrable (fun x : ℝ ↦ x) (ν : Measure ℝ)) {a : ℝ} (ha : 0 < a) :
    wasserstein1 (μ.map (fun x ↦ a * x)) (ν.map (fun x ↦ a * x))
      (integrable_id_map_mul μ hμ a) (integrable_id_map_mul ν hν a) ≤
        a * wasserstein1 μ ν hμ hν := by
  apply wasserstein1_le
  intro h hh
  rw [integral_map_mul_eq_rescaled μ hh ha, integral_map_mul_eq_rescaled ν hh ha,
    ← mul_sub, abs_mul, abs_of_pos ha]
  exact mul_le_mul_of_nonneg_left
    (abs_integral_sub_le_wasserstein1 μ ν hμ hν (rescaled_mem_unitTests hh ha)) ha.le

end ExactOverlaps.GaussianApproximation
