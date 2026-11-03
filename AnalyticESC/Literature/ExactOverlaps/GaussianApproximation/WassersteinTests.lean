module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.Wasserstein

set_option maxSynthPendingDepth 3

/-!
# Unnormalized Lipschitz tests

The normalization at zero in the dual distance loses no test functions.
Every unit Lipschitz function is integrable for a law with finite first moment,
and its expectation difference is bounded by the dual distance.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.WassersteinTests`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace ExactOverlaps.GaussianApproximation

lemma pin_mem_unitTests {f : ℝ → ℝ} (hf : LipschitzWith 1 f) :
    (fun x ↦ f x - f 0) ∈ unitTests := by
  refine ⟨lipschitzWith_iff_dist_le_mul.mpr (fun x y ↦ ?_), sub_self _⟩
  simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using hf.dist_le_mul x y

lemma integrable_unitLipschitz (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    {f : ℝ → ℝ} (hf : LipschitzWith 1 f) : Integrable f (μ : Measure ℝ) := by
  have h := (integrable_unitTest μ hμ (pin_mem_unitTests hf)).add
    (integrable_const (f 0))
  convert h using 1
  funext x
  exact (sub_add_cancel (f x) (f 0)).symm

lemma abs_integral_sub_le_wasserstein1_of_lipschitz (μ ν : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    (hν : Integrable (fun x : ℝ ↦ x) (ν : Measure ℝ))
    {f : ℝ → ℝ} (hf : LipschitzWith 1 f) :
    |(∫ x, f x ∂(μ : Measure ℝ)) - ∫ x, f x ∂(ν : Measure ℝ)| ≤
      wasserstein1 μ ν hμ hν := by
  have h := abs_integral_sub_le_wasserstein1 μ ν hμ hν (pin_mem_unitTests hf)
  rw [integral_sub (integrable_unitLipschitz μ hμ hf) (integrable_const _),
    integral_sub (integrable_unitLipschitz ν hν hf) (integrable_const _)] at h
  have hm : (μ : Measure ℝ).real univ = 1 := by simp
  have hn : (ν : Measure ℝ).real univ = 1 := by simp
  simpa only [integral_const, hm, hn, one_smul,
    sub_sub_sub_cancel_right] using h

end ExactOverlaps.GaussianApproximation
