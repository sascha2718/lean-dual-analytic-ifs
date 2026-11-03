module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.NormalizedCLT

set_option maxSynthPendingDepth 3

/-!
# The normalized quantitative CLT in Wasserstein distance

The comparison applies to the actual pushforward law of the sum. Its first
moment is proved from the summand hypotheses, and the estimate is uniform
over the entire defining set of Lipschitz tests.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.NormalizedWasserstein`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace ExactOverlaps.GaussianApproximation

lemma integrable_id_sum_law {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 3 μ) (ν : ProbabilityMeasure ℝ)
    (hν : (ν : Measure ℝ) = μ.map (fun ω ↦ ∑ i, X i ω)) :
    Integrable (fun x : ℝ ↦ x) (ν : Measure ℝ) := by
  have hS : Integrable (fun ω ↦ ∑ i, X i ω) μ :=
    integrable_finsetSum _ (fun i _ ↦ integrable_of_memLp_three (hX i))
  rw [hν]
  exact (integrable_map_measure measurable_id.aestronglyMeasurable hS.aemeasurable).mpr hS

theorem wasserstein1_normalized_sum_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 3 μ) (hind : iIndepFun X μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hnorm : (∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) = 1)
    (ν : ProbabilityMeasure ℝ)
    (hν : (ν : Measure ℝ) = μ.map (fun ω ↦ ∑ i, X i ω)) :
    wasserstein1 ν standardGaussian (integrable_id_sum_law X hX ν hν)
      integrable_id_standardGaussian ≤
        gaussianApproximationConstant * ∑ i, ∫ ω, |X i ω| ^ 3 ∂μ := by
  have hS : Integrable (fun ω ↦ ∑ i, X i ω) μ :=
    integrable_finsetSum _ (fun i _ ↦ integrable_of_memLp_three (hX i))
  apply wasserstein1_le
  intro h hh
  have he : (∫ x, h x ∂(ν : Measure ℝ)) = ∫ ω, h (∑ i, X i ω) ∂μ := by
    rw [hν]
    exact integral_map hS.aemeasurable hh.1.continuous.aestronglyMeasurable
  rw [he]
  exact abs_normalized_sum_test_error_le X hX hind hmean hnorm hh

end ExactOverlaps.GaussianApproximation
