module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.SumApproximation

set_option maxSynthPendingDepth 3

/-!
# Gaussian approximation for bounded centered summands

The same universal constant as in the third-moment estimate gives an error
at most C times the common bound on the summands. This is the second clause
of the primary paper's Lemma 3.7, including summands of zero variance.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.BoundedSumApproximation`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace ExactOverlaps.GaussianApproximation

lemma memLp_three_of_ae_bounded {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : AEMeasurable X μ) {R : ℝ} (hR : ∀ᵐ ω ∂μ, |X ω| ≤ R) : MemLp X 3 μ :=
  MemLp.of_bound hX.aestronglyMeasurable R (by simpa only [Real.norm_eq_abs] using hR)

theorem wasserstein1_sum_le_of_bounded {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 3 μ) (hind : iIndepFun X μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0) (v : ℝ≥0) (hv : 0 < (v : ℝ))
    (hvariance : (∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) = (v : ℝ))
    (ν : ProbabilityMeasure ℝ)
    (hν : (ν : Measure ℝ) = μ.map (fun ω ↦ ∑ i, X i ω))
    {R : ℝ} (hR : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ R) :
    wasserstein1 ν (centeredGaussian v)
      (integrable_id_sum_law X hX ν hν) (integrable_id_centeredGaussian v) ≤
        gaussianApproximationConstant * R := by
  have hthird : (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) ≤ R * (v : ℝ) := by
    rw [← hvariance, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ ↦
      thirdMoment_le_radius_mul_secondMoment (hX i).aestronglyMeasurable.aemeasurable (hR i))
  calc
    _ ≤ gaussianApproximationConstant * (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) / (v : ℝ) :=
      wasserstein1_sum_le X hX hind hmean v hv hvariance ν hν
    _ ≤ gaussianApproximationConstant * (R * (v : ℝ)) / (v : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hthird gaussianApproximationConstant_pos.le) hv.le
    _ = _ := by field_simp [hv.ne']

end ExactOverlaps.GaussianApproximation
