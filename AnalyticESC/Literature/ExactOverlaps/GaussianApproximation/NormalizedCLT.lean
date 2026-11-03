module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.GaussianCentering
public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.SteinRegularity
public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.SteinSum

set_option maxSynthPendingDepth 3

/-!
# Quantitative Gaussian approximation of normalized independent sums

The constant below is absolute. The summands may have different distributions
and zero individual variance. The actual total second moment is normalized
to one; the error is the sum of the actual third absolute moments.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.NormalizedCLT`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace ExactOverlaps.GaussianApproximation

def gaussianApproximationConstant : ℝ := 2 * (2 * steinGlobalBound gaussianFirstMoment + 1)

lemma gaussianApproximationConstant_pos : 0 < gaussianApproximationConstant := by
  have := steinGlobalBound_nonneg gaussianFirstMoment_nonneg
  unfold gaussianApproximationConstant
  positivity

theorem abs_normalized_sum_test_error_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 3 μ) (hind : iIndepFun X μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hnorm : (∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) = 1)
    {h : ℝ → ℝ} (hh : h ∈ unitTests) :
    |(∫ ω, h (∑ i, X i ω) ∂μ) - ∫ x, h x ∂(standardGaussian : Measure ℝ)| ≤
      gaussianApproximationConstant * ∑ i, ∫ ω, |X i ω| ^ 3 ∂μ := by
  let H := centeredGaussianTest h
  let g := steinSolution H
  let g' := fun x ↦ x * g x + H x
  let S := fun ω ↦ ∑ i, X i ω
  have hH : LipschitzWith 1 H := lipschitz_centeredGaussianTest hh.1
  have hb : ∀ x, |H x| ≤ |x| + gaussianFirstMoment := abs_centeredGaussianTest_le hh
  have hz : (∫ x, H x * gaussianWeight x) = 0 :=
    integral_centeredGaussianTest_weight_eq_zero hh
  have hHi := integrable_mul_gaussianWeight hH.continuous hb
  have hd : ∀ x, HasDerivAt g (g' x) x := hasDerivAt_steinSolution hH.continuous hHi
  have hg : ∀ x, |g x| ≤ steinGlobalBound gaussianFirstMoment :=
    abs_steinSolution_le hH gaussianFirstMoment_nonneg hb hz
  have hg' : ∀ x, |g' x| ≤ steinGlobalBound gaussianFirstMoment :=
    abs_stein_derivative_le hH gaussianFirstMoment_nonneg hb hz
  have hLip := lipschitz_stein_derivative hH gaussianFirstMoment_nonneg hb hz
  have hS : Integrable S μ := integrable_finsetSum _ (fun i _ ↦ integrable_of_memLp_three (hX i))
  have hgmeas : Measurable g :=
    (continuous_iff_continuousAt.mpr (fun x ↦ (hd x).continuousAt)).measurable
  have hi1 : Integrable (fun ω ↦ g' (S ω)) μ :=
    integrable_bounded_lipschitz_comp hS.aemeasurable hLip hg'
  have hi2 : Integrable (fun ω ↦ S ω * g (S ω)) μ :=
    hS.mul_bdd (hgmeas.comp_aemeasurable hS.aemeasurable).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs] using hg (S ω)))
  have htest : Integrable (fun ω ↦ h (S ω)) μ := by
    apply hS.mono (hh.1.continuous.measurable.comp_aemeasurable hS.aemeasurable).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω ↦ by
      change ‖h (S ω)‖ ≤ ‖S ω‖
      simpa only [Real.norm_eq_abs] using abs_le_of_mem_unitTests hh (S ω))
  have he : (∫ ω, g' (S ω) ∂μ) - (∫ ω, S ω * g (S ω) ∂μ) =
      (∫ ω, h (S ω) ∂μ) - ∫ x, h x ∂(standardGaussian : Measure ℝ) := by
    rw [← integral_sub hi1 hi2]
    calc
      _ = ∫ ω, h (S ω) - (∫ x, h x ∂(standardGaussian : Measure ℝ)) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω ↦ by dsimp [g', H, centeredGaussianTest]; ring)
      _ = _ := by rw [integral_sub htest (integrable_const _)]; simp
  have hstein := abs_normalized_sum_stein_error_le X hX hind hmean hnorm hd hLip hg hg'
  change |(∫ ω, g' (S ω) ∂μ) - (∫ ω, S ω * g (S ω) ∂μ)| ≤
    gaussianApproximationConstant * ∑ i, ∫ ω, |X i ω| ^ 3 ∂μ at hstein
  rwa [he] at hstein

end ExactOverlaps.GaussianApproximation
