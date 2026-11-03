module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.SteinOneSummand
public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.MomentProducts

set_option maxSynthPendingDepth 3

/-!
# Moving the derivative to the full sum

The Lipschitz derivative estimate and the moment-product inequality replace
the background derivative in the one-summand expansion by the derivative
at the full sum. The resulting error is twice the third-moment bound.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.SteinShift`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ExactOverlaps.GaussianApproximation

lemma integrable_bounded_lipschitz_comp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Y : Ω → ℝ}
    (hY : AEMeasurable Y μ) {f : ℝ → ℝ} {K : ℝ≥0} {B : ℝ}
    (hf : LipschitzWith K f) (hB : ∀ x, |f x| ≤ B) :
    Integrable (fun ω ↦ f (Y ω)) μ := by
  apply memLp_one_iff_integrable.mp
  exact MemLp.of_bound (hf.continuous.measurable.comp_aemeasurable hY).aestronglyMeasurable B
    (Filter.Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs] using hB (Y ω)))

lemma abs_integral_lipschitz_shift_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : Integrable X μ) (hY : AEMeasurable Y μ)
    {f : ℝ → ℝ} {K : ℝ≥0} {B : ℝ}
    (hf : LipschitzWith K f) (hB : ∀ x, |f x| ≤ B) :
    |(∫ ω, f (Y ω + X ω) ∂μ) - (∫ ω, f (Y ω) ∂μ)| ≤
      (K : ℝ) * ∫ ω, |X ω| ∂μ := by
  have hi1 : Integrable (fun ω ↦ f (Y ω + X ω)) μ :=
    integrable_bounded_lipschitz_comp (hY.add hX.aemeasurable) hf hB
  have hi0 := integrable_bounded_lipschitz_comp hY hf hB
  rw [← integral_sub hi1 hi0]
  calc
    _ ≤ ∫ ω, |f (Y ω + X ω) - f (Y ω)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (K : ℝ) * |X ω| ∂μ := by
      apply integral_mono (hi1.sub hi0).abs (hX.abs.const_mul K)
      intro ω
      change |f (Y ω + X ω) - f (Y ω)| ≤ (K : ℝ) * |X ω|
      simpa only [Real.dist_eq, add_sub_cancel_left] using hf.dist_le_mul (Y ω + X ω) (Y ω)
    _ = _ := integral_const_mul _ _

lemma abs_summand_stein_error_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 3 μ) (hY : AEMeasurable Y μ) (hXY : IndepFun X Y μ)
    (hmean : (∫ ω, X ω ∂μ) = 0)
    {g g' : ℝ → ℝ} {K : ℝ≥0} {A B : ℝ}
    (hd : ∀ x, HasDerivAt g (g' x) x) (hLip : LipschitzWith K g')
    (hg : ∀ x, |g x| ≤ A) (hg' : ∀ x, |g' x| ≤ B) :
    |(∫ ω, (X ω) ^ 2 ∂μ) * (∫ ω, g' (Y ω + X ω) ∂μ) -
      (∫ ω, X ω * g (Y ω + X ω) ∂μ)| ≤
      2 * (K : ℝ) * ∫ ω, |X ω| ^ 3 ∂μ := by
  let v := ∫ ω, (X ω) ^ 2 ∂μ
  have hv : 0 ≤ v := integral_nonneg (fun ω ↦ sq_nonneg (X ω))
  have hshift := abs_integral_lipschitz_shift_le
    (integrable_of_memLp_three hX) hY hLip hg'
  have hprod := firstMoment_mul_secondMoment_le_thirdMoment hX
  have hfirst : |v * (∫ ω, g' (Y ω + X ω) ∂μ) - v * (∫ ω, g' (Y ω) ∂μ)| ≤
      (K : ℝ) * ∫ ω, |X ω| ^ 3 ∂μ := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hv]
    calc
      _ ≤ v * ((K : ℝ) * ∫ ω, |X ω| ∂μ) := mul_le_mul_of_nonneg_left hshift hv
      _ = (K : ℝ) * ((∫ ω, |X ω| ∂μ) * v) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod K.coe_nonneg
  have hsecond := abs_summand_secondMoment_error_le hX hY hXY hmean hd hLip hg hg'
  rw [abs_sub_comm] at hsecond
  calc
    _ ≤ |v * (∫ ω, g' (Y ω + X ω) ∂μ) - v * (∫ ω, g' (Y ω) ∂μ)| +
        |v * (∫ ω, g' (Y ω) ∂μ) - (∫ ω, X ω * g (Y ω + X ω) ∂μ)| :=
      abs_sub_le _ _ _
    _ ≤ (K : ℝ) * (∫ ω, |X ω| ^ 3 ∂μ) + (K : ℝ) * (∫ ω, |X ω| ^ 3 ∂μ) :=
      add_le_add hfirst hsecond
    _ = _ := by ring

end ExactOverlaps.GaussianApproximation
