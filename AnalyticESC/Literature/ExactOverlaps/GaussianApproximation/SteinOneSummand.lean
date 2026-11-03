module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.Moments
public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.SteinTaylor
public import Mathlib.Probability.Independence.Integration

set_option maxSynthPendingDepth 3

/-!
# One independent summand in the Stein expansion

Independence and centering cancel the constant Taylor term. The linear term
is the actual second moment times the expected derivative. The remaining
error is controlled by the third absolute moment, without moment assumptions
on the independent background variable.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.SteinOneSummand`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ExactOverlaps.GaussianApproximation

lemma abs_summand_secondMoment_error_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 3 μ) (hY : AEMeasurable Y μ) (hXY : IndepFun X Y μ)
    (hmean : (∫ ω, X ω ∂μ) = 0)
    {g g' : ℝ → ℝ} {K : ℝ≥0} {A B : ℝ}
    (hd : ∀ x, HasDerivAt g (g' x) x) (hLip : LipschitzWith K g')
    (hg : ∀ x, |g x| ≤ A) (hg' : ∀ x, |g' x| ≤ B) :
    |(∫ ω, X ω * g (Y ω + X ω) ∂μ) -
      (∫ ω, (X ω) ^ 2 ∂μ) * (∫ ω, g' (Y ω) ∂μ)| ≤
      (K : ℝ) * ∫ ω, |X ω| ^ 3 ∂μ := by
  have h1 := integrable_of_memLp_three hX
  have h2 := integrable_sq_of_memLp_three hX
  have h3 := integrable_abs_cube_of_memLp_three hX
  have hgm : Measurable g :=
    (continuous_iff_continuousAt.mpr (fun x ↦ (hd x).continuousAt)).measurable
  have hpm : Measurable g' := hLip.continuous.measurable
  have hgY : AEStronglyMeasurable (fun ω ↦ g (Y ω)) μ :=
    (hgm.comp_aemeasurable hY).aestronglyMeasurable
  have hgYX : AEStronglyMeasurable (fun ω ↦ g (Y ω + X ω)) μ :=
    (hgm.comp_aemeasurable (hY.add hX.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hpY : AEStronglyMeasurable (fun ω ↦ g' (Y ω)) μ :=
    (hpm.comp_aemeasurable hY).aestronglyMeasurable
  have hi0 : Integrable (fun ω ↦ X ω * g (Y ω)) μ :=
    h1.mul_bdd hgY (Filter.Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs] using hg (Y ω)))
  have hi1 : Integrable (fun ω ↦ X ω * g (Y ω + X ω)) μ :=
    h1.mul_bdd hgYX (Filter.Eventually.of_forall (fun ω ↦ by
      simpa only [Real.norm_eq_abs] using hg (Y ω + X ω)))
  have hi2 : Integrable (fun ω ↦ (X ω) ^ 2 * g' (Y ω)) μ :=
    h2.mul_bdd hpY (Filter.Eventually.of_forall (fun ω ↦ by
      simpa only [Real.norm_eq_abs] using hg' (Y ω)))
  have he0 : (∫ ω, X ω * g (Y ω) ∂μ) = 0 := by
    have h := (hXY.comp measurable_id hgm).integral_fun_mul_eq_mul_integral
      hX.aestronglyMeasurable hgY
    simpa only [Function.comp_apply, id_eq, hmean, zero_mul] using h
  have he2 : (∫ ω, (X ω) ^ 2 * g' (Y ω) ∂μ) =
      (∫ ω, (X ω) ^ 2 ∂μ) * (∫ ω, g' (Y ω) ∂μ) := by
    exact (hXY.comp (measurable_id.pow_const 2) hpm).integral_fun_mul_eq_mul_integral
      h2.aestronglyMeasurable hpY
  let R : Ω → ℝ := fun ω ↦
    X ω * g (Y ω + X ω) - X ω * g (Y ω) - (X ω) ^ 2 * g' (Y ω)
  have hiR : Integrable R μ := (hi1.sub hi0).sub hi2
  have hR (ω : Ω) : |R ω| ≤ (K : ℝ) * |X ω| ^ 3 := by
    have h := mul_le_mul_of_nonneg_left
      (abs_linear_remainder_le hd hLip (Y ω) (X ω)) (abs_nonneg (X ω))
    calc
      |R ω| = |X ω| * |g (Y ω + X ω) - g (Y ω) - X ω * g' (Y ω)| := by
        rw [← abs_mul]
        congr 1
        dsimp [R]
        ring
      _ ≤ |X ω| * ((K : ℝ) * (X ω) ^ 2) := h
      _ = (K : ℝ) * |X ω| ^ 3 := by rw [← sq_abs (X ω)]; ring
  have hbound : |∫ ω, R ω ∂μ| ≤ (K : ℝ) * ∫ ω, |X ω| ^ 3 ∂μ := by
    calc
      _ ≤ ∫ ω, |R ω| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (K : ℝ) * |X ω| ^ 3 ∂μ := integral_mono hiR.abs (h3.const_mul K) hR
      _ = _ := integral_const_mul _ _
  have heR : (∫ ω, R ω ∂μ) = (∫ ω, X ω * g (Y ω + X ω) ∂μ) -
      (∫ ω, (X ω) ^ 2 ∂μ) * (∫ ω, g' (Y ω) ∂μ) := by
    have hi10 : Integrable (fun ω ↦ X ω * g (Y ω + X ω) - X ω * g (Y ω)) μ :=
      hi1.sub hi0
    dsimp [R]
    rw [integral_sub hi10 hi2, integral_sub hi1 hi0, he0, he2, sub_zero]
  rwa [heR] at hbound

lemma abs_summand_variance_error_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 3 μ) (hY : AEMeasurable Y μ) (hXY : IndepFun X Y μ)
    (hmean : (∫ ω, X ω ∂μ) = 0)
    {g g' : ℝ → ℝ} {K : ℝ≥0} {A B : ℝ}
    (hd : ∀ x, HasDerivAt g (g' x) x) (hLip : LipschitzWith K g')
    (hg : ∀ x, |g x| ≤ A) (hg' : ∀ x, |g' x| ≤ B) :
    |(∫ ω, X ω * g (Y ω + X ω) ∂μ) -
      variance X μ * (∫ ω, g' (Y ω) ∂μ)| ≤ (K : ℝ) * ∫ ω, |X ω| ^ 3 ∂μ := by
  rw [variance_eq_integral hX.aestronglyMeasurable.aemeasurable, hmean]
  simpa only [sub_zero] using abs_summand_secondMoment_error_le hX hY hXY hmean hd hLip hg hg'

end ExactOverlaps.GaussianApproximation
