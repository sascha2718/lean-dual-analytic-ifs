module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Tactic

set_option maxSynthPendingDepth 3

/-!
# Moments for the quantitative Gaussian approximation

The third-moment condition supplies every lower moment used in the proof.
For centered bounded summands, the third absolute moment is at most the
support radius times the actual variance, including zero-variance summands.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.Moments`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ExactOverlaps.GaussianApproximation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma integrable_of_memLp_three [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 3 μ) :
    Integrable X μ :=
  (memLp_one_iff_integrable).mp (hX.mono_exponent (by norm_num))

lemma integrable_sq_of_memLp_three [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 3 μ) :
    Integrable (fun ω ↦ (X ω) ^ 2) μ := by
  have h2 : MemLp X (2 : ℕ) μ := hX.mono_exponent (by norm_num)
  simpa only [Real.norm_eq_abs, sq_abs] using h2.integrable_norm_pow'

lemma integrable_abs_cube_of_memLp_three [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 3 μ) : Integrable (fun ω ↦ |X ω| ^ 3) μ := by
  have h3 : MemLp X (3 : ℕ) μ := hX
  simpa only [Real.norm_eq_abs] using h3.integrable_norm_pow'

lemma abs_cube_le_radius_mul_sq {x R : ℝ} (hx : |x| ≤ R) : |x| ^ 3 ≤ R * x ^ 2 := by
  have h := mul_le_mul_of_nonneg_right hx (sq_nonneg x)
  have he : |x| ^ 3 = |x| * x ^ 2 := by rw [pow_succ, sq_abs]; ring
  rwa [he]

lemma thirdMoment_le_radius_mul_secondMoment [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hX : AEMeasurable X μ) {R : ℝ}
    (hR : ∀ᵐ ω ∂μ, |X ω| ≤ R) :
    (∫ ω, |X ω| ^ 3 ∂μ) ≤ R * ∫ ω, (X ω) ^ 2 ∂μ := by
  have h3 : MemLp X 3 μ := MemLp.of_bound hX.aestronglyMeasurable R
    (by simpa only [Real.norm_eq_abs] using hR)
  have h := integral_mono_ae (integrable_abs_cube_of_memLp_three h3)
    ((integrable_sq_of_memLp_three h3).const_mul R)
    (hR.mono (fun _ hω ↦ abs_cube_le_radius_mul_sq hω))
  simpa only [integral_const_mul] using h

lemma thirdMoment_le_radius_mul_variance [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (hmean : (∫ ω, X ω ∂μ) = 0) {R : ℝ}
    (hR : ∀ᵐ ω ∂μ, |X ω| ≤ R) :
    (∫ ω, |X ω| ^ 3 ∂μ) ≤ R * variance X μ := by
  rw [variance_eq_integral hX, hmean]
  simpa only [sub_zero] using thirdMoment_le_radius_mul_secondMoment hX hR

lemma sum_thirdMoment_le_radius_mul_totalVariance [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ)
    (hX : ∀ i, AEMeasurable (X i) μ) (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0) {R : ℝ}
    (hR : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ R) :
    (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) ≤ R * ∑ i, variance (X i) μ := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ ↦ thirdMoment_le_radius_mul_variance (hX i) (hmean i) (hR i))

end ExactOverlaps.GaussianApproximation
