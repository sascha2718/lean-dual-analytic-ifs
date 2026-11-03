module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.Wasserstein
public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.SteinEquation
public import Mathlib.Probability.Distributions.Gaussian.Real

set_option maxSynthPendingDepth 3

/-!
# Centering actual Gaussian Lipschitz tests

The universal growth envelope is the first absolute moment of the standard
Gaussian. Centering with respect to that probability law is identified with
centering of the Gaussian-weighted Lebesgue integral in the Stein solution.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.GaussianCentering`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ExactOverlaps.GaussianApproximation

def standardGaussian : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩

lemma integrable_id_standardGaussian :
    Integrable (fun x : ℝ ↦ x) (standardGaussian : Measure ℝ) :=
  (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)

def gaussianFirstMoment : ℝ := ∫ x : ℝ, |x| ∂(standardGaussian : Measure ℝ)

lemma gaussianFirstMoment_nonneg : 0 ≤ gaussianFirstMoment := integral_nonneg (fun x ↦ abs_nonneg x)

def centeredGaussianTest (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  h x - ∫ t, h t ∂(standardGaussian : Measure ℝ)

lemma lipschitz_centeredGaussianTest {h : ℝ → ℝ} (hh : LipschitzWith 1 h) :
    LipschitzWith 1 (centeredGaussianTest h) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [centeredGaussianTest, dist_sub_right] using hh.dist_le_mul x y

lemma abs_centeredGaussianTest_le {h : ℝ → ℝ} (hh : h ∈ unitTests) (x : ℝ) :
    |centeredGaussianTest h x| ≤ |x| + gaussianFirstMoment := by
  exact (abs_sub _ _).trans (add_le_add (abs_le_of_mem_unitTests hh x)
    (abs_integral_unitTest_le standardGaussian integrable_id_standardGaussian hh))

lemma gaussianPDFReal_standard (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * gaussianWeight x := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, gaussianWeight]

lemma integral_standardGaussian_eq_weighted (H : ℝ → ℝ) :
    (∫ x, H x ∂(standardGaussian : Measure ℝ)) =
      (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x, H x * gaussianWeight x := by
  change (∫ x, H x ∂gaussianReal 0 1) = _
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [gaussianPDFReal_standard, smul_eq_mul]
  calc
    _ = ∫ x, (Real.sqrt (2 * Real.pi))⁻¹ * (H x * gaussianWeight x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ by ring)
    _ = _ := integral_const_mul _ _

lemma integral_centeredGaussianTest_eq_zero {h : ℝ → ℝ} (hh : h ∈ unitTests) :
    (∫ x, centeredGaussianTest h x ∂(standardGaussian : Measure ℝ)) = 0 := by
  unfold centeredGaussianTest
  rw [integral_sub (integrable_unitTest standardGaussian integrable_id_standardGaussian hh)
    (integrable_const _)]
  simp

lemma integral_centeredGaussianTest_weight_eq_zero {h : ℝ → ℝ} (hh : h ∈ unitTests) :
    (∫ x, centeredGaussianTest h x * gaussianWeight x) = 0 := by
  have hz := integral_centeredGaussianTest_eq_zero hh
  rw [integral_standardGaussian_eq_weighted] at hz
  have hc : (Real.sqrt (2 * Real.pi))⁻¹ ≠ 0 := by positivity
  exact (mul_eq_zero.mp hz).resolve_left hc

end ExactOverlaps.GaussianApproximation
