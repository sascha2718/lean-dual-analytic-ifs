module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.MillsKernel
public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.SteinEquation
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

set_option maxSynthPendingDepth 3

/-!
# Tail representation of the Gaussian Stein solution

Translation of the genuine upper-tail integral exposes the shifted Gaussian
kernel. The Lipschitz increment has an integrable first-moment majorant.
These formulas retain the cancellation needed for a uniform derivative bound.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.SteinTail`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace ExactOverlaps.GaussianApproximation

lemma integral_Ioi_add_left (F : ℝ → ℝ) (x : ℝ) :
    (∫ u in Ioi (0 : ℝ), F (x + u)) = ∫ t in Ioi x, F t := by
  have h := (measurePreserving_add_left (volume : Measure ℝ) x).setIntegral_preimage_emb
    (Homeomorph.addLeft x).measurableEmbedding F (Ioi x)
  have he : (fun u : ℝ ↦ x + u) ⁻¹' Ioi x = Ioi 0 := by
    ext u
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro h <;> linarith
  rwa [he] at h

lemma exp_mul_gaussianWeight_add (x u : ℝ) :
    Real.exp (x ^ 2 / 2) * gaussianWeight (x + u) = tailKernel x u := by
  rw [gaussianWeight, ← Real.exp_add]
  unfold tailKernel
  congr 1
  ring

lemma steinSolution_eq_tailKernel {H : ℝ → ℝ}
    (hi : Integrable (fun x ↦ H x * gaussianWeight x))
    (hzero : (∫ x, H x * gaussianWeight x) = 0) (x : ℝ) :
    steinSolution H x = -(∫ u in Ioi 0, H (x + u) * tailKernel x u) := by
  rw [steinSolution_upper_tail hi hzero x,
    ← integral_Ioi_add_left (fun t ↦ H t * gaussianWeight t) x, neg_mul,
    ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u ↦ by
    change Real.exp (x ^ 2 / 2) * (H (x + u) * gaussianWeight (x + u)) =
      H (x + u) * tailKernel x u
    rw [mul_left_comm, exp_mul_gaussianWeight_add])

lemma abs_lipschitz_increment_le {H : ℝ → ℝ} (hH : LipschitzWith 1 H)
    (x : ℝ) {u : ℝ} (hu : 0 ≤ u) : |H (x + u) - H x| ≤ u := by
  simpa only [Real.dist_eq, add_sub_cancel_left, NNReal.coe_one, one_mul, abs_of_nonneg hu]
    using hH.dist_le_mul (x + u) x

lemma integrableOn_tail_increment {H : ℝ → ℝ} (hH : LipschitzWith 1 H)
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u ↦ (H (x + u) - H x) * tailKernel x u) (Ioi 0) := by
  have hc : Continuous H := hH.continuous
  apply (integrableOn_mul_tailKernel hx).mono'
  · exact (by unfold tailKernel; fun_prop :
      Continuous (fun u ↦ (H (x + u) - H x) * tailKernel x u)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (tailKernel_pos x u)]
    exact mul_le_mul_of_nonneg_right (abs_lipschitz_increment_le hH x hu.le)
      (tailKernel_pos x u).le

lemma abs_integral_tail_increment_le {H : ℝ → ℝ} (hH : LipschitzWith 1 H)
    {x : ℝ} (hx : 0 < x) :
    |∫ u in Ioi 0, (H (x + u) - H x) * tailKernel x u| ≤
      ∫ u in Ioi 0, u * tailKernel x u := by
  apply abs_integral_le_integral_abs.trans
  apply integral_mono_ae (integrableOn_tail_increment hH hx).abs (integrableOn_mul_tailKernel hx)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [abs_mul, abs_of_pos (tailKernel_pos x u)]
  exact mul_le_mul_of_nonneg_right (abs_lipschitz_increment_le hH x hu.le)
    (tailKernel_pos x u).le

lemma steinSolution_tail_decomposition {H : ℝ → ℝ} (hH : LipschitzWith 1 H)
    (hi : Integrable (fun x ↦ H x * gaussianWeight x))
    (hzero : (∫ x, H x * gaussianWeight x) = 0) {x : ℝ} (hx : 0 < x) :
    steinSolution H x = -(H x * (∫ u in Ioi 0, tailKernel x u) +
      ∫ u in Ioi 0, (H (x + u) - H x) * tailKernel x u) := by
  rw [steinSolution_eq_tailKernel hi hzero]
  have he : (fun u ↦ H (x + u) * tailKernel x u) =
      (fun u ↦ H x * tailKernel x u + (H (x + u) - H x) * tailKernel x u) := by
    funext u
    ring
  rw [he, integral_add ((integrableOn_tailKernel hx).const_mul (H x))
    (integrableOn_tail_increment hH hx), integral_const_mul]

end ExactOverlaps.GaussianApproximation
