module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.SteinTail

set_option maxSynthPendingDepth 3

/-!
# Uniform Stein bounds on the positive tail

The cancellation xI+J=1 gives a uniform bound for x*g', as well as for g,
on x≥1. The constants depend only on the linear-growth envelope, not on the
particular unit Lipschitz test. No derivative of that test is required.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.SteinPositiveBounds`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace ExactOverlaps.GaussianApproximation

lemma stein_derivative_tail_identity {H : ℝ → ℝ} (hH : LipschitzWith 1 H)
    (hi : Integrable (fun x ↦ H x * gaussianWeight x))
    (hzero : (∫ x, H x * gaussianWeight x) = 0) {x : ℝ} (hx : 0 < x) :
    x * steinSolution H x + H x =
      H x * (∫ u in Ioi 0, u * tailKernel x u) -
      x * (∫ u in Ioi 0, (H (x + u) - H x) * tailKernel x u) := by
  rw [steinSolution_tail_decomposition hH hi hzero hx]
  have hmoment := tailKernel_moment_identity hx
  have hJ : 1 - x * (∫ u in Ioi 0, tailKernel x u) =
      ∫ u in Ioi 0, u * tailKernel x u := by linarith
  calc
    _ = H x * (1 - x * (∫ u in Ioi 0, tailKernel x u)) -
        x * (∫ u in Ioi 0, (H (x + u) - H x) * tailKernel x u) := by ring
    _ = _ := by rw [hJ]

lemma abs_steinSolution_le_of_one_le {H : ℝ → ℝ} (hH : LipschitzWith 1 H)
    {m : ℝ} (hm : 0 ≤ m) (hbound : ∀ x, |H x| ≤ |x| + m)
    (hzero : (∫ x, H x * gaussianWeight x) = 0) {x : ℝ} (hx : 1 ≤ x) :
    |steinSolution H x| ≤ 2 + m := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hi := integrable_mul_gaussianWeight hH.continuous hbound
  have hI : 0 ≤ ∫ u in Ioi 0, tailKernel x u :=
    integral_nonneg (fun u ↦ (tailKernel_pos x u).le)
  have hHbound : |H x| ≤ x + m := by simpa only [abs_of_pos hx0] using hbound x
  have hIupper := integral_tailKernel_le hx0
  have hJupper := integral_mul_tailKernel_le hx0
  have hR := abs_integral_tail_increment_le hH hx0
  have hmx : m / x ≤ m := (div_le_iff₀ hx0).mpr (by nlinarith [mul_nonneg hm (sub_nonneg.mpr hx)])
  have hxx : 1 ≤ x ^ 2 := by nlinarith
  have hinv : 1 / x ^ 2 ≤ (1 : ℝ) := (div_le_iff₀ (sq_pos_of_pos hx0)).mpr (by nlinarith)
  rw [steinSolution_tail_decomposition hH hi hzero hx0, abs_neg]
  calc
    _ ≤ |H x * (∫ u in Ioi 0, tailKernel x u)| +
        |∫ u in Ioi 0, (H (x + u) - H x) * tailKernel x u| := abs_add_le _ _
    _ = |H x| * (∫ u in Ioi 0, tailKernel x u) +
        |∫ u in Ioi 0, (H (x + u) - H x) * tailKernel x u| := by rw [abs_mul, abs_of_nonneg hI]
    _ ≤ (x + m) * (1 / x) + 1 / x ^ 2 := by
      exact add_le_add (mul_le_mul hHbound hIupper hI (by positivity)) (hR.trans hJupper)
    _ = 1 + m / x + 1 / x ^ 2 := by field_simp
    _ ≤ 2 + m := by linarith

lemma abs_mul_stein_derivative_le_of_one_le {H : ℝ → ℝ} (hH : LipschitzWith 1 H)
    {m : ℝ} (hm : 0 ≤ m) (hbound : ∀ x, |H x| ≤ |x| + m)
    (hzero : (∫ x, H x * gaussianWeight x) = 0) {x : ℝ} (hx : 1 ≤ x) :
    |x * (x * steinSolution H x + H x)| ≤ 2 + m := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hi := integrable_mul_gaussianWeight hH.continuous hbound
  have hJ : 0 ≤ ∫ u in Ioi 0, u * tailKernel x u := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg hu.le (tailKernel_pos x u).le
  have hR := abs_integral_tail_increment_le hH hx0
  have hHbound : |H x| ≤ x + m := by simpa only [abs_of_pos hx0] using hbound x
  have hfirst : |x * steinSolution H x + H x| ≤
      (|H x| + x) * (∫ u in Ioi 0, u * tailKernel x u) := by
    rw [stein_derivative_tail_identity hH hi hzero hx0]
    calc
      _ ≤ |H x * (∫ u in Ioi 0, u * tailKernel x u)| +
          |x * (∫ u in Ioi 0, (H (x + u) - H x) * tailKernel x u)| := abs_sub _ _
      _ = |H x| * (∫ u in Ioi 0, u * tailKernel x u) +
          x * |∫ u in Ioi 0, (H (x + u) - H x) * tailKernel x u| := by
        rw [abs_mul, abs_of_nonneg hJ, abs_mul, abs_of_pos hx0]
      _ ≤ |H x| * (∫ u in Ioi 0, u * tailKernel x u) +
          x * (∫ u in Ioi 0, u * tailKernel x u) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hR hx0.le)
      _ = _ := by ring
  have hmx : m / x ≤ m := (div_le_iff₀ hx0).mpr (by nlinarith [mul_nonneg hm (sub_nonneg.mpr hx)])
  rw [abs_mul, abs_of_pos hx0]
  calc
    _ ≤ x * ((|H x| + x) * (∫ u in Ioi 0, u * tailKernel x u)) :=
      mul_le_mul_of_nonneg_left hfirst hx0.le
    _ ≤ x * ((2 * x + m) * (1 / x ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hx0.le
      exact mul_le_mul (by linarith : |H x| + x ≤ 2 * x + m)
        (integral_mul_tailKernel_le hx0) hJ (by positivity)
    _ = 2 + m / x := by field_simp
    _ ≤ 2 + m := by linarith

end ExactOverlaps.GaussianApproximation
