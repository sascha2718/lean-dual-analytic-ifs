module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.SteinPositiveBounds
public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.SteinReflection
public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.SteinCentralBound

set_option maxSynthPendingDepth 3

/-!
# Global bounds for the Gaussian Stein solution

The central integral bound and the two tail estimates give uniform bounds for
the solution, its derivative, and the derivative multiplied by the argument.
The constant depends only on a fixed linear-growth envelope of the test.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.SteinGlobalBounds`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace ExactOverlaps.GaussianApproximation

def steinGlobalBound (m : ℝ) : ℝ := steinCentralBound m + 3 + 2 * m

lemma steinGlobalBound_nonneg {m : ℝ} (hm : 0 ≤ m) : 0 ≤ steinGlobalBound m := by
  have := steinCentralBound_nonneg hm
  unfold steinGlobalBound
  positivity

lemma steinCentralBound_le_global {m : ℝ} (hm : 0 ≤ m) :
    steinCentralBound m ≤ steinGlobalBound m := by
  unfold steinGlobalBound
  linarith

lemma two_add_le_steinGlobalBound {m : ℝ} (hm : 0 ≤ m) : 2 + m ≤ steinGlobalBound m := by
  have := steinCentralBound_nonneg hm
  unfold steinGlobalBound
  linarith

lemma stein_negative_tail_bounds {H : ℝ → ℝ} (hH : LipschitzWith 1 H)
    {m : ℝ} (hm : 0 ≤ m) (hbound : ∀ x, |H x| ≤ |x| + m)
    (hzero : (∫ x, H x * gaussianWeight x) = 0) {x : ℝ} (hx : x ≤ -1) :
    |steinSolution H x| ≤ 2 + m ∧
      |x * (x * steinSolution H x + H x)| ≤ 2 + m := by
  have hi := integrable_mul_gaussianWeight hH.continuous hbound
  have hrbound : ∀ t, |H (-t)| ≤ |t| + m := by
    intro t
    simpa only [abs_neg] using hbound (-t)
  have hrzero : (∫ t, H (-t) * gaussianWeight t) = 0 := by
    rw [integral_reflect_mul_gaussianWeight, hzero]
  have hrsol : steinSolution (fun t ↦ H (-t)) (-x) = -steinSolution H x := by
    simpa only [neg_neg] using steinSolution_reflect hi hzero (-x)
  have hneg : 1 ≤ -x := by linarith
  have hg := abs_steinSolution_le_of_one_le (lipschitz_reflect hH) hm hrbound hrzero hneg
  rw [hrsol, abs_neg] at hg
  have hd := abs_mul_stein_derivative_le_of_one_le
    (lipschitz_reflect hH) hm hrbound hrzero hneg
  simp only [hrsol, neg_neg] at hd
  have he : (-x) * ((-x) * (-steinSolution H x) + H x) =
      -(x * (x * steinSolution H x + H x)) := by ring
  rw [he, abs_neg] at hd
  exact ⟨hg, hd⟩

lemma stein_tail_bounds {H : ℝ → ℝ} (hH : LipschitzWith 1 H)
    {m : ℝ} (hm : 0 ≤ m) (hbound : ∀ x, |H x| ≤ |x| + m)
    (hzero : (∫ x, H x * gaussianWeight x) = 0) {x : ℝ} (hx : 1 ≤ |x|) :
    |steinSolution H x| ≤ 2 + m ∧
      |x * (x * steinSolution H x + H x)| ≤ 2 + m := by
  by_cases hx0 : 0 ≤ x
  · rw [abs_of_nonneg hx0] at hx
    exact ⟨abs_steinSolution_le_of_one_le hH hm hbound hzero hx,
      abs_mul_stein_derivative_le_of_one_le hH hm hbound hzero hx⟩
  · rw [abs_of_neg (lt_of_not_ge hx0)] at hx
    exact stein_negative_tail_bounds hH hm hbound hzero (by linarith)

lemma abs_steinSolution_le {H : ℝ → ℝ} (hH : LipschitzWith 1 H)
    {m : ℝ} (hm : 0 ≤ m) (hbound : ∀ x, |H x| ≤ |x| + m)
    (hzero : (∫ x, H x * gaussianWeight x) = 0) (x : ℝ) :
    |steinSolution H x| ≤ steinGlobalBound m := by
  by_cases hx : |x| ≤ 1
  · exact (abs_steinSolution_le_central hH.continuous hm hbound hx).trans
      (steinCentralBound_le_global hm)
  · exact ((stein_tail_bounds hH hm hbound hzero (le_of_not_ge hx)).1).trans
      (two_add_le_steinGlobalBound hm)

lemma abs_stein_derivative_le_central {H : ℝ → ℝ} (hH : LipschitzWith 1 H)
    {m : ℝ} (hm : 0 ≤ m) (hbound : ∀ x, |H x| ≤ |x| + m)
    {x : ℝ} (hx : |x| ≤ 1) :
    |x * steinSolution H x + H x| ≤ steinCentralBound m + 1 + m := by
  have hg := abs_steinSolution_le_central hH.continuous hm hbound hx
  calc
    _ ≤ |x * steinSolution H x| + |H x| := abs_add_le _ _
    _ = |x| * |steinSolution H x| + |H x| := by rw [abs_mul]
    _ ≤ 1 * steinCentralBound m + (1 + m) :=
      add_le_add (mul_le_mul hx hg (abs_nonneg _) zero_le_one)
        ((hbound x).trans (by linarith))
    _ = _ := by ring

lemma abs_mul_stein_derivative_le {H : ℝ → ℝ} (hH : LipschitzWith 1 H)
    {m : ℝ} (hm : 0 ≤ m) (hbound : ∀ x, |H x| ≤ |x| + m)
    (hzero : (∫ x, H x * gaussianWeight x) = 0) (x : ℝ) :
    |x * (x * steinSolution H x + H x)| ≤ steinGlobalBound m := by
  by_cases hx : |x| ≤ 1
  · have hc := abs_stein_derivative_le_central hH hm hbound hx
    have hboundC : steinCentralBound m + 1 + m ≤ steinGlobalBound m := by
      unfold steinGlobalBound
      linarith
    rw [abs_mul]
    calc
      _ ≤ 1 * (steinCentralBound m + 1 + m) :=
        mul_le_mul hx hc (abs_nonneg _) zero_le_one
      _ ≤ steinGlobalBound m := by simpa only [one_mul] using hboundC
  · exact ((stein_tail_bounds hH hm hbound hzero (le_of_not_ge hx)).2).trans
      (two_add_le_steinGlobalBound hm)

lemma abs_stein_derivative_le {H : ℝ → ℝ} (hH : LipschitzWith 1 H)
    {m : ℝ} (hm : 0 ≤ m) (hbound : ∀ x, |H x| ≤ |x| + m)
    (hzero : (∫ x, H x * gaussianWeight x) = 0) (x : ℝ) :
    |x * steinSolution H x + H x| ≤ steinGlobalBound m := by
  by_cases hx : |x| ≤ 1
  · apply (abs_stein_derivative_le_central hH hm hbound hx).trans
    unfold steinGlobalBound
    linarith
  · have hx1 : 1 ≤ |x| := le_of_not_ge hx
    calc
      _ ≤ |x| * |x * steinSolution H x + H x| := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hx1 (abs_nonneg (x * steinSolution H x + H x))
      _ = |x * (x * steinSolution H x + H x)| := (abs_mul _ _).symm
      _ ≤ steinGlobalBound m := abs_mul_stein_derivative_le hH hm hbound hzero x

end ExactOverlaps.GaussianApproximation
