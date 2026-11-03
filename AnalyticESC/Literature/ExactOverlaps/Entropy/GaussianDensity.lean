module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Tactic

set_option maxSynthPendingDepth 3

/-!
# Uniform local variation of Gaussian densities

On a fixed interval about the mean and with variance bounded below, the
Gaussian density ratio is controlled by the distance between the points.
The mean is arbitrary, so the estimate is stable under translations of the
dyadic grid.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.GaussianDensity`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open ProbabilityTheory
open scoped NNReal

namespace ExactOverlaps.Entropy

lemma gaussianPDFReal_eq_exp_mul (b : ℝ) (v : ℝ≥0) (x y : ℝ) :
    gaussianPDFReal b v x =
      Real.exp (((y - b) ^ 2 - (x - b) ^ 2) / (2 * v)) * gaussianPDFReal b v y := by
  unfold gaussianPDFReal
  rw [mul_left_comm, ← Real.exp_add]
  congr 1
  congr 1
  ring

lemma gaussian_exponent_difference_bound (b : ℝ) (v : ℝ≥0)
    {σ R h x y : ℝ} (hσ : 0 < σ) (hv : σ ≤ (v : ℝ))
    (hx : |x - b| ≤ R) (hy : |y - b| ≤ R) (hxy : |x - y| ≤ h) :
    |((y - b) ^ 2 - (x - b) ^ 2) / (2 * v)| ≤ R * h / σ := by
  have hvpos : 0 < (v : ℝ) := hσ.trans_le hv
  have hR : 0 ≤ R := (abs_nonneg _).trans hx
  have hh : 0 ≤ h := (abs_nonneg _).trans hxy
  have h₁ : |y - x| ≤ h := by simpa only [abs_sub_comm] using hxy
  have h₂ : |(y - b) + (x - b)| ≤ 2 * R := by
    have ha := abs_add_le (y - b) (x - b)
    linarith
  have hsq : |(y - b) ^ 2 - (x - b) ^ 2| ≤ 2 * R * h := by
    rw [show (y - b) ^ 2 - (x - b) ^ 2 = (y - x) * ((y - b) + (x - b)) by ring,
      abs_mul]
    have hm := mul_le_mul h₁ h₂ (abs_nonneg _) hh
    nlinarith
  calc
    _ = |(y - b) ^ 2 - (x - b) ^ 2| / (2 * (v : ℝ)) := by
      rw [abs_div, abs_of_pos (mul_pos (by norm_num) hvpos)]
    _ ≤ (2 * R * h) / (2 * (v : ℝ)) :=
      div_le_div_of_nonneg_right hsq (by positivity)
    _ = R * h / (v : ℝ) := by ring
    _ ≤ R * h / σ := div_le_div_of_nonneg_left (mul_nonneg hR hh) hσ hv

theorem gaussianPDFReal_le_exp_mul (b : ℝ) (v : ℝ≥0)
    {σ R h x y : ℝ} (hσ : 0 < σ) (hv : σ ≤ (v : ℝ))
    (hx : |x - b| ≤ R) (hy : |y - b| ≤ R) (hxy : |x - y| ≤ h) :
    gaussianPDFReal b v x ≤ Real.exp (R * h / σ) * gaussianPDFReal b v y := by
  rw [gaussianPDFReal_eq_exp_mul b v x y]
  apply mul_le_mul_of_nonneg_right _ (gaussianPDFReal_nonneg _ _ _)
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans (gaussian_exponent_difference_bound b v hσ hv hx hy hxy)

theorem gaussianPDFReal_exp_neg_mul_le (b : ℝ) (v : ℝ≥0)
    {σ R h x y : ℝ} (hσ : 0 < σ) (hv : σ ≤ (v : ℝ))
    (hx : |x - b| ≤ R) (hy : |y - b| ≤ R) (hxy : |x - y| ≤ h) :
    Real.exp (-(R * h / σ)) * gaussianPDFReal b v y ≤ gaussianPDFReal b v x := by
  have hb := gaussianPDFReal_le_exp_mul b v hσ hv hy hx
    (by simpa only [abs_sub_comm] using hxy)
  have he := mul_le_mul_of_nonneg_left hb (Real.exp_pos (-(R * h / σ))).le
  simpa only [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] using he

end ExactOverlaps.Entropy
