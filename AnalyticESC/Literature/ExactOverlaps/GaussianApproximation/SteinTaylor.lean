module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic

set_option maxSynthPendingDepth 3

/-!
# A quadratic remainder from a Lipschitz derivative

This estimate is valid for both signs of the increment, without a second
derivative assumption. It is the deterministic remainder used in the
independent-summand Stein expansion.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.SteinTaylor`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open Set
open scoped NNReal

namespace ExactOverlaps.GaussianApproximation

lemma abs_linear_remainder_le {g g' : ℝ → ℝ} {K : ℝ≥0}
    (hd : ∀ x, HasDerivAt g (g' x) x) (hLip : LipschitzWith K g') (x y : ℝ) :
    |g (x + y) - g x - y * g' x| ≤ (K : ℝ) * y ^ 2 := by
  let f : ℝ → ℝ := fun t ↦ g (x + t * y) - g x - t * y * g' x
  let f' : ℝ → ℝ := fun t ↦ y * (g' (x + t * y) - g' x)
  have hf (t : ℝ) : HasDerivAt f (f' t) t := by
    have h := ((hd (x + t * y)).comp t
      (((hasDerivAt_id t).mul_const y).const_add x)).sub_const (g x)
    have h' := h.sub (((hasDerivAt_id t).mul_const y).mul_const (g' x))
    change HasDerivAt f (g' (x + t * y) * (1 * y) - 1 * y * g' x) t at h'
    convert h' using 1
    dsimp [f']
    ring
  have hbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : ‖f' t‖ ≤ (K : ℝ) * y ^ 2 := by
    have h := hLip.dist_le_mul (x + t * y) x
    simp only [Real.dist_eq, add_sub_cancel_left, abs_mul, abs_of_nonneg ht.1] at h
    have hty : t * |y| ≤ |y| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2.le (abs_nonneg y)
    have h1 : |g' (x + t * y) - g' x| ≤ (K : ℝ) * |y| :=
      h.trans (mul_le_mul_of_nonneg_left hty K.coe_nonneg)
    have h2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg y)
    change |y * (g' (x + t * y) - g' x)| ≤ (K : ℝ) * y ^ 2
    rw [abs_mul]
    calc
      _ ≤ |y| * ((K : ℝ) * |y|) := h2
      _ = (K : ℝ) * y ^ 2 := by rw [mul_left_comm, ← sq, sq_abs]
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ ↦ (hf t).hasDerivWithinAt) hbound
  simpa only [f, zero_mul, one_mul, add_zero, sub_self, sub_zero, Real.norm_eq_abs] using h

end ExactOverlaps.GaussianApproximation
