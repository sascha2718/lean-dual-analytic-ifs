module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.SteinTail

set_option maxSynthPendingDepth 3

/-!
# Reflection of the actual Stein solution

Reflection preserves Gaussian centering and unit Lipschitz regularity. The
solution changes sign after reflection, by its lower and upper tail formulas.
This transports positive-tail estimates without a symmetry hypothesis on the
original test function.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.SteinReflection`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace ExactOverlaps.GaussianApproximation

lemma gaussianWeight_neg (x : ℝ) : gaussianWeight (-x) = gaussianWeight x := by
  simp only [gaussianWeight, neg_sq]

lemma lipschitz_reflect {H : ℝ → ℝ} (hH : LipschitzWith 1 H) :
    LipschitzWith 1 (fun x ↦ H (-x)) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  simpa only [dist_neg_neg] using hH.dist_le_mul (-x) (-y)

lemma integrable_reflect_mul_gaussianWeight {H : ℝ → ℝ}
    (hi : Integrable (fun x ↦ H x * gaussianWeight x)) :
    Integrable (fun x ↦ H (-x) * gaussianWeight x) := by
  simpa only [gaussianWeight_neg] using hi.comp_neg

lemma integral_reflect_mul_gaussianWeight (H : ℝ → ℝ) :
    (∫ x, H (-x) * gaussianWeight x) = ∫ x, H x * gaussianWeight x := by
  have h := integral_neg_eq_self (fun x ↦ H x * gaussianWeight x) (volume : Measure ℝ)
  simpa only [gaussianWeight_neg] using h

lemma steinSolution_reflect {H : ℝ → ℝ}
    (hi : Integrable (fun x ↦ H x * gaussianWeight x))
    (hzero : (∫ x, H x * gaussianWeight x) = 0) (x : ℝ) :
    steinSolution (fun t ↦ H (-t)) x = -steinSolution H (-x) := by
  rw [steinSolution_upper_tail hi hzero (-x)]
  unfold steinSolution
  have he : (fun t ↦ H (-t) * gaussianWeight t) =
      (fun t ↦ H (-t) * gaussianWeight (-t)) := by
    funext t
    rw [gaussianWeight_neg]
  rw [he, integral_comp_neg_Iic x (fun t ↦ H t * gaussianWeight t), neg_sq]
  ring

end ExactOverlaps.GaussianApproximation
