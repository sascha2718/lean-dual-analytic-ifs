module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.SteinGlobalBounds
public import Mathlib.Analysis.Calculus.MeanValue

set_option maxSynthPendingDepth 3

/-!
# Uniform Lipschitz regularity of the Stein derivative

The product x*g has bounded derivative g+x*g'. The mean value theorem therefore
makes x*g Lipschitz, and the Stein equation gives the same property for g'.
Only Lipschitz regularity of the original test is needed.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.SteinRegularity`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace ExactOverlaps.GaussianApproximation

lemma hasDerivAt_mul_steinSolution {H : ℝ → ℝ} (hH : Continuous H)
    (hi : Integrable (fun x ↦ H x * gaussianWeight x)) (x : ℝ) :
    HasDerivAt (fun t ↦ t * steinSolution H t)
      (steinSolution H x + x * (x * steinSolution H x + H x)) x := by
  have hd := (hasDerivAt_id x).mul (hasDerivAt_steinSolution hH hi x)
  change HasDerivAt (fun t ↦ t * steinSolution H t)
    (1 * steinSolution H x + x * (x * steinSolution H x + H x)) x at hd
  simpa only [one_mul] using hd

lemma lipschitz_mul_steinSolution {H : ℝ → ℝ} (hH : LipschitzWith 1 H)
    {m : ℝ} (hm : 0 ≤ m) (hbound : ∀ x, |H x| ≤ |x| + m)
    (hzero : (∫ x, H x * gaussianWeight x) = 0) :
    LipschitzWith ⟨2 * steinGlobalBound m, mul_nonneg (by norm_num) (steinGlobalBound_nonneg hm)⟩
      (fun x ↦ x * steinSolution H x) := by
  have hi := integrable_mul_gaussianWeight hH.continuous hbound
  have hd := hasDerivAt_mul_steinSolution hH.continuous hi
  apply lipschitzWith_of_nnnorm_deriv_le (fun x ↦ (hd x).differentiableAt)
  intro x
  rw [(hd x).deriv]
  have hb : |steinSolution H x + x * (x * steinSolution H x + H x)| ≤
      2 * steinGlobalBound m := by
    calc
      _ ≤ |steinSolution H x| + |x * (x * steinSolution H x + H x)| := abs_add_le _ _
      _ ≤ steinGlobalBound m + steinGlobalBound m :=
        add_le_add (abs_steinSolution_le hH hm hbound hzero x)
          (abs_mul_stein_derivative_le hH hm hbound hzero x)
      _ = _ := by ring
  exact_mod_cast hb

lemma lipschitz_stein_derivative {H : ℝ → ℝ} (hH : LipschitzWith 1 H)
    {m : ℝ} (hm : 0 ≤ m) (hbound : ∀ x, |H x| ≤ |x| + m)
    (hzero : (∫ x, H x * gaussianWeight x) = 0) :
    LipschitzWith ⟨2 * steinGlobalBound m + 1, by
      have := steinGlobalBound_nonneg hm
      positivity⟩ (fun x ↦ x * steinSolution H x + H x) := by
  exact (lipschitz_mul_steinSolution hH hm hbound hzero).add hH

end ExactOverlaps.GaussianApproximation
