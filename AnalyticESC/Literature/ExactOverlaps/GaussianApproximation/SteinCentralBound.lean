module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.SteinEquation

set_option maxSynthPendingDepth 3

/-!
# A uniform central bound for the Stein solution

On the unit interval about zero, the integral solution is controlled by one
fixed Gaussian envelope. Its actual integrability and nonnegativity are
proved, so this bound is independent of the particular test function.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.SteinCentralBound`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set

namespace ExactOverlaps.GaussianApproximation

def steinEnvelopeIntegral (m : ℝ) : ℝ := ∫ t : ℝ, (|t| + m) * gaussianWeight t

def steinCentralBound (m : ℝ) : ℝ := Real.exp (1 / 2) * steinEnvelopeIntegral m

lemma steinEnvelopeIntegral_nonneg {m : ℝ} (hm : 0 ≤ m) : 0 ≤ steinEnvelopeIntegral m :=
  integral_nonneg (fun t ↦ mul_nonneg (add_nonneg (abs_nonneg t) hm) (gaussianWeight_pos t).le)

lemma steinCentralBound_nonneg {m : ℝ} (hm : 0 ≤ m) : 0 ≤ steinCentralBound m :=
  mul_nonneg (Real.exp_pos _).le (steinEnvelopeIntegral_nonneg hm)

lemma abs_integral_Iic_gaussian_le_envelope {H : ℝ → ℝ} (hH : Continuous H)
    {m : ℝ} (hm : 0 ≤ m) (hbound : ∀ x, |H x| ≤ |x| + m) (x : ℝ) :
    |∫ t in Iic x, H t * gaussianWeight t| ≤ steinEnvelopeIntegral m := by
  have hi := integrable_mul_gaussianWeight hH hbound
  calc
    _ ≤ ∫ t in Iic x, |H t * gaussianWeight t| := abs_integral_le_integral_abs
    _ ≤ ∫ t in Iic x, (|t| + m) * gaussianWeight t := by
      apply integral_mono hi.abs.integrableOn (integrable_gaussian_envelope m).integrableOn
      intro t
      change |H t * gaussianWeight t| ≤ (|t| + m) * gaussianWeight t
      rw [abs_mul, abs_of_pos (gaussianWeight_pos t)]
      exact mul_le_mul_of_nonneg_right (hbound t) (gaussianWeight_pos t).le
    _ ≤ steinEnvelopeIntegral m := setIntegral_le_integral (integrable_gaussian_envelope m)
      (Filter.Eventually.of_forall (fun t ↦
        mul_nonneg (add_nonneg (abs_nonneg t) hm) (gaussianWeight_pos t).le))

lemma abs_steinSolution_le_central {H : ℝ → ℝ} (hH : Continuous H)
    {m : ℝ} (hm : 0 ≤ m) (hbound : ∀ x, |H x| ≤ |x| + m)
    {x : ℝ} (hx : |x| ≤ 1) : |steinSolution H x| ≤ steinCentralBound m := by
  have hx2 : x ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg x) zero_le_one).mpr hx
  have he : Real.exp (x ^ 2 / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith)
  rw [steinSolution, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul he (abs_integral_Iic_gaussian_le_envelope hH hm hbound x)
    (abs_nonneg _) (Real.exp_pos _).le

end ExactOverlaps.GaussianApproximation
