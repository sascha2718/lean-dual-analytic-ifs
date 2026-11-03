module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

set_option maxSynthPendingDepth 3

/-!
# The actual integral solution of the Gaussian Stein equation

The solution is defined by an ordinary convergent Gaussian-weighted integral.
Its derivative and upper-tail representation are proved by the fundamental
theorem of calculus and centering. Global Stein factor estimates are proved
separately; they are not built into this definition.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.SteinEquation`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set

namespace ExactOverlaps.GaussianApproximation

def gaussianWeight (x : ℝ) : ℝ := Real.exp (-x ^ 2 / 2)

lemma gaussianWeight_pos (x : ℝ) : 0 < gaussianWeight x := Real.exp_pos _

lemma continuous_gaussianWeight : Continuous gaussianWeight := by
  unfold gaussianWeight
  fun_prop

lemma integrable_gaussianWeight : Integrable gaussianWeight := by
  unfold gaussianWeight
  convert integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num) using 1
  funext x
  congr 1
  ring

lemma integrable_abs_mul_gaussianWeight : Integrable (fun x : ℝ ↦ |x| * gaussianWeight x) := by
  have h := (integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ))
    (s := 1) (by norm_num) (by norm_num)).abs
  simpa only [Real.rpow_one, abs_mul, abs_of_pos (Real.exp_pos _), gaussianWeight,
    show ∀ x : ℝ, -x ^ 2 / 2 = -(1 / 2) * x ^ 2 by intro x; ring] using h

lemma integrable_gaussian_envelope (m : ℝ) :
    Integrable (fun x : ℝ ↦ (|x| + m) * gaussianWeight x) := by
  have h : Integrable (fun x : ℝ ↦ |x| * gaussianWeight x + m * gaussianWeight x) :=
    integrable_abs_mul_gaussianWeight.add (integrable_gaussianWeight.const_mul m)
  simpa only [add_mul] using h

lemma integrable_mul_gaussianWeight {H : ℝ → ℝ} (hH : Continuous H) {m : ℝ}
    (hbound : ∀ x, |H x| ≤ |x| + m) : Integrable (fun x ↦ H x * gaussianWeight x) := by
  apply (integrable_gaussian_envelope m).mono'
  · exact (hH.mul continuous_gaussianWeight).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gaussianWeight_pos x)]
      exact mul_le_mul_of_nonneg_right (hbound x) (gaussianWeight_pos x).le)

def steinSolution (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (x ^ 2 / 2) * ∫ t in Iic x, H t * gaussianWeight t

lemma gaussianWeight_cancel (x : ℝ) : Real.exp (x ^ 2 / 2) * gaussianWeight x = 1 := by
  rw [gaussianWeight, ← Real.exp_add]
  have he : x ^ 2 / 2 + -x ^ 2 / 2 = 0 := by ring
  rw [he, Real.exp_zero]

lemma hasDerivAt_integral_Iic_of_continuous {F : ℝ → ℝ} (hF : Continuous F)
    (hi : Integrable F) (x : ℝ) :
    HasDerivAt (fun y ↦ ∫ t in Iic y, F t) (F x) x := by
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hF.intervalIntegrable 0 x) (hF.stronglyMeasurable.stronglyMeasurableAtFilter)
    hF.continuousAt).const_add (∫ t in Iic 0, F t)
  have he : (fun y ↦ (∫ t in Iic 0, F t) + ∫ t in (0 : ℝ)..y, F t) =
      (fun y ↦ ∫ t in Iic y, F t) := by
    funext y
    have h := intervalIntegral.integral_Iic_sub_Iic
      (a := 0) (b := y) hi.integrableOn hi.integrableOn
    linarith
  rwa [he] at hd

lemma hasDerivAt_steinSolution {H : ℝ → ℝ} (hH : Continuous H)
    (hi : Integrable (fun x ↦ H x * gaussianWeight x)) (x : ℝ) :
    HasDerivAt (steinSolution H) (x * steinSolution H x + H x) x := by
  have he : HasDerivAt (fun x : ℝ ↦ Real.exp (x ^ 2 / 2))
      (x * Real.exp (x ^ 2 / 2)) x := by
    have h := (((hasDerivAt_id x).pow 2).div_const 2).exp
    change HasDerivAt (fun x : ℝ ↦ Real.exp (x ^ 2 / 2))
      (Real.exp (x ^ 2 / 2) * ((2 : ℝ) * x ^ (2 - 1) * 1 / 2)) x at h
    convert h using 1
    norm_num
    ring
  have h := he.mul (hasDerivAt_integral_Iic_of_continuous
    (hH.mul continuous_gaussianWeight) hi x)
  change HasDerivAt (steinSolution H)
    (x * Real.exp (x ^ 2 / 2) * (∫ t in Iic x, H t * gaussianWeight t) +
      Real.exp (x ^ 2 / 2) * (H x * gaussianWeight x)) x at h
  convert h using 1
  dsimp only [steinSolution]
  have hc := gaussianWeight_cancel x
  have hcancel : Real.exp (x ^ 2 / 2) * (H x * gaussianWeight x) = H x := by
    calc
      _ = H x * (Real.exp (x ^ 2 / 2) * gaussianWeight x) := by ring
      _ = _ := by rw [hc, mul_one]
  rw [hcancel]
  ring

lemma steinSolution_upper_tail {H : ℝ → ℝ}
    (hi : Integrable (fun x ↦ H x * gaussianWeight x))
    (hzero : (∫ x, H x * gaussianWeight x) = 0) (x : ℝ) :
    steinSolution H x = -Real.exp (x ^ 2 / 2) * ∫ t in Ioi x, H t * gaussianWeight t := by
  have h := integral_add_compl (s := Iic x) measurableSet_Iic hi
  rw [compl_Iic, hzero] at h
  have he : (∫ t in Iic x, H t * gaussianWeight t) =
      -(∫ t in Ioi x, H t * gaussianWeight t) := by linarith
  dsimp only [steinSolution]
  rw [he]
  ring

end ExactOverlaps.GaussianApproximation
