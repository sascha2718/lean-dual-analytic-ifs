module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Tactic

set_option maxSynthPendingDepth 3

/-!
# The shifted Gaussian tail kernel

Exponential comparison bounds the zeroth and first moments of the shifted
tail kernel. Integrating its actual derivative gives the cancellation
identity needed to control the Gaussian Stein solution far from the origin.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.MillsKernel`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace ExactOverlaps.GaussianApproximation

def tailKernel (x u : ℝ) : ℝ := Real.exp (-x * u - u ^ 2 / 2)

lemma tailKernel_pos (x u : ℝ) : 0 < tailKernel x u := Real.exp_pos _

lemma tailKernel_le_exp (x u : ℝ) : tailKernel x u ≤ Real.exp (-x * u) := by
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg u]

lemma integrableOn_exp_tail {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ ↦ Real.exp (-x * u)) (Ioi 0) :=
  integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hx) 0

lemma integral_exp_tail {x : ℝ} (hx : 0 < x) :
    (∫ u : ℝ in Ioi 0, Real.exp (-x * u)) = 1 / x := by
  simpa using integral_exp_mul_Ioi (neg_lt_zero.mpr hx) 0

lemma integrableOn_mul_exp_tail {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ ↦ u * Real.exp (-x * u)) (Ioi 0) := by
  simpa only [Real.rpow_one] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (by norm_num) (by norm_num) hx

lemma integral_mul_exp_tail {x : ℝ} (hx : 0 < x) :
    (∫ u : ℝ in Ioi 0, u * Real.exp (-x * u)) = 1 / x ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) hx
  have hg : Real.Gamma (2 : ℝ) = 1 := by simp
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
    hg, mul_one, one_div, inv_pow, neg_mul] at h
  simpa only [neg_mul, one_div] using h

lemma integrableOn_tailKernel {x : ℝ} (hx : 0 < x) :
    IntegrableOn (tailKernel x) (Ioi 0) := by
  apply (integrableOn_exp_tail hx).mono'
  · exact (by unfold tailKernel; fun_prop : Continuous (tailKernel x)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun u ↦ by
      simpa only [Real.norm_eq_abs, abs_of_pos (tailKernel_pos x u)] using tailKernel_le_exp x u)

lemma integrableOn_mul_tailKernel {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ ↦ u * tailKernel x u) (Ioi 0) := by
  apply (integrableOn_mul_exp_tail hx).mono'
  · exact (by unfold tailKernel; fun_prop : Continuous (fun u ↦ u * tailKernel x u)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hu.le (tailKernel_pos x u).le)]
    exact mul_le_mul_of_nonneg_left (tailKernel_le_exp x u) hu.le

lemma integral_tailKernel_le {x : ℝ} (hx : 0 < x) :
    (∫ u in Ioi 0, tailKernel x u) ≤ 1 / x := by
  rw [← integral_exp_tail hx]
  exact integral_mono (integrableOn_tailKernel hx) (integrableOn_exp_tail hx)
    (tailKernel_le_exp x)

lemma integral_mul_tailKernel_le {x : ℝ} (hx : 0 < x) :
    (∫ u in Ioi 0, u * tailKernel x u) ≤ 1 / x ^ 2 := by
  rw [← integral_mul_exp_tail hx]
  apply integral_mono_ae (integrableOn_mul_tailKernel hx) (integrableOn_mul_exp_tail hx)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact mul_le_mul_of_nonneg_left (tailKernel_le_exp x u) hu.le

lemma hasDerivAt_tailKernel (x u : ℝ) :
    HasDerivAt (tailKernel x) (-(x + u) * tailKernel x u) u := by
  have hp : HasDerivAt (fun u : ℝ ↦ -x * u - u ^ 2 / 2) (-x - u) u := by
    have h := ((hasDerivAt_id u).const_mul (-x)).sub
      (((hasDerivAt_id u).pow 2).div_const 2)
    change HasDerivAt (fun u : ℝ ↦ -x * u - u ^ 2 / 2)
      (-x * 1 - (2 : ℝ) * u ^ (2 - 1) * 1 / 2) u at h
    convert h using 1
    norm_num
  have h := hp.exp
  change HasDerivAt (tailKernel x) (tailKernel x u * (-x - u)) u at h
  convert h using 1
  ring

lemma tendsto_tailKernel_zero {x : ℝ} (hx : 0 < x) :
    Tendsto (tailKernel x) atTop (𝓝 0) := by
  have he : Tendsto (fun u : ℝ ↦ Real.exp (-x * u)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.neg_mul_atTop (neg_lt_zero.mpr hx) tendsto_id)
  exact squeeze_zero (fun u ↦ (tailKernel_pos x u).le) (tailKernel_le_exp x) he

lemma tailKernel_moment_identity {x : ℝ} (hx : 0 < x) :
    x * (∫ u in Ioi 0, tailKernel x u) + (∫ u in Ioi 0, u * tailKernel x u) = 1 := by
  have hi0 := integrableOn_tailKernel hx
  have hi1 := integrableOn_mul_tailKernel hx
  have hi : IntegrableOn (fun u ↦ -(x + u) * tailKernel x u) (Ioi 0) := by
    have hi' : Integrable (fun u ↦ -(x * tailKernel x u + u * tailKernel x u))
        (volume.restrict (Ioi 0)) := ((hi0.const_mul x).add hi1).neg
    exact hi'.congr (Filter.Eventually.of_forall (fun u ↦ by ring))
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u _ ↦ hasDerivAt_tailKernel x u) hi (tendsto_tailKernel_zero hx)
  have he : (fun u ↦ -(x + u) * tailKernel x u) =
      (fun u ↦ -(x * tailKernel x u + u * tailKernel x u)) := by funext u; ring
  rw [he, integral_neg, integral_add (hi0.const_mul x) hi1, integral_const_mul] at h
  have hz : tailKernel x 0 = 1 := by simp [tailKernel]
  simp only [hz, zero_sub] at h
  linarith

end ExactOverlaps.GaussianApproximation
