module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.WassersteinTests
public import Mathlib.Probability.CDF

set_option maxSynthPendingDepth 3

/-!
# Distribution-function control from the dual distance

A unit Lipschitz ramp approximates a half-line indicator. This gives a shifted
CDF bound without any atom restrictions. If the comparison CDF is Lipschitz,
it gives a uniform unshifted error bound.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.CDFDistance`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace ExactOverlaps.GaussianApproximation

/-- A descending ramp of height e across the interval from a to a+e. -/
def cdfRamp (a e x : ℝ) : ℝ := max 0 (min e (a + e - x))

lemma lipschitz_cdfRamp (a e : ℝ) : LipschitzWith 1 (cdfRamp a e) := by
  have h : LipschitzWith 1 (fun x : ℝ ↦ a + e - x) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    have he : a + e - x - (a + e - y) = -(x - y) := by ring
    rw [he, abs_neg]
  exact (h.const_min e).const_max 0

lemma indicator_le_cdfRamp (a : ℝ) {e : ℝ} (he : 0 ≤ e) (x : ℝ) :
    (Iic a).indicator (fun _ ↦ e) x ≤ cdfRamp a e x := by
  by_cases hx : x ≤ a
  · rw [indicator_of_mem (show x ∈ Iic a from hx)]
    simp only [cdfRamp, min_eq_left (by linarith : e ≤ a + e - x), max_eq_right he]
    exact le_rfl
  · rw [indicator_of_notMem (show x ∉ Iic a from hx)]
    exact le_max_left _ _

lemma cdfRamp_le_indicator (a : ℝ) {e : ℝ} (he : 0 ≤ e) (x : ℝ) :
    cdfRamp a e x ≤ (Iic (a + e)).indicator (fun _ ↦ e) x := by
  by_cases hx : x ≤ a + e
  · rw [indicator_of_mem (show x ∈ Iic (a + e) from hx)]
    exact max_le he (min_le_left _ _)
  · rw [indicator_of_notMem (show x ∉ Iic (a + e) from hx)]
    exact max_le le_rfl ((min_le_right _ _).trans (by linarith))

lemma cdf_le_shift_add_wasserstein1_div (μ ν : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    (hν : Integrable (fun x : ℝ ↦ x) (ν : Measure ℝ))
    (a : ℝ) {e : ℝ} (he : 0 < e) :
    cdf (μ : Measure ℝ) a ≤ cdf (ν : Measure ℝ) (a + e) + wasserstein1 μ ν hμ hν / e := by
  have hm := integrable_unitLipschitz μ hμ (lipschitz_cdfRamp a e)
  have hn := integrable_unitLipschitz ν hν (lipschitz_cdfRamp a e)
  have hl := integral_mono ((integrable_const e).indicator measurableSet_Iic) hm
    (indicator_le_cdfRamp a he.le)
  have hu := integral_mono hn ((integrable_const e).indicator measurableSet_Iic)
    (cdfRamp_le_indicator a he.le)
  rw [integral_indicator_const e measurableSet_Iic, smul_eq_mul,
    ← cdf_eq_real] at hl hu
  have hd := abs_integral_sub_le_wasserstein1_of_lipschitz μ ν hμ hν
    (lipschitz_cdfRamp a e)
  have hsub := (le_abs_self _).trans hd
  apply (mul_le_mul_iff_of_pos_right he).mp
  have heq : (cdf (ν : Measure ℝ) (a + e) + wasserstein1 μ ν hμ hν / e) * e =
      cdf (ν : Measure ℝ) (a + e) * e + wasserstein1 μ ν hμ hν := by
    field_simp
  rw [heq]
  linarith

/-- A Lipschitz comparison CDF turns transport error into uniform CDF error. -/
theorem abs_cdf_sub_le (μ ν : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    (hν : Integrable (fun x : ℝ ↦ x) (ν : Measure ℝ))
    {L : ℝ≥0} (hL : LipschitzWith L (cdf (ν : Measure ℝ)))
    (a : ℝ) {e : ℝ} (he : 0 < e) :
    |cdf (μ : Measure ℝ) a - cdf (ν : Measure ℝ) a| ≤
      wasserstein1 μ ν hμ hν / e + (L : ℝ) * e := by
  have hp := cdf_le_shift_add_wasserstein1_div μ ν hμ hν a he
  have hn := cdf_le_shift_add_wasserstein1_div ν μ hν hμ (a - e) he
  rw [wasserstein1_comm ν μ hν hμ] at hn
  have hplus := hL.dist_le_mul (a + e) a
  have hminus := hL.dist_le_mul a (a - e)
  simp only [Real.dist_eq, add_sub_cancel_left, sub_sub_cancel, abs_of_pos he] at hplus hminus
  have hplus' := (le_abs_self _).trans hplus
  have hminus' := (le_abs_self _).trans hminus
  rw [sub_add_cancel] at hn
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end ExactOverlaps.GaussianApproximation
