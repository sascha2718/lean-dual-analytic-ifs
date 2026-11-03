module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Concentration
public import Mathlib.Probability.Moments.Variance

set_option maxSynthPendingDepth 3

/-!
# Entropy controls variance on a bounded interval

A large dyadic cell provides a center near most of the mass. Comparing with
the squared distance from that center bounds the actual measure variance.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.VarianceConcentration`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ExactOverlaps.Entropy

lemma variance_le_sq_add_compl_mass (μ : ProbabilityMeasure ℝ)
    (hunit : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    {s : Set ℝ} (hs : MeasurableSet s) {c r : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) (hr : 0 ≤ r)
    (hnear : ∀ x ∈ s, x ∈ Icc (0 : ℝ) 1 → |x - c| ≤ r) :
    ProbabilityTheory.variance id (μ : Measure ℝ) ≤
      r ^ 2 + ((μ : Measure ℝ) sᶜ).toReal := by
  have hsq : Integrable (fun x : ℝ ↦ (x - c) ^ 2) (μ : Measure ℝ) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [hunit] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have ha : |x - c| ≤ 1 := abs_le.mpr
      ⟨by linarith [hc.2, hx.1], by linarith [hc.1, hx.2]⟩
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 ha
  have hi : Integrable (sᶜ.indicator (fun _ : ℝ ↦ (1 : ℝ))) (μ : Measure ℝ) :=
    (integrable_const 1).indicator hs.compl
  have hbound : ∀ᵐ x ∂(μ : Measure ℝ), (x - c) ^ 2 ≤
      r ^ 2 + sᶜ.indicator (fun _ : ℝ ↦ (1 : ℝ)) x := by
    filter_upwards [hunit] with x hx
    by_cases hxS : x ∈ s
    · have h := hnear x hxS hx
      rw [indicator_of_notMem (by simpa using hxS), add_zero]
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr).2 h
    · rw [indicator_of_mem hxS]
      have hdiff : |x - c| ≤ 1 := abs_le.mpr ⟨by linarith [hc.2, hx.1], by linarith [hc.1, hx.2]⟩
      have hsquare : (x - c) ^ 2 ≤ 1 := by
        simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 hdiff
      linarith [sq_nonneg r]
  have h := integral_mono_ae hsq ((integrable_const (r ^ 2)).add hi) hbound
  change (∫ x : ℝ, (x - c) ^ 2 ∂(μ : Measure ℝ)) ≤
    ∫ x : ℝ, r ^ 2 + sᶜ.indicator (fun _ : ℝ ↦ (1 : ℝ)) x ∂(μ : Measure ℝ) at h
  rw [integral_add (integrable_const (r ^ 2)) hi, integral_const,
    integral_indicator_const 1 hs.compl] at h
  simp only [smul_eq_mul, mul_one, Measure.real, measure_univ, ENNReal.toReal_one, one_mul] at h
  have hv := variance_le_expectation_sq (μ := (μ : Measure ℝ))
    (X := fun x : ℝ ↦ x - c) (by fun_prop)
  have hv' : ProbabilityTheory.variance (fun x : ℝ ↦ x - c) (μ : Measure ℝ) =
      ProbabilityTheory.variance id (μ : Measure ℝ) :=
    variance_sub_const measurable_id.aestronglyMeasurable c
  rw [hv'] at hv
  exact hv.trans h

lemma abs_sub_le_of_mem_dyadicCell {i k : ℤ} {x y : ℝ}
    (hx : x ∈ dyadicCell i k) (hy : y ∈ dyadicCell i k) :
    |x - y| ≤ (2 : ℝ) ^ (-i) := by
  rw [dyadicCell_eq_Ico] at hx hy
  have hscale : (2 : ℝ) ^ (-i) = 1 / (2 : ℝ) ^ i := by simp [zpow_neg]
  rw [hscale]
  simp only [add_div] at hx hy
  apply abs_le.mpr
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- Quantitative small-entropy-to-small-variance bound, with natural-log entropy. -/
theorem variance_le_dyadicEntropy_add_mesh_sq (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ)
    (hunit : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1) (i : ℤ) :
    ProbabilityTheory.variance id (μ : Measure ℝ) ≤
      dyadicEntropy μ hμ i + ((2 : ℝ) ^ (-i)) ^ 2 := by
  obtain ⟨k, hk, hmass⟩ := exists_dyadicCell_one_sub_entropy_le μ hμ i
  have hcell : (μ : Measure ℝ) (dyadicCell i k) ≠ 0 := by
    simpa only [PMF.mem_support_iff, dyadicLaw_apply] using hk
  have he : (μ : Measure ℝ) (dyadicCell i k ∩ Icc (0 : ℝ) 1) =
      (μ : Measure ℝ) (dyadicCell i k) := by
    apply measure_congr
    filter_upwards [hunit] with x hx
    simp [hx]
  obtain ⟨c, hcs, hc⟩ := nonempty_of_measure_ne_zero (he ▸ hcell)
  have h := variance_le_sq_add_compl_mass μ hunit (measurableSet_dyadicCell i k) hc
    (le_of_lt (zpow_pos (by norm_num) _)) (fun x hx _ ↦ abs_sub_le_of_mem_dyadicCell hx hcs)
  have hcpl := measureReal_add_measureReal_compl (μ := (μ : Measure ℝ))
    (measurableSet_dyadicCell i k)
  simp only [Measure.real, measure_univ, ENNReal.toReal_one] at hcpl
  change ((μ : Measure ℝ) (dyadicCell i k)).toReal +
    ((μ : Measure ℝ) (dyadicCell i k)ᶜ).toReal = 1 at hcpl
  linarith

end ExactOverlaps.Entropy
