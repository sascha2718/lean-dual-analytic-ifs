module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Dyadic

set_option maxSynthPendingDepth 3

/-!
# Concentration and dyadic labels

A neighborhood of radius half a cell width meets at most two relevant cell
labels. Event probabilities for the quantized law are actual measure masses.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.DyadicConcentration`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.Entropy

lemma dyadicLaw_map_bool_apply (μ : ProbabilityMeasure ℝ) (i : ℤ) (f : ℤ → Bool) :
    ((dyadicLaw μ i).map f) true =
      (μ : Measure ℝ) {x | f (dyadicQuantize i x) = true} := by
  have hf : Measurable f := measurable_of_countable _
  rw [← PMF.toMeasure_apply_singleton _ true (measurableSet_singleton true),
    ← PMF.toMeasure_map _ _ hf, dyadicLaw_toMeasure,
    Measure.map_map hf (measurable_dyadicQuantize i),
    Measure.map_apply (hf.comp (measurable_dyadicQuantize i)) (measurableSet_singleton true)]
  rfl

lemma dyadicQuantize_near_center (i : ℤ) (c x : ℝ)
    (h : |x - c| < 1 / (2 * (2 : ℝ) ^ i)) :
    dyadicQuantize i x ∈
      Icc (dyadicQuantize i (c - 1 / (2 * (2 : ℝ) ^ i)))
        (dyadicQuantize i (c - 1 / (2 * (2 : ℝ) ^ i)) + 1) := by
  have hp := dyadic_scale_pos i
  have ha := abs_lt.mp h
  have hlow : c - 1 / (2 * (2 : ℝ) ^ i) ≤ x := by linarith [ha.1]
  have hupp : x ≤ c + 1 / (2 * (2 : ℝ) ^ i) := by linarith [ha.2]
  refine ⟨Int.floor_mono (mul_le_mul_of_nonneg_left hlow hp.le), ?_⟩
  have he : (2 : ℝ) ^ i * (c + 1 / (2 * (2 : ℝ) ^ i)) =
      (2 : ℝ) ^ i * (c - 1 / (2 * (2 : ℝ) ^ i)) + 1 := by field_simp; ring
  have hb := mul_le_mul_of_nonneg_left hupp hp.le
  rw [he] at hb
  simpa only [dyadicQuantize, Int.floor_add_one] using Int.floor_mono hb

lemma dyadicLaw_card_le_pow_two_add_one (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (m : ℕ)
    (hunit : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1) :
    (dyadicLaw_support_finite μ hμ m).toFinset.card ≤ 2 ^ m + 1 := by
  have hzero : dyadicQuantize m 0 = 0 := by simp [dyadicQuantize]
  have hone : dyadicQuantize m 1 = (2 : ℤ) ^ m := by
    simp only [dyadicQuantize, mul_one, zpow_natCast]
    have he : (2 : ℝ) ^ m = (((2 : ℤ) ^ m : ℤ) : ℝ) := by simp
    rw [he, Int.floor_intCast]
  have hsub : (dyadicLaw_support_finite μ hμ m).toFinset ⊆
      Finset.Icc (0 : ℤ) ((2 : ℤ) ^ m) := by
    intro k hk
    have h := dyadicLaw_support_subset μ m hunit (by simpa using hk)
    simpa only [hzero, hone, Finset.mem_Icc, Set.mem_Icc] using h
  have h := Finset.card_le_card hsub
  have he : (Finset.Icc (0 : ℤ) ((2 : ℤ) ^ m)).card = 2 ^ m + 1 := by
    rw [Int.card_Icc]
    have hp : (2 : ℤ) ^ m = ((2 ^ m : ℕ) : ℤ) := by simp
    rw [hp, sub_zero]
    exact Int.toNat_natCast (2 ^ m + 1)
  simpa only [he] using h

end ExactOverlaps.Entropy
