module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Dyadic

set_option maxSynthPendingDepth 3

/-!
# Sharp entropy bounds for the unit cell

The half-open support condition is explicit: it gives exactly `2^m` possible
labels at level `m`, without an additional boundary atom at one.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.DyadicBounds`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set

namespace ExactOverlaps.Entropy

lemma dyadicQuantize_mem_unit_labels (m : ℕ) {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    dyadicQuantize m x ∈ Ico (0 : ℤ) (2 ^ m) := by
  have hp : 0 < (2 : ℝ) ^ m := pow_pos (by norm_num) _
  constructor
  · apply Int.floor_nonneg.mpr
    exact mul_nonneg (dyadic_scale_pos m).le hx.1
  · have h : (dyadicQuantize m x : ℝ) < (2 : ℝ) ^ m := by
      unfold dyadicQuantize
      rw [zpow_natCast]
      exact (Int.floor_le _).trans_lt (by nlinarith [hx.2])
    exact_mod_cast h

lemma dyadicLaw_support_subset_unit_labels (μ : ProbabilityMeasure ℝ) (m : ℕ)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Ico (0 : ℝ) 1) :
    (dyadicLaw μ m).support ⊆ Ico (0 : ℤ) (2 ^ m) := by
  intro k hk
  by_contra hnot
  have hz : (μ : Measure ℝ) (dyadicCell m k) = 0 := by
    apply measure_mono_null (t := {x | x ∉ Ico (0 : ℝ) 1})
    · intro x hx hunit
      apply hnot
      have hlabel := dyadicQuantize_mem_unit_labels m hunit
      rwa [show dyadicQuantize m x = k from hx] at hlabel
    · exact ae_iff.mp hμ
  exact hk (by rw [dyadicLaw_apply, hz])

lemma dyadicLaw_card_le_pow_two (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (m : ℕ) (hunit : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Ico (0 : ℝ) 1) :
    (dyadicLaw_support_finite μ hμ m).toFinset.card ≤ 2 ^ m := by
  have hsub : (dyadicLaw_support_finite μ hμ m).toFinset ⊆
      Finset.Ico (0 : ℤ) (2 ^ m) := by
    intro k hk
    exact Finset.mem_Ico.mpr (dyadicLaw_support_subset_unit_labels μ m hunit
      (by simpa using hk))
  have h := Finset.card_le_card hsub
  have h' : ((dyadicLaw_support_finite μ hμ m).toFinset.card : ℤ) ≤ (2 : ℤ) ^ m := by
    simpa using h
  exact_mod_cast h'

lemma dyadicEntropy_le_nat_mul_log_two (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (m : ℕ)
    (hunit : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Ico (0 : ℝ) 1) :
    dyadicEntropy μ hμ m ≤ (m : ℝ) * Real.log 2 := by
  have hcard := dyadicLaw_card_le_pow_two μ hμ m hunit
  have hpos : (0 : ℝ) < (dyadicLaw_support_finite μ hμ m).toFinset.card := by
    exact_mod_cast Finset.card_pos.mpr (by simp)
  calc
    dyadicEntropy μ hμ m ≤ Real.log (dyadicLaw_support_finite μ hμ m).toFinset.card :=
      finiteEntropy_le_log_card _ _
    _ ≤ Real.log ((2 ^ m : ℕ) : ℝ) := Real.log_le_log hpos (by exact_mod_cast hcard)
    _ = (m : ℝ) * Real.log 2 := by rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

lemma normalizedDyadicEntropy_le_one (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) {m : ℕ} (hm : 0 < m)
    (hunit : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Ico (0 : ℝ) 1) :
    normalizedDyadicEntropy μ hμ m ≤ 1 := by
  unfold normalizedDyadicEntropy
  apply (div_le_one (mul_pos (Nat.cast_pos.mpr hm) (Real.log_pos (by norm_num)))).mpr
  exact dyadicEntropy_le_nat_mul_log_two μ hμ m hunit

end ExactOverlaps.Entropy
