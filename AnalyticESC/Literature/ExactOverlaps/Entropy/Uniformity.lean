module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Atomicity

set_option maxSynthPendingDepth 3

/-!
# Low-entropy exceptional components of an almost-uniform law

The deficiency `1 - H_m` is nonnegative for a rescaled component. Applying
the same finite Markov argument to this deficiency yields the uniformity
counterpart of the atomicity estimate.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.Uniformity`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

/-- Probability that a component has entropy at most `1-a`. -/
noncomputable def componentEntropyLowerTailMass (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) (a : ℝ) : ℝ := by
  classical
  letI : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  exact ∑ k : (dyadicLaw μ i).support,
    if normalizedDyadicEntropy (rescaledComponent μ i k)
      (rescaledComponent_hasBoundedSupport μ i k) m ≤ 1 - a
      then ((dyadicLaw μ i) k).toReal else 0

lemma componentEntropyLowerTailMass_nonneg (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) (a : ℝ) :
    0 ≤ componentEntropyLowerTailMass μ hμ i m a := by
  unfold componentEntropyLowerTailMass
  apply Finset.sum_nonneg
  intro k _
  split_ifs <;> positivity

lemma componentEntropyLowerTailMass_le_one (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) (a : ℝ) :
    componentEntropyLowerTailMass μ hμ i m a ≤ 1 := by
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  rw [← sum_dyadic_cell_mass μ hμ i]
  unfold componentEntropyLowerTailMass
  apply Finset.sum_le_sum
  intro k _
  split_ifs <;> simp

lemma mul_componentEntropyLowerTailMass_le (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) {m : ℕ} (hm : 0 < m) (a : ℝ) :
    a * componentEntropyLowerTailMass μ hμ i m a ≤ 1 - averageComponentEntropy μ hμ i m := by
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  rw [le_sub_iff_add_le, ← sum_dyadic_cell_mass μ hμ i]
  unfold componentEntropyLowerTailMass averageComponentEntropy
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  split_ifs with h
  · have hmul := mul_le_mul_of_nonneg_left h
      (show 0 ≤ ((dyadicLaw μ i) k).toReal from ENNReal.toReal_nonneg)
    nlinarith
  · simp only [mul_zero, zero_add]
    have he := normalizedDyadicEntropy_le_one _
      (rescaledComponent_hasBoundedSupport μ i k) hm (ae_rescaledComponent_mem_Ico μ i k)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he
      (show 0 ≤ ((dyadicLaw μ i) k).toReal from ENNReal.toReal_nonneg)

/-- Probability of a low-entropy component under uniform selection of a level. -/
noncomputable def levelEntropyLowerTailMass (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n m : ℕ) (a : ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, componentEntropyLowerTailMass μ hμ i m a) / n

lemma mul_levelEntropyLowerTailMass_le (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (a : ℝ) :
    a * levelEntropyLowerTailMass μ hμ n m a ≤ 1 - levelAverageComponentEntropy μ hμ n m := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsum : a * (∑ i ∈ Finset.range n, componentEntropyLowerTailMass μ hμ i m a) ≤
      (n : ℝ) - ∑ i ∈ Finset.range n, averageComponentEntropy μ hμ i m := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ i ∈ Finset.range n, (1 - averageComponentEntropy μ hμ i m) :=
        Finset.sum_le_sum (fun i _ ↦ mul_componentEntropyLowerTailMass_le μ hμ i hm a)
      _ = _ := by simp [Finset.sum_sub_distrib]
  unfold levelEntropyLowerTailMass levelAverageComponentEntropy
  rw [← mul_div_assoc]
  calc
    _ ≤ ((n : ℝ) - ∑ i ∈ Finset.range n, averageComponentEntropy μ hμ i m) / n :=
      div_le_div_of_nonneg_right hsum hn'.le
    _ = _ := by rw [sub_div, div_self hn'.ne']

/-- High entropy of a unit-cell law forces high entropy in most of its components. -/
theorem levelEntropyLowerTailMass_le_of_unit_support (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ)
    (hunit : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Ico (0 : ℝ) 1)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {a : ℝ} (ha : 0 < a) :
    levelEntropyLowerTailMass μ hμ n m a ≤
      (1 - normalizedDyadicEntropy μ hμ n + (m : ℝ) / n) / a := by
  apply (le_div_iff₀ ha).mpr
  rw [mul_comm]
  apply (mul_levelEntropyLowerTailMass_le μ hμ hn hm a).trans
  have h := (abs_le.mp (abs_levelAverageComponentEntropy_sub_le μ hμ hn hm)).1
  rw [dyadicEntropy_zero_of_unit_support μ hμ hunit, zero_div, add_zero] at h
  linarith

end ExactOverlaps.Entropy
