module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Averaging

set_option maxSynthPendingDepth 3

/-!
# Entropy tails of random dyadic components

The probabilities below sum the actual cell masses, first at a fixed level
and then under uniform choice of a level. Markov's inequality together with
the proved averaging estimate controls the exceptional components.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.Atomicity`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

/-- Probability that a level-`i` component has normalized entropy at least `a`. -/
noncomputable def componentEntropyTailMass (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) (a : ℝ) : ℝ := by
  classical
  letI : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  exact ∑ k : (dyadicLaw μ i).support,
    if a ≤ normalizedDyadicEntropy (rescaledComponent μ i k)
      (rescaledComponent_hasBoundedSupport μ i k) m then ((dyadicLaw μ i) k).toReal else 0

lemma componentEntropyTailMass_nonneg (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) (a : ℝ) :
    0 ≤ componentEntropyTailMass μ hμ i m a := by
  unfold componentEntropyTailMass
  apply Finset.sum_nonneg
  intro k _
  split_ifs <;> positivity

lemma componentEntropyTailMass_le_one (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) (a : ℝ) :
    componentEntropyTailMass μ hμ i m a ≤ 1 := by
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  rw [← sum_dyadic_cell_mass μ hμ i]
  unfold componentEntropyTailMass
  apply Finset.sum_le_sum
  intro k _
  split_ifs <;> simp

lemma mul_componentEntropyTailMass_le (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) (a : ℝ) :
    a * componentEntropyTailMass μ hμ i m a ≤ averageComponentEntropy μ hμ i m := by
  unfold componentEntropyTailMass averageComponentEntropy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  split_ifs with h
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left h
      (show 0 ≤ ((dyadicLaw μ i) k).toReal from ENNReal.toReal_nonneg)
  · simp only [mul_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (normalizedDyadicEntropy_nonneg _ _ _)

/-- Probability of an entropy tail when a level in `0,…,n−1` is chosen uniformly. -/
noncomputable def levelEntropyTailMass (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n m : ℕ) (a : ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, componentEntropyTailMass μ hμ i m a) / n

lemma mul_levelEntropyTailMass_le (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n m : ℕ) (a : ℝ) :
    a * levelEntropyTailMass μ hμ n m a ≤ levelAverageComponentEntropy μ hμ n m := by
  unfold levelEntropyTailMass levelAverageComponentEntropy
  rw [← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact Finset.sum_le_sum (fun i _ ↦ mul_componentEntropyTailMass_le μ hμ i m a)

theorem levelEntropyTailMass_le (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {a : ℝ} (ha : 0 < a) :
    levelEntropyTailMass μ hμ n m a ≤
      (normalizedDyadicEntropy μ hμ n + (m : ℝ) / n +
        dyadicEntropy μ hμ 0 / ((n : ℝ) * Real.log 2)) / a := by
  apply (le_div_iff₀ ha).mpr
  rw [mul_comm]
  apply (mul_levelEntropyTailMass_le μ hμ n m a).trans
  have h := (abs_le.mp (abs_levelAverageComponentEntropy_sub_le μ hμ hn hm)).2
  linarith

lemma dyadicEntropy_zero_of_unit_support (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ)
    (hunit : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Ico (0 : ℝ) 1) :
    dyadicEntropy μ hμ 0 = 0 := by
  have h : dyadicEntropy μ hμ 0 ≤ 0 := by
    simpa using dyadicEntropy_le_nat_mul_log_two μ hμ 0 hunit
  exact le_antisymm h (dyadicEntropy_nonneg μ hμ 0)

/-- Small entropy of a unit-cell law forces small entropy in most of its components. -/
theorem levelEntropyTailMass_le_of_unit_support (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ)
    (hunit : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Ico (0 : ℝ) 1)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {a : ℝ} (ha : 0 < a) :
    levelEntropyTailMass μ hμ n m a ≤
      (normalizedDyadicEntropy μ hμ n + (m : ℝ) / n) / a := by
  simpa only [dyadicEntropy_zero_of_unit_support μ hμ hunit, zero_div, add_zero] using
    levelEntropyTailMass_le μ hμ hn hm ha

end ExactOverlaps.Entropy
