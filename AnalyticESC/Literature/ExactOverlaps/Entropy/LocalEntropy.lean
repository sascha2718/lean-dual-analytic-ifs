module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Components
public import AnalyticESC.Literature.ExactOverlaps.Entropy.DyadicBounds

set_option maxSynthPendingDepth 3

/-!
# Entropy averages of dyadic components

All averages use the actual probabilities of positive-mass cells. The entropy
increment identity and the unit-cell cardinality bound supply uniform bounds
without assuming an entropy-dimension theorem.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.LocalEntropy`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

lemma sum_dyadic_cell_mass (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (i : ℤ)
    [Fintype (dyadicLaw μ i).support] :
    ∑ k : (dyadicLaw μ i).support, ((dyadicLaw μ i) k).toReal = 1 := by
  classical
  rw [← Finset.sum_subtype (dyadicLaw_support_finite μ hμ i).toFinset
    (by simp : ∀ k, k ∈ (dyadicLaw_support_finite μ hμ i).toFinset ↔
      k ∈ (dyadicLaw μ i).support) (fun k : ℤ ↦ ((dyadicLaw μ i) k).toReal)]
  exact sum_support_toReal _ _

lemma dyadicEntropy_increment_le (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (i : ℤ) (m : ℕ) :
    dyadicEntropy μ hμ (i + m) - dyadicEntropy μ hμ i ≤ (m : ℝ) * Real.log 2 := by
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  rw [← averageRawComponentEntropy_eq_sub]
  unfold averageRawComponentEntropy
  calc
    _ ≤ ∑ k : (dyadicLaw μ i).support,
        ((dyadicLaw μ i) k).toReal * ((m : ℝ) * Real.log 2) := by
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      rw [← dyadicEntropy_rescaledComponent]
      exact dyadicEntropy_le_nat_mul_log_two _ _ _ (ae_rescaledComponent_mem_Ico μ i k)
    _ = (m : ℝ) * Real.log 2 := by
      rw [← Finset.sum_mul, sum_dyadic_cell_mass μ hμ i, one_mul]

/-- Expected normalized entropy of a random rescaled level-`i` component. -/
noncomputable def averageComponentEntropy (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) : ℝ :=
  letI : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  ∑ k : (dyadicLaw μ i).support, ((dyadicLaw μ i) k).toReal *
    normalizedDyadicEntropy (rescaledComponent μ i k)
      (rescaledComponent_hasBoundedSupport μ i k) m

theorem averageComponentEntropy_eq_increment (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) :
    averageComponentEntropy μ hμ i m =
      (dyadicEntropy μ hμ (i + m) - dyadicEntropy μ hμ i) / ((m : ℝ) * Real.log 2) := by
  rw [← averageRawComponentEntropy_eq_sub]
  unfold averageComponentEntropy averageRawComponentEntropy
  simp only [normalizedDyadicEntropy, dyadicEntropy_rescaledComponent, ← mul_div_assoc]
  rw [← Finset.sum_div]

lemma averageComponentEntropy_nonneg (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) :
    0 ≤ averageComponentEntropy μ hμ i m := by
  rw [averageComponentEntropy_eq_increment]
  exact div_nonneg (sub_nonneg.mpr (dyadicEntropy_le_add_nat μ hμ i m))
    (mul_nonneg (Nat.cast_nonneg m) (Real.log_nonneg (by norm_num)))

lemma averageComponentEntropy_le_one (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) {m : ℕ} (hm : 0 < m) :
    averageComponentEntropy μ hμ i m ≤ 1 := by
  rw [averageComponentEntropy_eq_increment]
  apply (div_le_one (mul_pos (Nat.cast_pos.mpr hm) (Real.log_pos (by norm_num)))).mpr
  exact dyadicEntropy_increment_le μ hμ i m

end ExactOverlaps.Entropy
