module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Components
public import AnalyticESC.Literature.ExactOverlaps.Entropy.DyadicMixture

set_option maxSynthPendingDepth 3

/-!
# Exact decomposition into positive-mass dyadic components

The normalized restrictions reconstruct the original Borel probability
measure with their actual cell masses. Zero-mass cells are discarded by a
proved null-set argument, not by a choice of conditional laws on null cells.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.ComponentMixture`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ExactOverlaps.Entropy

lemma sum_dyadicCell_inter (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (i : ℤ) (A : Set ℝ) (hA : MeasurableSet A) :
    (∑ k ∈ (dyadicLaw_support_finite μ hμ i).toFinset,
      (μ : Measure ℝ) (dyadicCell i k ∩ A)) = (μ : Measure ℝ) A := by
  classical
  have hcover : (⋃ k : ℤ, dyadicCell i k ∩ A) = A := by
    ext x
    simp only [mem_iUnion, mem_inter_iff]
    constructor
    · rintro ⟨_, _, hx⟩
      exact hx
    · intro hx
      exact ⟨dyadicQuantize i x, rfl, hx⟩
  have hdisj : Pairwise (fun j k : ℤ ↦ Disjoint (dyadicCell i j ∩ A) (dyadicCell i k ∩ A)) := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hjk (hx.1.symm.trans hy.1)
  calc
    _ = ∑' k : ℤ, (μ : Measure ℝ) (dyadicCell i k ∩ A) := by
      symm
      apply tsum_eq_sum
      intro k hk
      have hz : (dyadicLaw μ i) k = 0 := by simpa using hk
      rw [dyadicLaw_apply] at hz
      exact measure_mono_null inter_subset_left hz
    _ = (μ : Measure ℝ) (⋃ k : ℤ, dyadicCell i k ∩ A) :=
      (measure_iUnion hdisj (fun k ↦ (measurableSet_dyadicCell i k).inter hA)).symm
    _ = _ := by rw [hcover]

lemma dyadic_cell_mass_mul_rawComponent (μ : ProbabilityMeasure ℝ) (i : ℤ)
    (k : (dyadicLaw μ i).support) (A : Set ℝ) :
    (dyadicLaw μ i) k * (rawComponent μ i k : Measure ℝ) A =
      (μ : Measure ℝ) (dyadicCell i k ∩ A) := by
  rw [dyadicLaw_apply, rawComponent_apply]
  exact ENNReal.mul_inv_cancel_left (dyadicCell_measure_ne_zero μ i k) (measure_ne_top _ _)

/-- Reconstruct the real probability measure as the finite mixture of its components. -/
theorem measure_eq_rawComponent_mixture (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) :
    (μ : Measure ℝ) =
      (letI : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
      ∑ k : (dyadicLaw μ i).support, (supportLaw (dyadicLaw μ i)) k •
        (rawComponent μ i k : Measure ℝ)) := by
  classical
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  apply Measure.ext
  intro A hA
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    supportLaw_apply, dyadic_cell_mass_mul_rawComponent]
  rw [← Finset.sum_subtype (dyadicLaw_support_finite μ hμ i).toFinset
    (by simp : ∀ k, k ∈ (dyadicLaw_support_finite μ hμ i).toFinset ↔ k ∈ (dyadicLaw μ i).support)
    (fun k ↦ (μ : Measure ℝ) (dyadicCell i k ∩ A))]
  exact (sum_dyadicCell_inter μ hμ i A hA).symm

end ExactOverlaps.Entropy
