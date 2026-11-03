module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Uniformity

set_option maxSynthPendingDepth 3

/-!
# Finite certificates of component uniformity

A finite set of labels whose positive-mass components all have high entropy
certifies the corresponding lower bound on the actual uniform-component
probability. Zero-mass labels require no arbitrary conditional law.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.FiniteComponentCertificate`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators Classical

namespace ExactOverlaps.Entropy

lemma sum_finset_pmf_eq_support_indicator {α : Type*} [DecidableEq α]
    (p : PMF α) (hp : p.support.Finite) (J : Finset α) :
    letI : Fintype p.support := hp.fintype
    (∑ a ∈ J, (p a).toReal) = ∑ a : p.support, if a.val ∈ J then (p a).toReal else 0 := by
  let : Fintype p.support := hp.fintype
  rw [← Finset.sum_subtype hp.toFinset (by simp : ∀ a, a ∈ hp.toFinset ↔ a ∈ p.support)
    (fun a ↦ if a ∈ J then (p a).toReal else 0)]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
  symm
  apply Finset.sum_subset Finset.inter_subset_left
  intro a ha hnot
  have hpnot : a ∉ p.support := by
    intro hpa
    apply hnot
    exact Finset.mem_inter.mpr ⟨ha, by simpa using hpa⟩
  have hz : p a = 0 := by simpa using hpnot
  simp only [hz, ENNReal.toReal_zero]

theorem componentEntropyLowerTailMass_le_compl_finset (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) (δ : ℝ) (J : Finset ℤ)
    (hJ : ∀ k : (dyadicLaw μ i).support, k.val ∈ J →
      1 - δ < normalizedDyadicEntropy (rescaledComponent μ i k)
        (rescaledComponent_hasBoundedSupport μ i k) m) :
    componentEntropyLowerTailMass μ hμ i m δ ≤
      1 - ∑ k ∈ J, ((dyadicLaw μ i) k).toReal := by
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  rw [le_sub_iff_add_le, sum_finset_pmf_eq_support_indicator
    (dyadicLaw μ i) (dyadicLaw_support_finite μ hμ i) J, ← sum_dyadic_cell_mass μ hμ i]
  unfold componentEntropyLowerTailMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k.val ∈ J
  · have h := hJ k hk
    simp only [not_le_of_gt h, ite_false, hk, ite_true, zero_add, le_refl]
  · simp only [hk, ite_false, add_zero]
    split_ifs <;> simp

end ExactOverlaps.Entropy
