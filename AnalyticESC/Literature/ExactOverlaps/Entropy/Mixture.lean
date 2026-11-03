module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.ChainRule
public import Mathlib.Analysis.Convex.Jensen

set_option maxSynthPendingDepth 3

/-!
# Concavity of finite Shannon entropy

The mixture is an actual probability law. Every component has proved finite
support, and the entropy comparison is obtained from the concavity of
`Real.negMulLog` on nonnegative real numbers.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.Mixture`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace ExactOverlaps.Entropy

lemma finiteEntropy_eq_sum_of_support_subset {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (s : Finset α) (hs : p.support ⊆ s) :
    finiteEntropy p hp = ∑ a ∈ s, Real.negMulLog (p a).toReal := by
  classical
  apply Finset.sum_subset
  · intro a ha
    exact hs (by simpa using ha)
  · intro a _ ha
    have hzero : p a = 0 := by simpa using ha
    simp [hzero]

lemma sum_pmf_toReal {ι : Type*} [Fintype ι] (p : PMF ι) :
    ∑ i, (p i).toReal = 1 := by
  have h : ∑ i, p i = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [← ENNReal.toReal_sum (fun i _ ↦ p.apply_ne_top i), h, ENNReal.toReal_one]

/-- Concavity for an explicitly identified finite mixture, with arbitrary real weights. -/
theorem finiteEntropy_mixture_le {ι α : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (q : ι → PMF α) (hq : ∀ i, (q i).support.Finite)
    (p : PMF α) (hp : p.support.Finite)
    (hmix : ∀ a, (p a).toReal = ∑ i, w i * (q i a).toReal) :
    (∑ i, w i * finiteEntropy (q i) (hq i)) ≤ finiteEntropy p hp := by
  classical
  let s : Finset α := hp.toFinset ∪ Finset.univ.biUnion (fun i ↦ (hq i).toFinset)
  have hps : p.support ⊆ s := by
    intro a ha
    exact Finset.mem_union_left _ (by simpa using ha)
  have hqs (i : ι) : (q i).support ⊆ s := by
    intro a ha
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simpa using ha⟩
  rw [finiteEntropy_eq_sum_of_support_subset p hp s hps]
  simp_rw [finiteEntropy_eq_sum_of_support_subset _ _ s (hqs _), Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  rw [hmix]
  simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.le_map_sum
    (t := Finset.univ) (w := w) (p := fun i ↦ (q i a).toReal)
    (fun i _ ↦ hw i) hwsum (fun i _ ↦ ENNReal.toReal_nonneg)

lemma bind_support_finite {ι α : Type*} [Fintype ι] (p : PMF ι)
    (q : ι → PMF α) (hq : ∀ i, (q i).support.Finite) : (p.bind q).support.Finite := by
  rw [PMF.support_bind]
  exact (Set.finite_iUnion hq).subset (by
    intro a ha
    obtain ⟨i, _, hi⟩ := Set.mem_iUnion₂.mp ha
    exact Set.mem_iUnion.mpr ⟨i, hi⟩)

lemma bind_toReal {ι α : Type*} [Fintype ι] (p : PMF ι) (q : ι → PMF α) (a : α) :
    (p.bind q a).toReal = ∑ i, (p i).toReal * (q i a).toReal := by
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro i _
    exact ENNReal.mul_ne_top (p.apply_ne_top i) ((q i).apply_ne_top a)

/-- Mixing finite laws cannot decrease the mean of their entropies. -/
theorem average_finiteEntropy_le_bind {ι α : Type*} [Fintype ι]
    (p : PMF ι) (q : ι → PMF α) (hq : ∀ i, (q i).support.Finite) :
    (∑ i, (p i).toReal * finiteEntropy (q i) (hq i)) ≤
      finiteEntropy (p.bind q) (bind_support_finite p q hq) :=
  finiteEntropy_mixture_le (fun i ↦ (p i).toReal) (fun _ ↦ ENNReal.toReal_nonneg)
    (sum_pmf_toReal p) q hq _ _ (bind_toReal p q)

end ExactOverlaps.Entropy
