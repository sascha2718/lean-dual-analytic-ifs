module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
Adapted from the LpSelfSimilar entropy library.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Bounds

set_option maxSynthPendingDepth 3

@[expose] public section

/-!
Conditioning a discrete probability law on a nonzero atom of a statistic. The
conditional law is Mathlib's normalized restriction, with its exact atom masses
and finite support proved here. These are genuine probability laws used by the
finite entropy chain rule.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.Conditioning`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

open MeasureTheory Set
open scoped ENNReal Classical

namespace ExactOverlaps.Entropy

/-- The conditional law given `f = b`, defined only for marginal atoms of positive mass. -/
noncomputable def conditionalPMF {α β : Type*} (p : PMF α) (f : α → β)
    (b : (p.map f).support) : PMF α :=
  p.filter {a | f a = b} (by
    obtain ⟨a, ha, hfa⟩ := (PMF.mem_support_map_iff f p b).mp b.property
    exact ⟨a, hfa, ha⟩)

lemma conditionalPMF_apply {α β : Type*} (p : PMF α) (f : α → β)
    (b : (p.map f).support) (a : α) :
    conditionalPMF p f b a = if f a = b then p a / (p.map f) b else 0 := by
  classical
  unfold conditionalPMF
  rw [PMF.filter_apply]
  have hmass : (∑' a', ({a | f a = b} : Set α).indicator p a') = (p.map f) b := by
    rw [PMF.map_apply]
    apply tsum_congr
    intro a'
    simp [Set.indicator, eq_comm]
  rw [hmass]
  by_cases h : f a = b
  · simp [h, div_eq_mul_inv]
  · simp [h]

lemma conditionalPMF_support {α β : Type*} (p : PMF α) (f : α → β)
    (b : (p.map f).support) :
    (conditionalPMF p f b).support = {a | f a = b} ∩ p.support := PMF.support_filter _

lemma conditionalPMF_support_finite {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (b : (p.map f).support) :
    (conditionalPMF p f b).support.Finite := by
  rw [conditionalPMF_support]
  exact hp.subset (inter_subset_right)

lemma conditionalPMF_toReal {α β : Type*} (p : PMF α) (f : α → β)
    (b : (p.map f).support) (a : α) :
    (conditionalPMF p f b a).toReal =
      if f a = b then (p a).toReal / ((p.map f) b).toReal else 0 := by
  classical
  rw [conditionalPMF_apply]
  split_ifs <;> simp [ENNReal.toReal_div]

lemma marginal_toReal_pos {α β : Type*} (p : PMF α) (f : α → β)
    (b : (p.map f).support) : 0 < ((p.map f) b).toReal :=
  ENNReal.toReal_pos b.property ((p.map f).apply_ne_top b)

lemma marginal_toReal_mul_conditional {α β : Type*} (p : PMF α) (f : α → β)
    (b : (p.map f).support) {a : α} (ha : f a = b) :
    ((p.map f) b).toReal * (conditionalPMF p f b a).toReal = (p a).toReal := by
  rw [conditionalPMF_toReal, ite_eq_left ha]
  exact mul_div_cancel₀ _ (marginal_toReal_pos p f b).ne'

lemma marginal_apply_eq_finite_sum {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (b : β) :
    (p.map f) b = ∑ a ∈ hp.toFinset, if f a = b then p a else 0 := by
  classical
  rw [PMF.map_apply, tsum_eq_sum (s := hp.toFinset)]
  · apply Finset.sum_congr rfl
    intro a _
    simp only [eq_comm]
  · intro a ha
    have hz : p a = 0 := by simpa using ha
    simp [hz]

lemma marginal_toReal_eq_finite_sum {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (b : β) :
    ((p.map f) b).toReal = ∑ a ∈ hp.toFinset, if f a = b then (p a).toReal else 0 := by
  classical
  rw [marginal_apply_eq_finite_sum p hp f b, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  · intro a _
    split_ifs <;> simp [p.apply_ne_top]

lemma atom_toReal_le_marginal {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (a : α) :
    (p a).toReal ≤ ((p.map f) (f a)).toReal := by
  rw [marginal_toReal_eq_finite_sum p hp]
  by_cases ha : a ∈ hp.toFinset
  · calc
      (p a).toReal = (if f a = f a then (p a).toReal else 0) := by simp
      _ ≤ _ := Finset.single_le_sum
        (f := fun a' ↦ if f a' = f a then (p a').toReal else 0)
        (fun _ _ ↦ by split_ifs <;> positivity) ha
  · have hz : p a = 0 := by simpa using ha
    simp only [hz, ENNReal.toReal_zero]
    exact Finset.sum_nonneg (fun _ _ ↦ by split_ifs <;> positivity)

lemma sum_marginal_mul {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (h : β → ℝ) :
    (∑ b ∈ (show (p.map f).support.Finite from by simpa using hp.image f).toFinset,
      ((p.map f) b).toReal * h b) = ∑ a ∈ hp.toFinset, (p a).toReal * h (f a) := by
  let hpf : (p.map f).support.Finite := by simpa using hp.image f
  change (∑ b ∈ hpf.toFinset, _) = _
  simp_rw [marginal_toReal_eq_finite_sum p hp f, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hfa : f a ∈ hpf.toFinset := by
    simpa using (show f a ∈ (p.map f).support from by
      rw [PMF.support_map]
      exact ⟨a, by simpa using ha, rfl⟩)
  rw [Finset.sum_eq_single (f a)]
  · simp
  · intro b _ hba
    simp [Ne.symm hba]
  · exact fun h ↦ (h hfa).elim

/-- Applying a statistic commutes with conditioning on a statistic of its value. -/
lemma map_conditionalPMF {α β γ : Type*} (p : PMF α) (g : α → β) (f : β → γ)
    (b : ((p.map g).map f).support) :
    (conditionalPMF p (f ∘ g) ⟨b, by simpa only [PMF.map_comp] using b.property⟩).map g =
      conditionalPMF (p.map g) f b := by
  have hm : p.map (f ∘ g) = (p.map g).map f := (PMF.map_comp g p f).symm
  ext y
  rw [PMF.map_apply, conditionalPMF_apply]
  simp_rw [conditionalPMF_apply, Function.comp_apply]
  rw [hm]
  by_cases hfy : f y = b
  · rw [ite_eq_left hfy, PMF.map_apply g p y, div_eq_mul_inv, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro a
    by_cases hya : y = g a
    · have hga : f (g a) = b := by rw [← hya]; exact hfy
      simp only [ite_eq_left hya, ite_eq_left hga, div_eq_mul_inv]
    · simp [hya]
  · rw [ite_eq_right hfy]
    apply (tsum_congr _).trans tsum_zero
    intro a
    by_cases hya : y = g a
    · simp [← hya, hfy]
    · simp [hya]

end ExactOverlaps.Entropy
