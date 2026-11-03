module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
Adapted from the LpSelfSimilar entropy library.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Conditioning

set_option maxSynthPendingDepth 3

@[expose] public section

/-!
The finite Shannon chain rule for a deterministic statistic. Conditional entropy
is first written as a weighted sum over the original atoms, which avoids
arbitrary choices on null conditioning events. Its probabilities are the
normalized conditional probabilities proved in `Entropy/Conditioning`.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.ChainRule`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

open Real
open scoped ENNReal Classical

namespace ExactOverlaps.Entropy

/-- Shannon entropy remaining after observing the statistic `f`. -/
noncomputable def conditionalEntropy {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) : ℝ :=
  ∑ a ∈ hp.toFinset, (p a).toReal * Real.log (((p.map f) (f a)).toReal / (p a).toReal)

lemma finiteEntropy_map_eq_sum_log_marginal {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) :
    finiteEntropy (p.map f) (by simpa using hp.image f) =
      ∑ a ∈ hp.toFinset, -(p a).toReal * Real.log ((p.map f) (f a)).toReal := by
  simpa only [finiteEntropy, Real.negMulLog, mul_neg, neg_mul] using
    sum_marginal_mul p hp f (fun b ↦ -Real.log ((p.map f) b).toReal)

lemma conditionalEntropy_nonneg {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) : 0 ≤ conditionalEntropy p hp f := by
  apply Finset.sum_nonneg
  intro a ha
  have hpa : 0 < (p a).toReal :=
    ENNReal.toReal_pos (by simpa using ha) (p.apply_ne_top a)
  apply mul_nonneg hpa.le
  apply Real.log_nonneg
  exact (one_le_div hpa).mpr (atom_toReal_le_marginal p hp f a)

/-- Exact entropy chain rule `H(X) = H(f(X)) + H(X | f(X))`. -/
theorem finiteEntropy_chain_rule {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) :
    finiteEntropy p hp =
      finiteEntropy (p.map f) (by simpa using hp.image f) + conditionalEntropy p hp f := by
  have hm := sum_marginal_mul p hp f (fun b ↦ -Real.log ((p.map f) b).toReal)
  have he : finiteEntropy (p.map f) (by simpa using hp.image f) =
      ∑ a ∈ hp.toFinset, -(p a).toReal * Real.log ((p.map f) (f a)).toReal := by
    simpa only [finiteEntropy, Real.negMulLog, mul_neg, neg_mul] using hm
  rw [he, conditionalEntropy, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have hpa : 0 < (p a).toReal :=
    ENNReal.toReal_pos (by simpa using ha) (p.apply_ne_top a)
  have hfa : 0 < ((p.map f) (f a)).toReal :=
    hpa.trans_le (atom_toReal_le_marginal p hp f a)
  rw [Real.log_div hfa.ne' hpa.ne']
  unfold Real.negMulLog
  ring

/-- Applying a deterministic statistic cannot increase finite Shannon entropy. -/
lemma finiteEntropy_map_le {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) :
    finiteEntropy (p.map f) (by simpa using hp.image f) ≤ finiteEntropy p hp := by
  conv_rhs => rw [finiteEntropy_chain_rule p hp f]
  exact le_add_of_nonneg_right (conditionalEntropy_nonneg p hp f)

lemma marginal_mul_conditional_entropy {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (b : (p.map f).support) :
    ((p.map f) b).toReal *
      finiteEntropy (conditionalPMF p f b) (conditionalPMF_support_finite p hp f b) =
      ∑ a ∈ hp.toFinset, if f a = b then
        (p a).toReal * Real.log (((p.map f) b).toReal / (p a).toReal) else 0 := by
  let q := conditionalPMF p f b
  let hq := conditionalPMF_support_finite p hp f b
  have hsub : hq.toFinset ⊆ hp.toFinset := by
    intro a ha
    have hmem : a ∈ q.support := by simpa using ha
    rw [conditionalPMF_support] at hmem
    simpa using hmem.2
  have he : finiteEntropy q hq = ∑ a ∈ hp.toFinset, Real.negMulLog (q a).toReal := by
    apply Finset.sum_subset hsub
    intro a _ ha
    have hz : q a = 0 := by simpa using ha
    simp [hz]
  change ((p.map f) b).toReal * finiteEntropy q hq = _
  rw [he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hpa : 0 < (p a).toReal :=
    ENNReal.toReal_pos (by simpa using ha) (p.apply_ne_top a)
  have hpb := marginal_toReal_pos p f b
  change ((p.map f) b).toReal * Real.negMulLog (conditionalPMF p f b a).toReal = _
  rw [conditionalPMF_toReal]
  by_cases hfa : f a = b
  · rw [ite_eq_left hfa, ite_eq_left hfa, Real.negMulLog,
      Real.log_div hpa.ne' hpb.ne', Real.log_div hpb.ne' hpa.ne']
    field_simp
    ring
  · simp [hfa]

/-- Expected Shannon entropy of the normalized conditional laws. -/
noncomputable def averageConditionalEntropy {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) : ℝ :=
  letI : Fintype (p.map f).support :=
    (show (p.map f).support.Finite from by simpa using hp.image f).fintype
  ∑ b : (p.map f).support, ((p.map f) b).toReal *
    finiteEntropy (conditionalPMF p f b) (conditionalPMF_support_finite p hp f b)

/-- The flat atom formula is exactly the average entropy of conditional probability laws. -/
lemma conditionalEntropy_eq_average {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) :
    conditionalEntropy p hp f = averageConditionalEntropy p hp f := by
  unfold averageConditionalEntropy
  simp_rw [marginal_mul_conditional_entropy p hp f]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  let b : (p.map f).support := ⟨f a, by
    rw [PMF.support_map]
    exact ⟨a, by simpa using ha, rfl⟩⟩
  symm
  rw [Finset.sum_eq_single b]
  · simp [b]
  · intro c _ hcb
    have hne : f a ≠ c := fun h ↦ hcb (Subtype.ext h.symm)
    simp [hne]
  · simp

end ExactOverlaps.Entropy
