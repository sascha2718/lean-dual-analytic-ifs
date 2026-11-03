module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.ConditionalConcavity
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.EntropyComparison

set_option maxSynthPendingDepth 3

/-!
# Subadditivity and strong subadditivity of finite entropy

All joint laws below are actual push-forwards of a common finite law.
Conditional concavity supplies subadditivity within each positive-mass fiber;
the exact chain rule then gives strong subadditivity.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.Submodularity`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace ExactOverlaps.Entropy

/-- Mean entropy of `g`, conditional on the positive-mass values of `f`. -/
noncomputable def averageStatisticConditionalEntropy {α β γ : Type*}
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (g : α → γ) : ℝ := by
  classical
  letI : Fintype (p.map f).support :=
    (show (p.map f).support.Finite from by simpa using hp.image f).fintype
  exact ∑ b : (p.map f).support, ((p.map f) b).toReal *
    finiteEntropy ((conditionalPMF p f b).map g)
      (by simpa using (conditionalPMF_support_finite p hp f b).image g)

theorem statisticEntropy_chain_rule {α β γ : Type*}
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (g : α → γ) :
    finiteEntropy (p.map (fun a ↦ (f a, g a)))
      (by simpa using hp.image (fun a ↦ (f a, g a))) =
    finiteEntropy (p.map f) (by simpa using hp.image f) +
      averageStatisticConditionalEntropy p hp f g := by
  have h := finiteEntropy_chain_rule (p.map (fun a ↦ (f a, g a)))
    (by simpa using hp.image (fun a ↦ (f a, g a))) Prod.fst
  rw [conditionalEntropy_eq_average, averageConditionalEntropy_joint_eq p hp f g] at h
  simpa only [PMF.map_comp, Function.comp_def, averageStatisticConditionalEntropy] using h

/-- The entropy of two statistics is at most the sum of their entropies. -/
theorem finiteEntropy_pair_map_le {α β γ : Type*}
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (g : α → γ) :
    finiteEntropy (p.map (fun a ↦ (f a, g a)))
      (by simpa using hp.image (fun a ↦ (f a, g a))) ≤
    finiteEntropy (p.map f) (by simpa using hp.image f) +
      finiteEntropy (p.map g) (by simpa using hp.image g) := by
  rw [statisticEntropy_chain_rule p hp f g]
  exact add_le_add le_rfl (average_conditional_map_entropy_le p hp f g)

lemma averageStatisticConditionalEntropy_pair_le {α β γ δ : Type*}
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (g : α → γ) (h : α → δ) :
    averageStatisticConditionalEntropy p hp f (fun a ↦ (g a, h a)) ≤
      averageStatisticConditionalEntropy p hp f g +
        averageStatisticConditionalEntropy p hp f h := by
  classical
  unfold averageStatisticConditionalEntropy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b _
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left
    (finiteEntropy_pair_map_le (conditionalPMF p f b)
      (conditionalPMF_support_finite p hp f b) g h) ENNReal.toReal_nonneg

/-- Strong subadditivity, written as submodularity for three finite statistics. -/
theorem finiteEntropy_submodular {α β γ δ : Type*}
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (g : α → γ) (h : α → δ) :
    finiteEntropy (p.map (fun a ↦ (f a, (g a, h a))))
        (by simpa using hp.image (fun a ↦ (f a, (g a, h a)))) +
      finiteEntropy (p.map f) (by simpa using hp.image f) ≤
    finiteEntropy (p.map (fun a ↦ (f a, g a)))
        (by simpa using hp.image (fun a ↦ (f a, g a))) +
      finiteEntropy (p.map (fun a ↦ (f a, h a)))
        (by simpa using hp.image (fun a ↦ (f a, h a))) := by
  rw [statisticEntropy_chain_rule p hp f (fun a ↦ (g a, h a)),
    statisticEntropy_chain_rule p hp f g, statisticEntropy_chain_rule p hp f h]
  have hc := averageStatisticConditionalEntropy_pair_le p hp f g h
  linarith

end ExactOverlaps.Entropy
