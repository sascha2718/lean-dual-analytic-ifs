module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Mixture

set_option maxSynthPendingDepth 3

/-!
# Disintegration and entropy concavity for a finite statistic

The probability law on positive-mass labels has the original atom weights.
Mixing the normalized conditional laws exactly reconstructs the original law.
After applying any statistic, entropy concavity gives the conditional-entropy
inequality used in information comparisons.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.ConditionalConcavity`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace ExactOverlaps.Entropy

/-- A law viewed on its positive-mass support, with its original weights. -/
noncomputable def supportLaw {α : Type*} (p : PMF α) : PMF p.support :=
  ⟨fun a ↦ p a, ENNReal.summable.hasSum_iff.mpr
    ((tsum_subtype_eq_of_support_subset (Set.Subset.refl p.support)).trans p.tsum_coe)⟩

lemma supportLaw_apply {α : Type*} (p : PMF α) (a : p.support) :
    supportLaw p a = p a := rfl

lemma supportLaw_map_val {α : Type*} (p : PMF α) :
    (supportLaw p).map Subtype.val = p := by
  classical
  ext a
  rw [PMF.map_apply]
  change (∑' b : p.support, if a = b.val then p b else 0) = p a
  calc
    _ = ∑' b, if a = b then p b else 0 :=
      tsum_subtype_eq_of_support_subset (by
        intro b hb
        by_contra h
        have hz : p b = 0 := by simpa using h
        simp [hz] at hb)
    _ = _ := by simp

/-- The normalized conditional laws reconstruct the original probability law. -/
theorem bind_conditionalPMF {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) :
    (supportLaw (p.map f)).bind (conditionalPMF p f) = p := by
  classical
  let : Fintype (p.map f).support :=
    (show (p.map f).support.Finite from by simpa using hp.image f).fintype
  ext a
  apply (ENNReal.toReal_eq_toReal_iff'
    (((supportLaw (p.map f)).bind (conditionalPMF p f)).apply_ne_top a)
    (p.apply_ne_top a)).mp
  rw [bind_toReal]
  simp only [supportLaw_apply]
  by_cases ha : a ∈ p.support
  · have hb : f a ∈ (p.map f).support := by
      rw [PMF.support_map]
      exact ⟨a, ha, rfl⟩
    rw [Finset.sum_eq_single (⟨f a, hb⟩ : (p.map f).support)]
    · exact marginal_toReal_mul_conditional p f _ rfl
    · intro b _ hne
      have hne' : f a ≠ b.val := fun h ↦ hne (Subtype.ext h.symm)
      simp [conditionalPMF_toReal, hne']
    · simp
  · have hz : p a = 0 := by simpa using ha
    simp [conditionalPMF_toReal, hz]

/-- Observing a statistic cannot increase the mean entropy of another statistic. -/
theorem average_conditional_map_entropy_le {α β γ : Type*}
    (p : PMF α) (hp : p.support.Finite) (f : α → β) (g : α → γ) :
    (letI : Fintype (p.map f).support :=
      (show (p.map f).support.Finite from by simpa using hp.image f).fintype
    ∑ b : (p.map f).support, ((p.map f) b).toReal *
      finiteEntropy ((conditionalPMF p f b).map g)
        (by simpa using (conditionalPMF_support_finite p hp f b).image g)) ≤
      finiteEntropy (p.map g) (by simpa using hp.image g) := by
  let : Fintype (p.map f).support :=
    (show (p.map f).support.Finite from by simpa using hp.image f).fintype
  have h := average_finiteEntropy_le_bind (supportLaw (p.map f))
    (fun b ↦ (conditionalPMF p f b).map g)
    (fun b ↦ by simpa using (conditionalPMF_support_finite p hp f b).image g)
  have hm : (supportLaw (p.map f)).bind (fun b ↦ (conditionalPMF p f b).map g) =
      p.map g := by
    rw [← PMF.map_bind, bind_conditionalPMF p hp f]
  simpa only [supportLaw_apply, hm] using h

end ExactOverlaps.Entropy
