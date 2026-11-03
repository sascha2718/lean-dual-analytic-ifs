module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
Adapted from the LpSelfSimilar finite entropy library.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Finite

set_option maxSynthPendingDepth 3

/-!
Entropy invariance only needs injectivity on the support. This version applies
to quantization maps, which are never injective on the whole real line but are
injective on sufficiently separated finite sets of atoms.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.EntropySupport`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

open scoped ENNReal

@[expose] public section

namespace ExactOverlaps.Entropy

lemma finiteEntropy_congr {α : Type*} {p q : PMF α} (h : p = q)
    (hp : p.support.Finite) (hq : q.support.Finite) : finiteEntropy p hp = finiteEntropy q hq := by
  subst q
  rfl

lemma map_congr_on_support {α β : Type*} (p : PMF α) {f g : α → β}
    (hfg : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g := by
  classical
  ext b
  simp only [PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · rw [hfg a ha]
  · have hz : p a = 0 := by simpa using ha
    simp [hz]

lemma map_apply_of_injective_support {α β : Type*} (p : PMF α) {f : α → β}
    (hf : Set.InjOn f p.support) {a : α} (ha : a ∈ p.support) :
    p.map f (f a) = p a := by
  classical
  rw [PMF.map_apply, tsum_eq_single a]
  · simp
  · intro b hba
    by_cases hb : b ∈ p.support
    · have hne : f a ≠ f b := fun h ↦ hba (hf hb ha h.symm)
      simp [hne]
    · have hz : p b = 0 := by simpa using hb
      simp [hz]

lemma finiteEntropy_map_of_injective_support {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) {f : α → β} (hf : Set.InjOn f p.support) :
    finiteEntropy (p.map f) (by simpa using hp.image f) = finiteEntropy p hp := by
  classical
  unfold finiteEntropy
  have hfin : (show (p.map f).support.Finite from by simpa using hp.image f).toFinset =
      hp.toFinset.image f := by ext x; simp
  rw [hfin, Finset.sum_image (fun a ha b hb h ↦ hf (by simpa using ha) (by simpa using hb) h)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [map_apply_of_injective_support p hf (by simpa using ha)]

end ExactOverlaps.Entropy
