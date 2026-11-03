module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.ConditionalConcavity

set_option maxSynthPendingDepth 3

/-!
# Independent finite laws and their entropy

The independent pair is constructed using `PMF.bind`, with no independence
assumption hidden in the entropy statements. Its support is the product of
the two actual supports, and its entropy is the sum of the two entropies.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.IndependentPair`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace ExactOverlaps.Entropy

noncomputable def independentPair {α β : Type*} (p : PMF α) (q : PMF β) : PMF (α × β) :=
  p.bind (fun a ↦ q.map (Prod.mk a))

lemma independentPair_apply {α β : Type*} (p : PMF α) (q : PMF β) (a : α) (b : β) :
    independentPair p q (a, b) = p a * q b := by
  classical
  unfold independentPair
  rw [PMF.bind_apply, tsum_eq_single a]
  · rw [map_apply_of_injective q (fun _ _ h ↦ (Prod.mk.inj h).2)]
  · intro x hx
    have hz : (q.map (Prod.mk x)) (a, b) = 0 := by
      rw [PMF.map_apply]
      simp [Ne.symm hx]
    simp [hz]

lemma independentPair_support {α β : Type*} (p : PMF α) (q : PMF β) :
    (independentPair p q).support = p.support ×ˢ q.support := by
  ext x
  rcases x with ⟨a, b⟩
  simp [PMF.mem_support_iff, independentPair_apply]

lemma independentPair_support_finite {α β : Type*}
    (p : PMF α) (q : PMF β) (hp : p.support.Finite) (hq : q.support.Finite) :
    (independentPair p q).support.Finite := by
  rw [independentPair_support]
  exact hp.prod hq

lemma independentPair_map_fst {α β : Type*} (p : PMF α) (q : PMF β) :
    (independentPair p q).map Prod.fst = p := by
  simp only [independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change p.bind (fun a ↦ q.map (Function.const β a)) = p
  simp only [PMF.map_const, PMF.bind_pure]

lemma independentPair_map_snd {α β : Type*} (p : PMF α) (q : PMF β) :
    (independentPair p q).map Prod.snd = q := by
  simp only [independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change p.bind (fun _ ↦ q.map id) = q
  simp only [PMF.map_id, PMF.bind_const]

lemma independentPair_map_left {α β γ : Type*}
    (p : PMF α) (q : PMF β) (f : α → γ) :
    (independentPair p q).map (fun x ↦ (f x.1, x.2)) = independentPair (p.map f) q := by
  simp only [independentPair, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def]

lemma independentPair_map_right {α β γ : Type*}
    (p : PMF α) (q : PMF β) (g : β → γ) :
    (independentPair p q).map (fun x ↦ (x.1, g x.2)) = independentPair p (q.map g) := by
  simp only [independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def]

lemma independentPair_assoc {α β γ : Type*}
    (p : PMF α) (q : PMF β) (r : PMF γ) :
    (independentPair p (independentPair q r)).map (fun x ↦ ((x.1, x.2.1), x.2.2)) =
      independentPair (independentPair p q) r := by
  simp only [independentPair, PMF.map_bind, PMF.map_comp, PMF.bind_bind,
    PMF.bind_map, Function.comp_def]

/-- Entropy is additive for the actual independent product law. -/
theorem finiteEntropy_independentPair {α β : Type*}
    (p : PMF α) (q : PMF β) (hp : p.support.Finite) (hq : q.support.Finite) :
    finiteEntropy (independentPair p q) (independentPair_support_finite p q hp hq) =
      finiteEntropy p hp + finiteEntropy q hq := by
  classical
  have hs : (independentPair_support_finite p q hp hq).toFinset =
      hp.toFinset ×ˢ hq.toFinset := by
    ext x
    simp [independentPair_support]
  unfold finiteEntropy
  rw [hs, Finset.sum_product]
  simp only [independentPair_apply, ENNReal.toReal_mul, Real.negMulLog_mul,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, sum_support_toReal,
    one_mul]

end ExactOverlaps.Entropy
