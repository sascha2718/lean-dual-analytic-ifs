module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
Adapted from the LpSelfSimilar finite entropy library.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.ChainRule
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.EntropySupport

set_option maxSynthPendingDepth 3

/-!
Conditional entropy of one statistic given another. Joint-law chain rules and
normalized conditional laws identify the expected entropy inside the fibers.
This supplies the comparison between fine and coarse grid entropies.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.EntropyComparison`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open scoped Classical

namespace ExactOverlaps.Entropy

lemma conditional_pair_map_entropy {α β γ : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → γ) (b : (p.map f).support) :
    finiteEntropy ((conditionalPMF p f b).map (fun a ↦ (f a, g a)))
      (by simpa using (conditionalPMF_support_finite p hp f b).image (fun a ↦ (f a, g a))) =
    finiteEntropy ((conditionalPMF p f b).map g)
      (by simpa using (conditionalPMF_support_finite p hp f b).image g) := by
  have he : (conditionalPMF p f b).map (fun a ↦ (f a, g a)) =
      ((conditionalPMF p f b).map g).map (fun c ↦ ((b : β), c)) := by
    rw [PMF.map_comp]
    apply map_congr_on_support
    intro a ha
    rw [conditionalPMF_support] at ha
    exact Prod.ext ha.1 rfl
  apply (finiteEntropy_congr he _ _).trans
  exact finiteEntropy_map_of_injective _ _ (fun _ _ h ↦ (Prod.mk.inj h).2)

lemma averageConditionalEntropy_joint_eq {α β γ : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → γ) :
    averageConditionalEntropy (p.map (fun a ↦ (f a, g a)))
      (by simpa using hp.image (fun a ↦ (f a, g a))) Prod.fst =
    (letI : Fintype (p.map f).support :=
      (show (p.map f).support.Finite from by simpa using hp.image f).fintype
    ∑ b : (p.map f).support, ((p.map f) b).toReal *
      finiteEntropy ((conditionalPMF p f b).map g)
        (by simpa using (conditionalPMF_support_finite p hp f b).image g)) := by
  let q := p.map (fun a ↦ (f a, g a))
  have hfst : q.map Prod.fst = p.map f := by simp [q, PMF.map_comp, Function.comp_def]
  let e : (q.map Prod.fst).support ≃ (p.map f).support :=
    Set.equivOfEq (congrArg PMF.support hfst)
  unfold averageConditionalEntropy
  classical
  let : Fintype (p.map f).support :=
    (show (p.map f).support.Finite from by simpa using hp.image f).fintype
  let : Fintype (q.map Prod.fst).support :=
    (show (q.map Prod.fst).support.Finite from by rw [hfst]; simpa using hp.image f).fintype
  apply Fintype.sum_equiv e
    (fun b ↦ ((q.map Prod.fst) b).toReal *
      finiteEntropy (conditionalPMF q Prod.fst b)
        (conditionalPMF_support_finite q (by simpa [q] using hp.image (fun a ↦ (f a, g a))) Prod.fst b))
    (fun b ↦ ((p.map f) b).toReal * finiteEntropy ((conditionalPMF p f b).map g)
      (by simpa using (conditionalPMF_support_finite p hp f b).image g))
  intro b
  have hw : ((q.map Prod.fst) b).toReal = ((p.map f) (e b)).toReal := by
    exact congrArg (fun ν : PMF β ↦ (ν b.val).toReal) hfst
  change ((q.map Prod.fst) b).toReal * _ = _
  rw [hw]
  congr 1
  have hm := map_conditionalPMF p (fun a ↦ (f a, g a)) Prod.fst b
  have he : conditionalPMF q Prod.fst b =
      (conditionalPMF p f (e b)).map (fun a ↦ (f a, g a)) := by
    exact hm.symm
  apply (finiteEntropy_congr he _ _).trans
  exact conditional_pair_map_entropy p hp f g (e b)

/-- Fine entropy minus coarse entropy is bounded by the mean entropy in coarse fibers. -/
theorem entropy_sub_le_conditional_statistic {α β γ : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → γ) :
    finiteEntropy (p.map g) (by simpa using hp.image g) -
      finiteEntropy (p.map f) (by simpa using hp.image f) ≤
    (letI : Fintype (p.map f).support :=
      (show (p.map f).support.Finite from by simpa using hp.image f).fintype
    ∑ b : (p.map f).support, ((p.map f) b).toReal *
      finiteEntropy ((conditionalPMF p f b).map g)
        (by simpa using (conditionalPMF_support_finite p hp f b).image g)) := by
  let q := p.map (fun a ↦ (f a, g a))
  let hq : q.support.Finite := by simpa [q] using hp.image (fun a ↦ (f a, g a))
  have hm := finiteEntropy_map_le q hq Prod.snd
  have hc := finiteEntropy_chain_rule q hq Prod.fst
  rw [conditionalEntropy_eq_average] at hc
  have hfst : q.map Prod.fst = p.map f := by simp [q, PMF.map_comp, Function.comp_def]
  have hsnd : q.map Prod.snd = p.map g := by simp [q, PMF.map_comp, Function.comp_def]
  have hm' := (finiteEntropy_congr hsnd _ (show (p.map g).support.Finite from by
    simpa using hp.image g)).symm.trans_le hm
  have hc' := hc.trans (congrArg (fun z ↦ z + averageConditionalEntropy q hq Prod.fst)
    (finiteEntropy_congr hfst _ (show (p.map f).support.Finite from by simpa using hp.image f)))
  have hav := averageConditionalEntropy_joint_eq p hp f g
  change averageConditionalEntropy q hq Prod.fst = _ at hav
  rw [hav] at hc'
  linarith

lemma finiteEntropy_le_log_of_card_le {α : Type*} (p : PMF α)
    (hp : p.support.Finite) {N : ℕ} (hN : hp.toFinset.card ≤ N) :
    finiteEntropy p hp ≤ Real.log N := by
  have hpos : (0 : ℝ) < hp.toFinset.card := by
    exact_mod_cast Finset.card_pos.mpr (by simp)
  exact (finiteEntropy_le_log_card p hp).trans
    (Real.log_le_log hpos (by exact_mod_cast hN))

/-- A uniform bound on the number of atoms in each fibre bounds conditional entropy. -/
theorem conditionalEntropy_le_log_of_card_le {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) {N : ℕ}
    (hN : ∀ b : (p.map f).support,
      (conditionalPMF_support_finite p hp f b).toFinset.card ≤ N) :
    conditionalEntropy p hp f ≤ Real.log N := by
  classical
  let hpf : (p.map f).support.Finite := by simpa using hp.image f
  let : Fintype (p.map f).support := hpf.fintype
  have hm : ∑ b : (p.map f).support, ((p.map f) b).toReal = 1 := by
    rw [← Finset.sum_subtype hpf.toFinset
      (by simp : ∀ b, b ∈ hpf.toFinset ↔ b ∈ (p.map f).support)
      (fun b ↦ ((p.map f) b).toReal)]
    exact sum_support_toReal _ _
  rw [conditionalEntropy_eq_average]
  unfold averageConditionalEntropy
  calc
    ∑ b : (p.map f).support, ((p.map f) b).toReal *
        finiteEntropy (conditionalPMF p f b) (conditionalPMF_support_finite p hp f b) ≤
        ∑ b : (p.map f).support, ((p.map f) b).toReal * Real.log N := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (finiteEntropy_le_log_of_card_le _ _ (hN b))
        ENNReal.toReal_nonneg
    _ = Real.log N := by rw [← Finset.sum_mul, hm, one_mul]

/-- Forgetting a statistic with at most N possibilities in each fibre costs at most log N. -/
theorem finiteEntropy_le_map_add_log_of_card_le {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) {N : ℕ}
    (hN : ∀ b : (p.map f).support,
      (conditionalPMF_support_finite p hp f b).toFinset.card ≤ N) :
    finiteEntropy p hp ≤ finiteEntropy (p.map f) (by simpa using hp.image f) +
      Real.log N := by
  rw [finiteEntropy_chain_rule p hp f]
  exact add_le_add le_rfl (conditionalEntropy_le_log_of_card_le p hp f hN)

/-- Comparing two statistics only requires a bound on the original support in each fibre. -/
theorem entropy_map_sub_le_log_of_fiber_card_le {α β γ : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → γ) {N : ℕ}
    (hN : ∀ b : β, (hp.toFinset.filter (fun a ↦ f a = b)).card ≤ N) :
    finiteEntropy (p.map g) (by simpa using hp.image g) -
      finiteEntropy (p.map f) (by simpa using hp.image f) ≤ Real.log N := by
  have hfiber (b : (p.map f).support) :
      (conditionalPMF_support_finite p hp f b).toFinset =
        hp.toFinset.filter (fun a ↦ f a = b) := by
    ext a
    simp [conditionalPMF_support, and_comm]
  have h := finiteEntropy_le_map_add_log_of_card_le p hp f (N := N)
    (fun b ↦ by rw [hfiber]; exact hN b)
  have hg := finiteEntropy_map_le p hp g
  linarith

end ExactOverlaps.Entropy
