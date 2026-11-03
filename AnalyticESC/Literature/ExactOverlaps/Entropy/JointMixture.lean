module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.ConditionalConcavity

set_option maxSynthPendingDepth 3

/-!
# Joint laws of a finite mixture

Remembering both the selected label and the sampled value gives an actual
joint law. Its entropy is label entropy plus mean component entropy.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.JointMixture`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace ExactOverlaps.Entropy

noncomputable def jointMixture {ι α : Type*} (p : PMF ι) (q : ι → PMF α) : PMF (ι × α) :=
  p.bind (fun i ↦ (q i).map (Prod.mk i))

lemma jointMixture_apply {ι α : Type*} (p : PMF ι) (q : ι → PMF α) (i : ι) (a : α) :
    jointMixture p q (i, a) = p i * q i a := by
  classical
  unfold jointMixture
  rw [PMF.bind_apply, tsum_eq_single i]
  · rw [map_apply_of_injective (q i) (fun _ _ h ↦ (Prod.mk.inj h).2)]
  · intro j hj
    have hz : ((q j).map (Prod.mk j)) (i, a) = 0 := by
      rw [PMF.map_apply]
      simp [Ne.symm hj]
    simp [hz]

lemma jointMixture_support_finite {ι α : Type*} [Fintype ι]
    (p : PMF ι) (q : ι → PMF α) (hq : ∀ i, (q i).support.Finite) :
    (jointMixture p q).support.Finite :=
  bind_support_finite p _ (fun i ↦ by simpa using (hq i).image (Prod.mk i))

lemma jointMixture_map_fst {ι α : Type*} (p : PMF ι) (q : ι → PMF α) :
    (jointMixture p q).map Prod.fst = p := by
  simp only [jointMixture, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change p.bind (fun i ↦ (q i).map (Function.const α i)) = p
  simp only [PMF.map_const, PMF.bind_pure]

lemma jointMixture_map_snd {ι α : Type*} (p : PMF ι) (q : ι → PMF α) :
    (jointMixture p q).map Prod.snd = p.bind q := by
  simp only [jointMixture, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change p.bind (fun i ↦ (q i).map id) = p.bind q
  simp only [PMF.map_id]

lemma jointMixture_map_right {ι α β : Type*} (p : PMF ι) (q : ι → PMF α) (f : α → β) :
    (jointMixture p q).map (fun x ↦ (x.1, f x.2)) =
      jointMixture p (fun i ↦ (q i).map f) := by
  simp only [jointMixture, PMF.map_bind, PMF.map_comp, Function.comp_def]

lemma sum_pmf_toReal_of_support_subset {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (s : Finset α) (hs : p.support ⊆ s) :
    ∑ a ∈ s, (p a).toReal = 1 := by
  rw [← sum_support_toReal p hp]
  symm
  apply Finset.sum_subset
  · intro a ha
    exact hs (by simpa using ha)
  · intro a _ ha
    have hz : p a = 0 := by simpa using ha
    simp [hz]

/-- Exact entropy of the mixture label together with its sampled value. -/
theorem finiteEntropy_jointMixture {ι α : Type*} [Fintype ι]
    (p : PMF ι) (q : ι → PMF α) (hq : ∀ i, (q i).support.Finite) :
    finiteEntropy (jointMixture p q) (jointMixture_support_finite p q hq) =
      finiteEntropy p (Set.toFinite _) + ∑ i, (p i).toReal * finiteEntropy (q i) (hq i) := by
  classical
  let s : Finset α := Finset.univ.biUnion (fun i ↦ (hq i).toFinset)
  have hqs (i : ι) : (q i).support ⊆ s := by
    intro a ha
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simpa using ha⟩
  have hjs : (jointMixture p q).support ⊆ (Finset.univ ×ˢ s : Finset (ι × α)) := by
    rintro ⟨i, a⟩ ha
    have hqa : a ∈ (q i).support := by
      have ha' : p i * q i a ≠ 0 := by simpa [PMF.mem_support_iff, jointMixture_apply] using ha
      exact fun hz ↦ ha' (by simp [hz])
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hqs i hqa⟩
  rw [finiteEntropy_eq_sum_of_support_subset _ _ _ hjs, Finset.sum_product]
  have hi (i : ι) :
      (∑ a ∈ s, Real.negMulLog ((jointMixture p q) (i, a)).toReal) =
        Real.negMulLog (p i).toReal + (p i).toReal * finiteEntropy (q i) (hq i) := by
    simp only [jointMixture_apply, ENNReal.toReal_mul, Real.negMulLog_mul,
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [sum_pmf_toReal_of_support_subset (q i) (hq i) s (hqs i), one_mul,
      ← finiteEntropy_eq_sum_of_support_subset (q i) (hq i) s (hqs i)]
  simp_rw [hi]
  rw [Finset.sum_add_distrib, finiteEntropy_eq_sum_of_support_subset p (Set.toFinite _)
    Finset.univ (by simp)]

end ExactOverlaps.Entropy
