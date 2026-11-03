module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.JointMixture
public import AnalyticESC.Literature.ExactOverlaps.Entropy.Submodularity

set_option maxSynthPendingDepth 3

/-!
# Concavity of finite conditional entropy

Remember the mixture label and apply strong subadditivity to the coarse
statistic, the label, and the sampled value. Forgetting the label increases
conditional entropy, including when some mixture weights vanish.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.ConditionalMixture`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace ExactOverlaps.Entropy

lemma conditionalEntropy_eq_entropy_sub {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) :
    conditionalEntropy p hp f =
      finiteEntropy p hp - finiteEntropy (p.map f) (by simpa using hp.image f) := by
  have h := finiteEntropy_chain_rule p hp f
  linarith

/-- Conditional entropy is concave under the actual finite mixture of laws. -/
theorem average_conditionalEntropy_le_bind {ι α β : Type*} [Fintype ι]
    (p : PMF ι) (q : ι → PMF α) (hq : ∀ i, (q i).support.Finite) (f : α → β) :
    (∑ i, (p i).toReal * conditionalEntropy (q i) (hq i) f) ≤
      conditionalEntropy (p.bind q) (bind_support_finite p q hq) f := by
  let w := jointMixture p q
  let hw := jointMixture_support_finite p q hq
  let qf : ι → PMF β := fun i ↦ (q i).map f
  let hqf : ∀ i, (qf i).support.Finite := fun i ↦ by simpa [qf] using (hq i).image f
  have hf : w.map (fun a ↦ f a.2) = (p.bind q).map f := by
    rw [← jointMixture_map_snd p q, PMF.map_comp]
    rfl
  have hfi : w.map (fun a ↦ (f a.2, a.1)) =
      (jointMixture p qf).map Prod.swap := by
    rw [← jointMixture_map_right p q f, PMF.map_comp]
    rfl
  have hfa : w.map (fun a ↦ (f a.2, a.2)) =
      (p.bind q).map (fun a ↦ (f a, a)) := by
    rw [← jointMixture_map_snd p q, PMF.map_comp]
    rfl
  have hentTriple := finiteEntropy_map_of_injective w hw
    (show Function.Injective (fun a : ι × α ↦ (f a.2, (a.1, a.2))) from
      fun _ _ h ↦ congrArg Prod.snd h)
  have hentFI : finiteEntropy (w.map (fun a ↦ (f a.2, a.1)))
      (by simpa using hw.image (fun a ↦ (f a.2, a.1))) =
        finiteEntropy (jointMixture p qf) (jointMixture_support_finite p qf hqf) := by
    apply (finiteEntropy_congr hfi _ _).trans
    exact finiteEntropy_map_of_injective _ _ (Equiv.prodComm ι β).injective
  have hentFA : finiteEntropy (w.map (fun a ↦ (f a.2, a.2)))
      (by simpa using hw.image (fun a ↦ (f a.2, a.2))) =
        finiteEntropy (p.bind q) (bind_support_finite p q hq) := by
    apply (finiteEntropy_congr hfa _ _).trans
    exact finiteEntropy_map_of_injective _ _ (fun _ _ h ↦ congrArg Prod.snd h)
  have h := finiteEntropy_submodular w hw (fun a ↦ f a.2) Prod.fst Prod.snd
  rw [hentTriple, hentFI, hentFA] at h
  have hentF := finiteEntropy_congr hf
    (show (w.map (fun a ↦ f a.2)).support.Finite from by simpa using hw.image (fun a ↦ f a.2))
    (show ((p.bind q).map f).support.Finite from by
      simpa using (bind_support_finite p q hq).image f)
  rw [hentF, finiteEntropy_jointMixture p q hq, finiteEntropy_jointMixture p qf hqf] at h
  simp_rw [conditionalEntropy_eq_entropy_sub, mul_sub, Finset.sum_sub_distrib]
  change (∑ i, (p i).toReal * finiteEntropy (q i) (hq i)) -
      (∑ i, (p i).toReal * finiteEntropy (qf i) (hqf i)) ≤ _
  linarith

end ExactOverlaps.Entropy
