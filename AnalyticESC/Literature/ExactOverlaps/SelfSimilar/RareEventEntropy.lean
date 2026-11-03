module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.EntropyComparison

set_option maxSynthPendingDepth 3

/-!
Finite entropy bounds when almost all mass lies in a small set. Observing
the exceptional-event indicator costs at most log 2, and only its actual
probability multiplies the entropy bound for the larger support.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.RareEventEntropy`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open scoped Classical BigOperators

namespace ExactOverlaps.Entropy

theorem finiteEntropy_le_bool_partition {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → Bool) (K N : ℕ)
    (hcard : ∀ b : (p.map f).support,
      (conditionalPMF_support_finite p hp f b).toFinset.card ≤ if b.val then N else K) :
    finiteEntropy p hp ≤ Real.log 2 +
      ((p.map f) true).toReal * Real.log N + ((p.map f) false).toReal * Real.log K := by
  let q := p.map f
  let hq : q.support.Finite := by simpa [q] using hp.image f
  let : Fintype q.support := hq.fintype
  have hm : finiteEntropy q hq ≤ Real.log 2 := by
    apply finiteEntropy_le_log_of_card_le
    exact le_trans (Finset.card_le_univ _) (by simp)
  have hsum : (∑ b : q.support, (q b).toReal * Real.log (if b.val then N else K : ℕ)) =
      (q true).toReal * Real.log N + (q false).toReal * Real.log K := by
    rw [← Finset.sum_subtype hq.toFinset
      (by simp : ∀ b, b ∈ hq.toFinset ↔ b ∈ q.support)
      (fun b ↦ (q b).toReal * Real.log (if b then N else K : ℕ))]
    have he : (∑ b ∈ hq.toFinset, (q b).toReal * Real.log (if b then N else K : ℕ)) =
        ∑ b : Bool, (q b).toReal * Real.log (if b then N else K : ℕ) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro b _ hb
      have hb0 : q b = 0 := by simpa using hb
      simp [hb0]
    rw [he, Fintype.sum_bool]
    rfl
  have hc : conditionalEntropy p hp f ≤
      (q true).toReal * Real.log N + (q false).toReal * Real.log K := by
    rw [conditionalEntropy_eq_average]
    unfold averageConditionalEntropy
    apply le_trans _ hsum.le
    apply Finset.sum_le_sum
    intro b _
    exact mul_le_mul_of_nonneg_left
      (finiteEntropy_le_log_of_card_le _ _ (hcard b)) ENNReal.toReal_nonneg
  rw [finiteEntropy_chain_rule p hp f]
  change finiteEntropy q hq + conditionalEntropy p hp f ≤ _
  linarith

/-- Rare mass outside a K-point part of an N-point support has controlled entropy. -/
theorem finiteEntropy_le_log_of_rare_event {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → Bool) {K N : ℕ} (hK : 0 < K) (hN : 0 < N)
    (hgood : (hp.toFinset.filter (fun a ↦ f a = false)).card ≤ K)
    (hall : hp.toFinset.card ≤ N) {δ : ℝ} (hrare : ((p.map f) true).toReal ≤ δ) :
    finiteEntropy p hp ≤ Real.log 2 + Real.log K + δ * Real.log N := by
  have hcard (b : (p.map f).support) :
      (conditionalPMF_support_finite p hp f b).toFinset.card ≤ if b.val then N else K := by
    have he : (conditionalPMF_support_finite p hp f b).toFinset =
        hp.toFinset.filter (fun a ↦ f a = b.val) := by
      ext a
      simp [conditionalPMF_support, and_comm]
    rw [he]
    cases hb : b.val with
    | false => simpa only [hb, Bool.false_eq_true, ↓reduceIte] using hgood
    | true =>
      simpa only [hb, ↓reduceIte] using
        (Finset.card_le_card (Finset.filter_subset (fun a ↦ f a = true) hp.toFinset)).trans hall
  have h := finiteEntropy_le_bool_partition p hp f K N hcard
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hfalse : ((p.map f) false).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top ((p.map f).coe_le_one false)
  have hgood' : ((p.map f) false).toReal * Real.log K ≤ Real.log K := by
    simpa using mul_le_mul_of_nonneg_right hfalse hlogK
  have hbad' := mul_le_mul_of_nonneg_right hrare hlogN
  linarith

end ExactOverlaps.Entropy
