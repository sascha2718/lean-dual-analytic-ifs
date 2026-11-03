module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.RareEventEntropy
public import AnalyticESC.Literature.ExactOverlaps.Entropy.Mixture

set_option maxSynthPendingDepth 3

/-!
# Entropy near a small set

Retaining the actual entropy of the exceptional-event indicator gives an
error tending to zero with the exceptional mass, uniformly for a fixed
finite support bound.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.RareConcentration`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open scoped BigOperators ENNReal Classical
open Set Filter

namespace ExactOverlaps.Entropy

lemma finiteEntropy_bool (p : PMF Bool) (hp : p.support.Finite) :
    finiteEntropy p hp = Real.negMulLog (p true).toReal +
      Real.negMulLog (1 - (p true).toReal) := by
  have hs := sum_pmf_toReal p
  simp only [Fintype.sum_bool] at hs
  have hf : (p false).toReal = 1 - (p true).toReal := by linarith
  rw [finiteEntropy_eq_sum_of_support_subset p hp Finset.univ
    (fun a _ ↦ Finset.mem_univ a)]
  simp only [Fintype.sum_bool, hf]

theorem finiteEntropy_le_binary_error {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → Bool) {K N : ℕ} (hK : 0 < K)
    (hgood : (hp.toFinset.filter (fun a ↦ f a = false)).card ≤ K)
    (hall : hp.toFinset.card ≤ N) :
    finiteEntropy p hp ≤ Real.log K + Real.negMulLog ((p.map f) true).toReal +
      Real.negMulLog (1 - ((p.map f) true).toReal) +
      ((p.map f) true).toReal * Real.log N := by
  let q := p.map f
  let hq : q.support.Finite := by simpa [q] using hp.image f
  let : Fintype q.support := hq.fintype
  have hcard (b : q.support) :
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
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  have hfalse : (q false).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (q.coe_le_one false)
  have hb := mul_le_mul_of_nonneg_right hfalse hlogK
  have he := finiteEntropy_chain_rule p hp f
  have hqent := finiteEntropy_bool q hq
  change finiteEntropy p hp = finiteEntropy q hq + conditionalEntropy p hp f at he
  change _ ≤ Real.log K + Real.negMulLog (q true).toReal +
    Real.negMulLog (1 - (q true).toReal) + (q true).toReal * Real.log N
  linarith

lemma exists_binary_entropy_error_bound (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) δ,
      Real.negMulLog t + Real.negMulLog (1 - t) + t * Real.log N < ε := by
  have hc : Continuous (fun t : ℝ ↦
      Real.negMulLog t + Real.negMulLog (1 - t) + t * Real.log N) := by fun_prop
  have he : ∀ᶠ t in nhds (0 : ℝ),
      Real.negMulLog t + Real.negMulLog (1 - t) + t * Real.log N < ε :=
    hc.continuousAt.eventually_lt_const (by simpa using hε)
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ / 2, half_pos hδ, fun t ht ↦ hd ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
  linarith [ht.2]

/-- Uniformly vanishing entropy loss as mass outside a K-point set tends to zero. -/
theorem exists_rare_mass_entropy_bound (K N : ℕ) (hK : 0 < K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {α : Type*} (p : PMF α) (hp : p.support.Finite) (f : α → Bool),
      (hp.toFinset.filter (fun a ↦ f a = false)).card ≤ K →
      hp.toFinset.card ≤ N → ((p.map f) true).toReal ≤ δ →
      finiteEntropy p hp < Real.log K + ε := by
  obtain ⟨δ, hδ, hd⟩ := exists_binary_entropy_error_bound N hε
  refine ⟨δ, hδ, ?_⟩
  intro α p hp f hgood hall hrare
  have hb := finiteEntropy_le_binary_error p hp f hK hgood hall
  have h := hd ((p.map f) true).toReal ⟨ENNReal.toReal_nonneg, hrare⟩
  linarith

end ExactOverlaps.Entropy
