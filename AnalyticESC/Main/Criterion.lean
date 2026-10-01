module

public import AnalyticESC.Main.Dichotomy

@[expose] public section

/-!
# Proposition 1.8

An explicit sufficient condition for the hypothesis of Theorem 1.5: if the distortions
`f_i''/f_i'` of different maps are `α`-apart somewhere on `[0,1]` and `α > 2β c_max/(1 - c_max)`,
then dual natural projections of distinct words of equal length differ, and `Φ` satisfies the
SESC.

The first term of the series (1.4) for `H_w` is `f_a''/f_a'`, where `a` is the first letter of
`w`, and the remaining terms sum to at most `β c_max/(1 - c_max)` on `I`. Hence words with
different first letters have different dual projections at a point of `I`, and, by the identity
theorem, on every nondegenerate subinterval of `I`. Distinct words of equal length are reduced to
this case by the cocycle identity for their longest common prefix.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- `β = sup_{x ∈ [0,1], i} |f_i''/f_i'(x)|` (Proposition 1.8). -/
noncomputable def beta : ℝ := ⨆ (x : I) (i : Fin N), ‖Φ.nonlin i ((x : ℝ) : ℂ)‖

theorem beta_nonneg : 0 ≤ Φ.beta :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _

private theorem bddAbove_beta :
    BddAbove (range fun x : I => ⨆ i : Fin N, ‖Φ.nonlin i ((x : ℝ) : ℂ)‖) := by
  obtain ⟨M, hM0, hM⟩ := Φ.exists_nonlin_bound
  refine ⟨M, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact Real.iSup_le (fun i => hM i _ (subset_closure (ofReal_mem_nbhd Φ.ε_pos x.2))) hM0

theorem norm_nonlin_le_beta (i : Fin N) {x : ℝ} (hx : x ∈ I) : ‖Φ.nonlin i x‖ ≤ Φ.beta :=
  le_ciSup_of_le Φ.bddAbove_beta ⟨x, hx⟩
    (le_ciSup (f := fun i : Fin N => ‖Φ.nonlin i ((x : ℝ) : ℂ)‖) (finite_range _).bddAbove i)

/-- The term with index `n` of (1.4) is at most `β c_max^n` at the points of `I`. -/
theorem norm_dualTerm_le_beta (w : Word N) (n : ℕ) {x : ℝ} (hx : x ∈ I) :
    ‖Φ.dualTerm w n x‖ ≤ Φ.beta * Φ.cmax ^ n := by
  cases h : w.get? n with
  | none =>
    rw [Φ.dualTerm_of_get?_eq_none h, norm_zero]
    exact mul_nonneg Φ.beta_nonneg (pow_nonneg Φ.cmax_nonneg n)
  | some i =>
    rw [Φ.dualTerm_of_get?_eq_some h, norm_mul]
    have hxn : (x : ℂ) ∈ closure (nbhd ε) := subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)
    have hlen : (w.take n).length = n := by
      have h1 := Word.length_take w n
      have h2 : (n : ℕ∞) < w.length := (Word.isSome_get?_iff w n).1 (by simp [h])
      rw [min_eq_left h2.le] at h1
      exact_mod_cast h1
    have h1 : ‖Φ.nonlin i (Φ.comp (w.take n).reverse x)‖ ≤ Φ.beta := by
      rw [Φ.comp_ofReal _ hx]
      exact Φ.norm_nonlin_le_beta i (Φ.re_comp_mem_I _ hx)
    have h2 := Φ.norm_deriv_comp_le (w.take n).reverse hxn
    rw [List.length_reverse, hlen] at h2
    exact mul_le_mul h1 h2 (norm_nonneg _) Φ.beta_nonneg

/-- If `w` begins with `a`, then `|H_w(x) - (f_a''/f_a')(x)| ≤ β c_max/(1 - c_max)` on `I`. -/
theorem norm_dualProj_sub_nonlin_le {w : Word N} {a : Fin N} (h : w.get? 0 = some a) {x : ℝ}
    (hx : x ∈ I) : ‖Φ.dualProj w x - Φ.nonlin a x‖ ≤ Φ.beta * Φ.cmax / (1 - Φ.cmax) := by
  have hxn : (x : ℂ) ∈ closure (nbhd ε) := subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)
  have h0 : Φ.dualTerm w 0 x = Φ.nonlin a x := by
    rw [Φ.dualTerm_of_get?_eq_some h]
    cases w <;> simp
  rw [dualProj, (Φ.summable_dualTerm w hxn).tsum_eq_zero_add, h0, add_sub_cancel_left,
    div_eq_mul_inv]
  have hg : HasSum (fun n : ℕ => Φ.beta * Φ.cmax * Φ.cmax ^ n)
      (Φ.beta * Φ.cmax * (1 - Φ.cmax)⁻¹) :=
    (hasSum_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left _
  refine tsum_of_norm_bounded hg fun n => ?_
  calc _ ≤ Φ.beta * Φ.cmax ^ (n + 1) := Φ.norm_dualTerm_le_beta w (n + 1) hx
    _ = _ := by ring

/-- Words with different first letters have different dual projections at a point of `I`. -/
theorem exists_dualProj_ne_of_get?_zero {α : ℝ}
    (hsep : ∀ i j : Fin N, i ≠ j → ∃ x ∈ I, α ≤ ‖Φ.nonlin i x - Φ.nonlin j x‖)
    (hlt : 2 * Φ.beta * Φ.cmax / (1 - Φ.cmax) < α) {i j : Word N} {a b : Fin N}
    (hi : i.get? 0 = some a) (hj : j.get? 0 = some b) (hab : a ≠ b) :
    ∃ x ∈ I, Φ.dualProj i x ≠ Φ.dualProj j x := by
  obtain ⟨x, hx, hαx⟩ := hsep a b hab
  refine ⟨x, hx, fun heq => ?_⟩
  have h1 := Φ.norm_dualProj_sub_nonlin_le hi hx
  have h2 := Φ.norm_dualProj_sub_nonlin_le hj hx
  have key : ‖Φ.nonlin a x - Φ.nonlin b x‖ ≤
      ‖Φ.dualProj i x - Φ.nonlin a x‖ + ‖Φ.dualProj j x - Φ.nonlin b x‖ := by
    calc ‖Φ.nonlin a x - Φ.nonlin b x‖ =
          ‖-(Φ.dualProj i x - Φ.nonlin a x) + (Φ.dualProj j x - Φ.nonlin b x)‖ := by
          rw [heq]; ring_nf
      _ ≤ _ := by rw [← norm_neg (Φ.dualProj i x - _)]; exact norm_add_le _ _
  have h2β : 2 * Φ.beta * Φ.cmax / (1 - Φ.cmax) = 2 * (Φ.beta * Φ.cmax / (1 - Φ.cmax)) := by
    ring
  linarith

/-- A word without a first letter is empty. -/
private theorem eq_fin_nil_of_get?_zero_eq_none {w : Word N} (h : w.get? 0 = none) :
    w = .fin [] := by
  cases w with
  | fin w => simpa using h
  | inf w => simp at h

/-- Distinct words of equal length have different dual projections at a point of `I`. -/
theorem exists_dualProj_ne {α : ℝ} (hN : 0 < N)
    (hsep : ∀ i j : Fin N, i ≠ j → ∃ x ∈ I, α ≤ ‖Φ.nonlin i x - Φ.nonlin j x‖)
    (hlt : 2 * Φ.beta * Φ.cmax / (1 - Φ.cmax) < α) {i j : Word N} (hij : i ≠ j)
    (hlen : i.length = j.length) : ∃ x ∈ I, Φ.dualProj i x ≠ Φ.dualProj j x := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (Word.commonPrefixLength_lt_top hij).ne
  obtain ⟨u, i', j', hu, rfl, rfl⟩ := Word.exists_eq_prepend hm.le
  -- the first letters of `i'` and `j'` differ
  have hfirst : ¬ ((i'.get? 0).isSome ∧ i'.get? 0 = j'.get? 0) := by
    intro h
    have : ((m + 1 : ℕ) : ℕ∞) ≤ (i'.prepend u).commonPrefixLength (j'.prepend u) := by
      rw [Word.le_commonPrefixLength_iff]
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact Word.le_commonPrefixLength_iff.1 hm.le k hk
      · have e1 := Word.get?_prepend_add u i' 0
        have e2 := Word.get?_prepend_add u j' 0
        rw [add_zero, hu] at e1 e2
        rw [e1, e2]
        exact h
    rw [← hm] at this
    norm_cast at this
    omega
  have hlen' : i'.length = j'.length := by
    rw [Word.length_prepend, Word.length_prepend] at hlen
    exact WithTop.add_left_cancel (ENat.natCast_ne_top _) hlen
  obtain ⟨c, d, hc, hd, hcd⟩ : ∃ c d, i'.get? 0 = some c ∧ j'.get? 0 = some d ∧ c ≠ d := by
    cases hi0 : i'.get? 0 with
    | none =>
      have h1 := eq_fin_nil_of_get?_zero_eq_none hi0
      subst h1
      have h2 : j'.get? 0 = none := by
        rw [← Option.not_isSome_iff_eq_none, Word.isSome_get?_iff, ← hlen']
        simp
      rw [eq_fin_nil_of_get?_zero_eq_none h2] at hij
      exact absurd rfl hij
    | some c =>
      cases hj0 : j'.get? 0 with
      | none =>
        have h1 : (i'.get? 0).isSome := by simp [hi0]
        rw [Word.isSome_get?_iff, hlen', ← Word.isSome_get?_iff, hj0] at h1
        simp at h1
      | some d =>
        refine ⟨c, d, rfl, rfl, fun hcd => hfirst ?_⟩
        rw [hi0, hj0, hcd]
        simp
  obtain ⟨y, hy, hne⟩ := Φ.exists_dualProj_ne_of_get?_zero hsep hlt hc hd hcd
  obtain ⟨p, q, hp, -, hq, hcmin, -, himg⟩ := Φ.exists_image_comp_eq_Icc u.reverse
  have hpq : p < q := sub_pos.1 ((pow_pos (Φ.cmin_pos hN) _).trans_le hcmin)
  by_contra hall
  push Not at hall
  -- `H_{i'} = H_{j'}` on `f_{u^←}(I) = [p, q]`
  have heq : ∀ z ∈ Icc p q, Φ.dualProj i' z = Φ.dualProj j' z := by
    intro z hz
    rw [← himg] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hxn : (x : ℂ) ∈ closure (nbhd ε) := subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)
    have h := hall x hx
    rw [Φ.dualProj_prepend u i' hxn, Φ.dualProj_prepend u j' hxn, add_right_inj] at h
    rw [← Φ.comp_ofReal u.reverse hx]
    exact mul_left_cancel₀ (Φ.deriv_comp_ne_zero u.reverse hxn) h
  have hEq := eqOn_nbhd_of_eqOn_Icc Φ.ε_pos (Φ.differentiableOn_dualProj i')
    (Φ.differentiableOn_dualProj j') hpq (Icc_subset_Icc hp hq) heq
  exact hne (hEq (ofReal_mem_nbhd Φ.ε_pos hy))

/-- Proposition 1.8. -/
theorem proposition_1_8 (hN : 2 ≤ N) {α : ℝ} (hα : 0 < α)
    (hsep : ∀ i j : Fin N, i ≠ j → ∃ x ∈ I, α ≤ ‖Φ.nonlin i x - Φ.nonlin j x‖) :
    0 < Φ.beta ∧ (2 * Φ.beta * Φ.cmax / (1 - Φ.cmax) < α →
      (∀ i j : Word N, i ≠ j → i.length = j.length →
        0 < ⨆ x : I, ‖Φ.dualProj i ((x : ℝ) : ℂ) - Φ.dualProj j ((x : ℝ) : ℂ)‖) ∧ Φ.SESC) := by
  have hbeta : 0 < Φ.beta := by
    obtain ⟨x, hx, hαx⟩ := hsep ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff])
    have h1 := Φ.norm_nonlin_le_beta ⟨0, by omega⟩ hx
    have h2 := Φ.norm_nonlin_le_beta ⟨1, by omega⟩ hx
    have h3 := norm_sub_le (Φ.nonlin ⟨0, by omega⟩ x) (Φ.nonlin ⟨1, by omega⟩ x)
    linarith
  refine ⟨hbeta, fun hlt => ?_⟩
  have hpos : ∀ i j : Word N, i ≠ j → i.length = j.length →
      0 < ⨆ x : I, ‖Φ.dualProj i ((x : ℝ) : ℂ) - Φ.dualProj j ((x : ℝ) : ℂ)‖ := by
    intro i j hij hlen
    obtain ⟨x, hx, hne⟩ := Φ.exists_dualProj_ne (by omega) hsep hlt hij hlen
    obtain ⟨M, -, hM⟩ := Φ.exists_norm_dualProj_le
    have hbdd : BddAbove
        (range fun x : I => ‖Φ.dualProj i ((x : ℝ) : ℂ) - Φ.dualProj j ((x : ℝ) : ℂ)‖) := by
      refine ⟨M + M, ?_⟩
      rintro _ ⟨x, rfl⟩
      have hxn : ((x : ℝ) : ℂ) ∈ closure (nbhd ε) :=
        subset_closure (ofReal_mem_nbhd Φ.ε_pos x.2)
      exact (norm_sub_le _ _).trans (add_le_add (hM i _ hxn) (hM j _ hxn))
    exact (norm_pos_iff.2 (sub_ne_zero.2 hne)).trans_le
      (le_ciSup (f := fun x : I => ‖Φ.dualProj i ((x : ℝ) : ℂ) - Φ.dualProj j ((x : ℝ) : ℂ)‖)
        hbdd ⟨x, hx⟩)
  exact ⟨hpos, Φ.theorem_1_5 hpos⟩

end IFS

end AnalyticESC
