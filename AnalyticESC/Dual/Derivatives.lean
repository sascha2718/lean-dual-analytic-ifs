module

public import AnalyticESC.Dual.HigherDerivatives

@[expose] public section

/-!
# Derivatives of the dual natural projection

Lemma 2.9 (uniform bounds for `H_w^{(k)}` on `I`), Corollary 2.10 (Lipschitz bounds) and
Lemma 2.11 (dependence on the common prefix), using the Faà di Bruno formula of Lemma 2.8,
induction on the derivative order, polynomial bounds and geometric-series tails.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- `H_w` is `C^k` at every real point of `I`. -/
theorem contDiffAt_dualProj_ofReal (w : Word N) (k : ℕ) {x : ℝ} (hx : x ∈ I) :
    ContDiffAt ℂ k (Φ.dualProj w) x :=
  (((Φ.differentiableOn_dualProj w).analyticOnNhd (isOpen_nbhd ε)) x
    (ofReal_mem_nbhd Φ.ε_pos hx)).contDiffAt

/-- The constants `D_{k+1}`: derivatives of `φ_i' = f_i''/f_i'` are bounded on `I`. -/
theorem exists_nonlin_iteratedDeriv_bound (k : ℕ) :
    ∃ D ≥ 0, ∀ i, ∀ x ∈ I, ‖iteratedDeriv k (Φ.nonlin i) x‖ ≤ D := by
  have hb : ∀ i, ∃ D, ∀ x ∈ I, ‖iteratedDeriv k (Φ.nonlin i) x‖ ≤ D := by
    intro i
    obtain ⟨U, hUo, hU, -, hd⟩ := Φ.exists_differentiableOn_nonlin i
    have hc : ContinuousOn (iteratedDeriv k (Φ.nonlin i)) U := fun z hz =>
      (differentiableAt_iteratedDeriv hUo hd k hz).continuousAt.continuousWithinAt
    exact isCompact_Icc.exists_bound_of_continuousOn
      (hc.comp Complex.continuous_ofReal.continuousOn fun x hx =>
        hU (subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)))
  choose D hD using hb
  refine ⟨∑ i, |D i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun i x hx => ?_⟩
  exact (hD i x hx).trans ((le_abs_self _).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (D j)) (Finset.mem_univ i)))

/-- The induction step in Lemma 2.9. Bounds for the lower derivatives bound each polynomial
in Lemma 2.8; the remaining factor is at most `c_max^n`, since every partition is nonempty. -/
theorem exists_dualDerivTerm_bound_of_lower (k : ℕ) (C : ℕ → ℝ) (hC0 : ∀ ℓ, 0 ≤ C ℓ)
    (hC : ∀ ℓ < k, ∀ x ∈ I, ∀ w : Word N, ‖iteratedDeriv ℓ (Φ.dualProj w) x‖ ≤ C ℓ) :
    ∃ A ≥ 0, ∀ (w : Word N) (n : ℕ), ∀ x ∈ I,
      ‖Φ.dualDerivTerm w k n x‖ ≤ A * Φ.cmax ^ n := by
  classical
  have hc0 := Φ.cmax_nonneg
  choose E hE0 hE using fun m =>
    exists_norm_aeval_le_of_supported (gPoly_mem_supported m) C (fun ℓ _ => hC0 ℓ)
  choose D hD0 hD using Φ.exists_nonlin_iteratedDeriv_bound
  let B (c : OrderedFinpartition (k + 1)) := D (c.length - 1) * ∏ j, E (c.partSize j - 1)
  have hB : ∀ c, 0 ≤ B c := fun c => mul_nonneg (hD0 _)
    (Finset.prod_nonneg fun j _ => hE0 _)
  refine ⟨∑ c, B c, Finset.sum_nonneg fun c _ => hB c, fun w n x hx => ?_⟩
  cases hw : w.get? n with
  | none =>
    simp only [dualDerivTerm, hw, norm_zero]
    exact mul_nonneg (Finset.sum_nonneg fun c _ => hB c) (pow_nonneg hc0 n)
  | some i =>
    have hlen : (w.take n).length = n := by
      cases w with
      | fin v =>
        have hn : n < v.length := (List.getElem?_eq_some_iff.1 hw).1
        simp [Word.take, Nat.min_eq_left hn.le]
      | inf v => simp [Word.take]
    have hx' := ofReal_mem_nbhd Φ.ε_pos hx
    have hcomp : Φ.comp (w.take n).reverse x = ((Φ.comp (w.take n).reverse x).re : ℂ) :=
      Φ.comp_ofReal _ hx
    have hder : ‖deriv (Φ.comp (w.take n).reverse) x‖ ≤ Φ.cmax ^ n := by
      simpa [hlen] using Φ.norm_deriv_comp_le (w.take n).reverse (subset_closure hx')
    simp only [dualDerivTerm, hw]
    calc
      _ ≤ ∑ c : OrderedFinpartition (k + 1),
          ‖iteratedDeriv (c.length - 1) (Φ.nonlin i) (Φ.comp (w.take n).reverse x) *
            deriv (Φ.comp (w.take n).reverse) x ^ c.length *
            ∏ j, MvPolynomial.aeval (fun ℓ => iteratedDeriv ℓ
              (Φ.dualProj (.fin (w.take n))) x) (gPoly (c.partSize j - 1))‖ := norm_sum_le _ _
      _ ≤ ∑ c, B c * Φ.cmax ^ n := by
        refine Finset.sum_le_sum fun c _ => ?_
        have hd := hD (c.length - 1) i _ (Φ.re_comp_mem_I (w.take n).reverse hx)
        rw [← hcomp] at hd
        have hp : ∀ j : Fin c.length,
            ‖MvPolynomial.aeval (fun ℓ => iteratedDeriv ℓ (Φ.dualProj (.fin (w.take n))) x)
              (gPoly (c.partSize j - 1))‖ ≤ E (c.partSize j - 1) := by
          intro j
          apply hE
          intro ℓ hℓ
          have hℓ' : ℓ < c.partSize j - 1 := Finset.mem_range.1 hℓ
          exact hC ℓ (by have := c.partSize_le j; omega) x hx _
        have hc : ‖deriv (Φ.comp (w.take n).reverse) x‖ ^ c.length ≤ Φ.cmax ^ n := by
          calc _ ≤ (Φ.cmax ^ n) ^ c.length := pow_le_pow_left₀ (norm_nonneg _) hder _
            _ = Φ.cmax ^ (n * c.length) := (pow_mul _ _ _).symm
            _ ≤ Φ.cmax ^ n := pow_le_pow_of_le_one Φ.cmax_nonneg Φ.cmax_lt_one.le
              (by have := c.length_pos k.succ_pos; nlinarith)
        rw [norm_mul, norm_mul, norm_pow, norm_prod]
        calc _ ≤ D (c.length - 1) * Φ.cmax ^ n * ∏ j, E (c.partSize j - 1) :=
              mul_le_mul (mul_le_mul hd hc (by positivity) (hD0 _))
                (Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => hp j))
                (Finset.prod_nonneg fun j _ => norm_nonneg _)
                (mul_nonneg (hD0 _) (pow_nonneg hc0 n))
          _ = B c * Φ.cmax ^ n := by dsimp [B]; ring
      _ = (∑ c, B c) * Φ.cmax ^ n := (Finset.sum_mul ..).symm

/-- Lemma 2.9 by strong induction using Lemma 2.8. The bounds also control the geometric tails
needed for Lemma 2.11. -/
theorem exists_dualDerivTerm_bound (k : ℕ) :
    ∃ A ≥ 0, ∀ (w : Word N) (n : ℕ), ∀ x ∈ I,
      ‖Φ.dualDerivTerm w k n x‖ ≤ A * Φ.cmax ^ n := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hb : ∀ ℓ < k, ∃ C ≥ 0, ∀ x ∈ I, ∀ w : Word N,
        ‖iteratedDeriv ℓ (Φ.dualProj w) x‖ ≤ C := by
      intro ℓ hℓ
      obtain ⟨A, hA0, hA⟩ := ih ℓ hℓ
      have hc1 : 0 < 1 - Φ.cmax := sub_pos.2 Φ.cmax_lt_one
      refine ⟨A * (1 - Φ.cmax)⁻¹, by positivity, fun x hx w => ?_⟩
      rw [(Φ.lemma_2_8 w ℓ hx).2]
      exact tsum_of_norm_bounded
        ((hasSum_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left A)
        (fun n => hA w n x hx)
    let C : ℕ → ℝ := fun ℓ => if hℓ : ℓ < k then (hb ℓ hℓ).choose else 0
    have hC0 : ∀ ℓ, 0 ≤ C ℓ := by
      intro ℓ
      dsimp [C]
      split_ifs with hℓ
      · exact (hb ℓ hℓ).choose_spec.1
      · rfl
    exact Φ.exists_dualDerivTerm_bound_of_lower k C hC0 fun ℓ hℓ => by
      simpa only [C, dite_eq_left hℓ] using (hb ℓ hℓ).choose_spec.2

/-- One family `C_k` serving Lemmas 2.9 and 2.11, the latter for every common prefix length
`m ≤ |i ∧ j|`. -/
theorem exists_iteratedDeriv_bounds :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      (∀ k, ∀ x ∈ I, ∀ w : Word N, ‖iteratedDeriv k (Φ.dualProj w) x‖ ≤ C k) ∧
      ∀ k, ∀ x ∈ I, ∀ (i j : Word N) (m : ℕ), (m : ℕ∞) ≤ i.commonPrefixLength j →
        ‖iteratedDeriv k (Φ.dualProj i) x - iteratedDeriv k (Φ.dualProj j) x‖ ≤
          2 * C k * Φ.cmax ^ m := by
  classical
  choose A hA0 hA using Φ.exists_dualDerivTerm_bound
  let C (k : ℕ) := A k * (1 - Φ.cmax)⁻¹ + 1
  have hc0 := Φ.cmax_nonneg
  have hc1 : 0 < 1 - Φ.cmax := sub_pos.2 Φ.cmax_lt_one
  have htail : ∀ k w m x, x ∈ I →
      ‖∑' n, Φ.dualDerivTerm w k (n + m) x‖ ≤ A k * (1 - Φ.cmax)⁻¹ * Φ.cmax ^ m := by
    intro k w m x hx
    have hs := (hasSum_geometric_of_lt_one hc0 Φ.cmax_lt_one).mul_left (A k * Φ.cmax ^ m)
    have hb : ∀ n, ‖Φ.dualDerivTerm w k (n + m) x‖ ≤ A k * Φ.cmax ^ m * Φ.cmax ^ n := by
      intro n
      calc _ ≤ A k * Φ.cmax ^ (n + m) := hA k w _ x hx
        _ = _ := by rw [pow_add]; ring
    simpa only [mul_right_comm (A k)] using tsum_of_norm_bounded hs hb
  refine ⟨C, fun k => by have := hA0 k; dsimp [C]; positivity, ?_, ?_⟩
  · intro k x hx w
    rw [(Φ.lemma_2_8 w k hx).2]
    have ht := htail k w 0 x hx
    simp only [Nat.add_zero, pow_zero, mul_one] at ht
    exact ht.trans (le_add_of_nonneg_right zero_le_one)
  · intro k x hx i j m hm
    have hprefix : ∀ n < m, Φ.dualDerivTerm i k n x = Φ.dualDerivTerm j k n x := by
      obtain ⟨a, i', j', ha, rfl, rfl⟩ := Word.exists_eq_prepend hm
      intro n hn
      have hn' : n < a.length := ha ▸ hn
      simp only [dualDerivTerm, Word.get?_prepend_of_lt a _ hn',
        Word.take_prepend_of_le a _ hn'.le]
    have heq : (∑ n ∈ Finset.range m, Φ.dualDerivTerm i k n x) =
        ∑ n ∈ Finset.range m, Φ.dualDerivTerm j k n x :=
      Finset.sum_congr rfl fun n hn => hprefix n (Finset.mem_range.1 hn)
    rw [(Φ.lemma_2_8 i k hx).2, (Φ.lemma_2_8 j k hx).2,
      ← (Φ.lemma_2_8 i k hx).1.sum_add_tsum_nat_add m,
      ← (Φ.lemma_2_8 j k hx).1.sum_add_tsum_nat_add m, heq, add_sub_add_left_eq_sub]
    calc _ ≤ ‖∑' n, Φ.dualDerivTerm i k (n + m) x‖ +
          ‖∑' n, Φ.dualDerivTerm j k (n + m) x‖ := norm_sub_le _ _
      _ ≤ A k * (1 - Φ.cmax)⁻¹ * Φ.cmax ^ m +
          A k * (1 - Φ.cmax)⁻¹ * Φ.cmax ^ m := add_le_add (htail k i m x hx) (htail k j m x hx)
      _ ≤ 2 * C k * Φ.cmax ^ m := by dsimp [C]; nlinarith [pow_nonneg hc0 m]

/-- Lemma 2.9. -/
theorem lemma_2_9 (k : ℕ) :
    ∃ C, ∀ x ∈ I, ∀ w : Word N, ‖iteratedDeriv k (Φ.dualProj w) x‖ ≤ C := by
  obtain ⟨C, -, hC, -⟩ := Φ.exists_iteratedDeriv_bounds
  exact ⟨C k, hC k⟩

/-- The Lipschitz bound of Corollary 2.10, for every `k`. -/
theorem norm_iteratedDeriv_sub_le_of_bounds (C : ℕ → ℝ)
    (hC : ∀ k, ∀ x ∈ I, ∀ w : Word N, ‖iteratedDeriv k (Φ.dualProj w) x‖ ≤ C k) (k : ℕ)
    {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) (w : Word N) :
    ‖iteratedDeriv k (Φ.dualProj w) x - iteratedDeriv k (Φ.dualProj w) y‖ ≤
      C (k + 1) * |x - y| := by
  have han : AnalyticOnNhd ℂ (Φ.dualProj w) (nbhd ε) :=
    (Φ.differentiableOn_dualProj w).analyticOnNhd (isOpen_nbhd ε)
  have hder : ∀ t ∈ I, HasDerivWithinAt (fun s : ℝ => iteratedDeriv k (Φ.dualProj w) s)
      (iteratedDeriv (k + 1) (Φ.dualProj w) t) I t := by
    intro t ht
    have hdiff : DifferentiableAt ℂ (iteratedDeriv k (Φ.dualProj w)) t := by
      rw [iteratedDeriv_eq_iterate]
      exact (han.iterated_deriv k t (ofReal_mem_nbhd Φ.ε_pos ht)).differentiableAt
    rw [iteratedDeriv_succ]
    exact hdiff.hasDerivAt.comp_ofReal.hasDerivWithinAt
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder
    (fun t ht => hC (k + 1) t ht w) (convex_Icc 0 1) hy hx
  simpa [Real.norm_eq_abs] using this

set_option linter.unusedVariables false in
/-- Corollary 2.10, for any constants `C_k` as in Lemma 2.9. -/
theorem corollary_2_10 (C : ℕ → ℝ)
    (hC : ∀ k, ∀ x ∈ I, ∀ w : Word N, ‖iteratedDeriv k (Φ.dualProj w) x‖ ≤ C k) {k : ℕ}
    (hk : 1 ≤ k) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) (w : Word N) :
    ‖iteratedDeriv k (Φ.dualProj w) x - iteratedDeriv k (Φ.dualProj w) y‖ ≤ C (k + 1) * |x - y| :=
  Φ.norm_iteratedDeriv_sub_le_of_bounds C hC k hx hy w

/-- Lemma 2.11, for distinct words, with constants `C_k` as in Lemma 2.9. -/
theorem lemma_2_11 :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      (∀ k, ∀ x ∈ I, ∀ w : Word N, ‖iteratedDeriv k (Φ.dualProj w) x‖ ≤ C k) ∧
      ∀ k, ∀ x ∈ I, ∀ i j : Word N, i ≠ j →
        ‖iteratedDeriv k (Φ.dualProj i) x - iteratedDeriv k (Φ.dualProj j) x‖ ≤
          2 * C k * Φ.cmax ^ (i.commonPrefixLength j).toNat := by
  obtain ⟨C, hC0, hC, hCd⟩ := Φ.exists_iteratedDeriv_bounds
  exact ⟨C, hC0, hC, fun k x hx i j hij =>
    hCd k x hx i j _ (ENat.natCast_toNat (Word.commonPrefixLength_lt_top hij).ne).le⟩

end IFS

end AnalyticESC
