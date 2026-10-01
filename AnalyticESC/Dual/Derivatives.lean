module

public import AnalyticESC.Dual.Projection

@[expose] public section

/-!
# Derivatives of the dual natural projection

Lemma 2.8 (uniform bounds for `H_w^{(k)}` on `I`), Corollary 2.9 (Lipschitz bounds) and
Lemma 2.10 (dependence on the common prefix), proved by Cauchy estimates on discs in `B_ε`.
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-- Cauchy estimate at a point of `I` on the disc of radius `ε / 2`, which lies in `B_ε`. -/
theorem norm_iteratedDeriv_ofReal_le_of_nbhd {ε : ℝ} (hε : 0 < ε) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (nbhd ε)) {B : ℝ} (hB : ∀ z ∈ nbhd ε, ‖g z‖ ≤ B) (k : ℕ)
    {x : ℝ} (hx : x ∈ I) :
    ‖iteratedDeriv k g x‖ ≤ k.factorial * B / (ε / 2) ^ k := by
  have hsub : closedBall (x : ℂ) (ε / 2) ⊆ nbhd ε :=
    (closedBall_subset_ball (half_lt_self hε)).trans (ball_subset_nbhd hx)
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (half_pos hε)
    (hg.diffContOnCl_ball hsub) fun z hz => hB z (hsub (sphere_subset_closedBall hz))

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- `H_w` is `C^k` at every real point of `I`. -/
theorem contDiffAt_dualProj_ofReal (w : Word N) (k : ℕ) {x : ℝ} (hx : x ∈ I) :
    ContDiffAt ℂ k (Φ.dualProj w) x :=
  (((Φ.differentiableOn_dualProj w).analyticOnNhd (isOpen_nbhd ε)) x
    (ofReal_mem_nbhd Φ.ε_pos hx)).contDiffAt

/-- One family `C_k` serving Lemmas 2.8 and 2.10, the latter for every common prefix length
`m ≤ |i ∧ j|`. -/
theorem exists_iteratedDeriv_bounds :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      (∀ k, ∀ x ∈ I, ∀ w : Word N, ‖iteratedDeriv k (Φ.dualProj w) x‖ ≤ C k) ∧
      ∀ k, ∀ x ∈ I, ∀ (i j : Word N) (m : ℕ), (m : ℕ∞) ≤ i.commonPrefixLength j →
        ‖iteratedDeriv k (Φ.dualProj i) x - iteratedDeriv k (Φ.dualProj j) x‖ ≤
          2 * C k * Φ.cmax ^ m := by
  obtain ⟨M, hM0, hM, hMd⟩ := Φ.exists_dualProj_bounds
  have hε := Φ.ε_pos
  refine ⟨fun k => k.factorial * (M + 1) / (ε / 2) ^ k, fun k => by positivity, ?_, ?_⟩
  · intro k x hx w
    calc ‖iteratedDeriv k (Φ.dualProj w) x‖ ≤ k.factorial * M / (ε / 2) ^ k :=
          norm_iteratedDeriv_ofReal_le_of_nbhd hε (Φ.differentiableOn_dualProj w)
            (fun z hz => hM w z (subset_closure hz)) k hx
      _ ≤ k.factorial * (M + 1) / (ε / 2) ^ k := by gcongr; linarith
  · intro k x hx i j m hm
    have hd : DifferentiableOn ℂ (Φ.dualProj i - Φ.dualProj j) (nbhd ε) :=
      (Φ.differentiableOn_dualProj i).sub (Φ.differentiableOn_dualProj j)
    have hc : 0 ≤ Φ.cmax ^ m := pow_nonneg Φ.cmax_nonneg m
    rw [← iteratedDeriv_sub (Φ.contDiffAt_dualProj_ofReal i k hx)
      (Φ.contDiffAt_dualProj_ofReal j k hx)]
    calc ‖iteratedDeriv k (Φ.dualProj i - Φ.dualProj j) x‖
        ≤ k.factorial * (2 * M * Φ.cmax ^ m) / (ε / 2) ^ k :=
          norm_iteratedDeriv_ofReal_le_of_nbhd hε hd
            (fun z hz => hMd i j m hm z (subset_closure hz)) k hx
      _ ≤ k.factorial * (2 * (M + 1) * Φ.cmax ^ m) / (ε / 2) ^ k := by
          gcongr
          linarith
      _ = 2 * (k.factorial * (M + 1) / (ε / 2) ^ k) * Φ.cmax ^ m := by ring

/-- Lemma 2.8. -/
theorem lemma_2_8 (k : ℕ) :
    ∃ C, ∀ x ∈ I, ∀ w : Word N, ‖iteratedDeriv k (Φ.dualProj w) x‖ ≤ C := by
  obtain ⟨C, -, hC, -⟩ := Φ.exists_iteratedDeriv_bounds
  exact ⟨C k, hC k⟩

/-- The Lipschitz bound of Corollary 2.9, for every `k`. -/
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
/-- Corollary 2.9, for any constants `C_k` as in Lemma 2.8. -/
theorem corollary_2_9 (C : ℕ → ℝ)
    (hC : ∀ k, ∀ x ∈ I, ∀ w : Word N, ‖iteratedDeriv k (Φ.dualProj w) x‖ ≤ C k) {k : ℕ}
    (hk : 1 ≤ k) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) (w : Word N) :
    ‖iteratedDeriv k (Φ.dualProj w) x - iteratedDeriv k (Φ.dualProj w) y‖ ≤ C (k + 1) * |x - y| :=
  Φ.norm_iteratedDeriv_sub_le_of_bounds C hC k hx hy w

/-- Lemma 2.10, for distinct words, with constants `C_k` as in Lemma 2.8. -/
theorem lemma_2_10 :
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
