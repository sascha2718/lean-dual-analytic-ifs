module

public import AnalyticESC.Dual.Attractor

@[expose] public section

/-!
# Lemma 2.5

The strong separation of the dual IFS in terms of cylinder sets, (a) ⇔ (b), and in terms of the
dual natural projection, (a) ⇔ (c).
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-- The cylinder set `(k,K)` of Section 2.1: maps in `C^ω_ε([0,1])` with values in `(k,K)` on
`[0,1]`. -/
def dualCyl (ε k K : ℝ) : Set (ℂ → ℂ) :=
  {g | DifferentiableOn ℂ g (nbhd ε) ∧ (∀ x ∈ I, (g x).im = 0) ∧
    ∀ x ∈ I, k < (g x).re ∧ (g x).re < K}

/-- The closed cylinder set `cl (k,K)`: maps in `C^ω_ε([0,1])` with values in `[k,K]` on
`[0,1]`. -/
def dualCylClosed (ε k K : ℝ) : Set (ℂ → ℂ) :=
  {g | DifferentiableOn ℂ g (nbhd ε) ∧ (∀ x ∈ I, (g x).im = 0) ∧
    ∀ x ∈ I, k ≤ (g x).re ∧ (g x).re ≤ K}

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-! ## Words -/

/-- An infinite word is its prefix of length `n` followed by its `n`-fold shift. -/
private theorem cyl_inf_eq_prepend_ofFn (w : ℕ → Fin N) (n : ℕ) :
    Word.inf w = (Word.inf fun k => w (k + n)).prepend (List.ofFn fun k : Fin n => w k) := by
  change Word.inf w = Word.inf fun m =>
    if h : m < (List.ofFn fun k : Fin n => w k).length then (List.ofFn fun k : Fin n => w k)[m]
    else w (m - (List.ofFn fun k : Fin n => w k).length + n)
  congr 1
  funext m
  simp only [List.length_ofFn]
  split_ifs with hm
  · simp
  · congr 1
    omega

/-! ## Iterates of the dual operators on `I` -/

/-- On `I`, `F_w` applied to a constant `c` is affine in `c`. -/
private theorem re_dualComp_const (w : List (Fin N)) (c : ℝ) {x : ℝ} (hx : x ∈ I) :
    (Φ.dualComp w (fun _ => (c : ℂ)) x).re =
      (deriv (Φ.comp w.reverse) x).re * c + (Φ.dualProj (.fin w) x).re := by
  rw [Φ.dualComp_apply w _ (ofReal_mem_nbhd Φ.ε_pos hx)]
  simp [Complex.mul_re]

/-- The cocycle identity `H_{w v} = F_w H_v` on `I`, in real parts. -/
private theorem re_dualProj_prepend (w : List (Fin N)) (v : Word N) {x : ℝ} (hx : x ∈ I) :
    (Φ.dualProj (v.prepend w) x).re =
      (deriv (Φ.comp w.reverse) x).re * (Φ.dualProj v ((Φ.comp w.reverse x).re : ℂ)).re +
        (Φ.dualProj (.fin w) x).re := by
  have hxn := ofReal_mem_nbhd Φ.ε_pos hx
  rw [Φ.dualProj_prepend w v (subset_closure hxn), ← Φ.comp_ofReal w.reverse hx]
  simp [Complex.mul_re, Φ.im_deriv_comp_ofReal _ hxn]
  ring

/-- `|f_{w^←}'| ≤ c_max^{|w|}` on `I`, in real parts. -/
private theorem abs_re_deriv_comp_reverse_le (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    |(deriv (Φ.comp w.reverse) x).re| ≤ Φ.cmax ^ w.length := by
  have h := Φ.norm_deriv_comp_le w.reverse (subset_closure (ofReal_mem_nbhd Φ.ε_pos hx))
  rw [List.length_reverse] at h
  exact (Complex.abs_re_le_norm _).trans h

/-- `F_w` maps the closed cylinder into itself if every `F_i` does. -/
private theorem dualComp_mem_dualCylClosed {k K : ℝ}
    (hmaps : ∀ i, MapsTo (Φ.dualOp i) (dualCylClosed ε k K) (dualCyl ε k K))
    (w : List (Fin N)) {h : ℂ → ℂ} (hh : h ∈ dualCylClosed ε k K) :
    Φ.dualComp w h ∈ dualCylClosed ε k K := by
  induction w with
  | nil => exact hh
  | cons i w ih =>
    obtain ⟨h1, h2, h3⟩ := hmaps i ih
    exact ⟨h1, h2, fun x hx => ⟨(h3 x hx).1.le, (h3 x hx).2.le⟩⟩

/-- If every `F_i` maps `cl (k,K)` into `(k,K)`, then `H_u` takes values in `[k,K]` on `I`, as
the limit of `F_{u|m} k`. -/
private theorem re_dualProj_mem_Icc {k K : ℝ} (hkK : k ≤ K)
    (hmaps : ∀ i, MapsTo (Φ.dualOp i) (dualCylClosed ε k K) (dualCyl ε k K))
    (u : ℕ → Fin N) {y : ℝ} (hy : y ∈ I) :
    (Φ.dualProj (.inf u) y).re ∈ Icc k K := by
  obtain ⟨M, -, hM⟩ := Φ.exists_norm_dualProj_le
  have hconst : (fun _ => (k : ℂ)) ∈ dualCylClosed ε k K :=
    ⟨differentiableOn_const _, fun _ _ => Complex.ofReal_im k, fun _ _ => ⟨le_rfl, hkK⟩⟩
  have hmem : ∀ m : ℕ, (Φ.dualComp (List.ofFn fun i : Fin m => u i)
      (fun _ => (k : ℂ)) y).re ∈ Icc k K := fun m =>
    (Φ.dualComp_mem_dualCylClosed hmaps _ hconst).2.2 y hy
  have hclose : ∀ m : ℕ, |(Φ.dualProj (.inf u) y).re -
      (Φ.dualComp (List.ofFn fun i : Fin m => u i) (fun _ => (k : ℂ)) y).re| ≤
        Φ.cmax ^ m * (M + |k|) := by
    intro m
    have hD := Φ.abs_re_deriv_comp_reverse_le (List.ofFn fun i : Fin m => u i) hy
    rw [List.length_ofFn] at hD
    rw [cyl_inf_eq_prepend_ofFn u m, Φ.re_dualProj_prepend _ _ hy, Φ.re_dualComp_const _ _ hy]
    set y' := (Φ.comp (List.ofFn fun i : Fin m => u i).reverse y).re
    have hy' : y' ∈ I := Φ.re_comp_mem_I _ hy
    have ht : |(Φ.dualProj (.inf fun i => u (i + m)) y').re - k| ≤ M + |k| :=
      (abs_sub _ _).trans (add_le_add ((Complex.abs_re_le_norm _).trans
        (hM _ _ (subset_closure (ofReal_mem_nbhd Φ.ε_pos hy')))) le_rfl)
    calc _ = |(deriv (Φ.comp (List.ofFn fun i : Fin m => u i).reverse) y).re| *
          |(Φ.dualProj (.inf fun i => u (i + m)) y').re - k| := by
          rw [← abs_mul]
          congr 1
          ring
      _ ≤ Φ.cmax ^ m * (M + |k|) :=
          mul_le_mul hD ht (abs_nonneg _) (pow_nonneg Φ.cmax_nonneg _)
  have hlim : Tendsto (fun m : ℕ => Φ.cmax ^ m * (M + |k|)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_const
      (M + |k|)
  have hT : Tendsto (fun m : ℕ => (Φ.dualComp (List.ofFn fun i : Fin m => u i)
      (fun _ => (k : ℂ)) y).re) atTop (𝓝 (Φ.dualProj (.inf u) y).re) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun m => ?_) hlim
    rw [Real.dist_eq, abs_sub_comm]
    exact hclose m
  exact isClosed_Icc.mem_of_tendsto hT (Eventually.of_forall hmem)

/-- If `H_u` takes values in `[k,K]` on `I` for every `u`, then `H_{w v}(x)` lies in the cylinder
interval `conv((F_w k)(x), (F_w K)(x))`. -/
private theorem re_dualProj_prepend_mem_dualCylAt {k K : ℝ}
    (hH : ∀ u : ℕ → Fin N, ∀ y ∈ I, (Φ.dualProj (.inf u) y).re ∈ Icc k K)
    (w : List (Fin N)) (v : ℕ → Fin N) {x : ℝ} (hx : x ∈ I) :
    (Φ.dualProj ((Word.inf v).prepend w) x).re ∈ Φ.dualCylAt k K w x := by
  rw [dualCylAt, Φ.re_dualComp_const _ _ hx, Φ.re_dualComp_const _ _ hx,
    Φ.re_dualProj_prepend _ _ hx]
  obtain ⟨h1, h2⟩ := hH v _ (Φ.re_comp_mem_I w.reverse hx)
  set a := (deriv (Φ.comp w.reverse) x).re
  set t := (Φ.dualProj (.inf v) ((Φ.comp w.reverse x).re : ℂ)).re
  rw [mem_uIcc]
  rcases le_total 0 a with ha | ha
  · left
    constructor <;> nlinarith
  · right
    constructor <;> nlinarith

/-- Points of one cylinder interval of `Φ` at `x ∈ I` are `c_max^{|w|} (K - k)` close. -/
theorem abs_sub_le_cmax_pow_of_mem_dualCylAt {k K : ℝ} (hkK : k ≤ K) (w : List (Fin N))
    {x : ℝ} (hx : x ∈ I) {p q : ℝ} (hp : p ∈ Φ.dualCylAt k K w x)
    (hq : q ∈ Φ.dualCylAt k K w x) : |p - q| ≤ Φ.cmax ^ w.length * (K - k) := by
  refine (abs_sub_le_of_uIcc_subset_uIcc (uIcc_subset_uIcc hq hp)).trans ?_
  rw [Φ.re_dualComp_const _ _ hx, Φ.re_dualComp_const _ _ hx]
  calc _ = |(deriv (Φ.comp w.reverse) x).re| * (K - k) := by
        rw [← abs_of_nonneg (sub_nonneg.2 hkK), ← abs_mul]
        congr 1
        ring
    _ ≤ Φ.cmax ^ w.length * (K - k) :=
        mul_le_mul_of_nonneg_right (Φ.abs_re_deriv_comp_reverse_le w hx) (sub_nonneg.2 hkK)

/-- `F_i` maps `cl (-K,K)` into `(-K,K)` as soon as `c_max K + M < K`, where `M` bounds
`f_i''/f_i'`. -/
private theorem mapsTo_dualOp_dualCylClosed {M K : ℝ}
    (hM : ∀ i, ∀ z ∈ closure (nbhd ε), ‖Φ.nonlin i z‖ ≤ M) (hK : Φ.cmax * K + M < K)
    (i : Fin N) : MapsTo (Φ.dualOp i) (dualCylClosed ε (-K) K) (dualCyl ε (-K) K) := by
  rintro h ⟨hd, hre, hb⟩
  have hfx : ∀ x ∈ I, Φ.f i x = (((Φ.f i x).re : ℝ) : ℂ) ∧ (Φ.f i x).re ∈ I := fun x hx =>
    ⟨Complex.ext (by simp)
      (by simp [Φ.im_f_ofReal i (nbhd_subset_two (ofReal_mem_nbhd Φ.ε_pos hx))]),
      (Φ.inClass i).re_mem_I x hx⟩
  have him : ∀ x ∈ I, (Φ.dualOp i h x).im = 0 := by
    intro x hx
    have hxn := ofReal_mem_nbhd Φ.ε_pos hx
    simp only [dualOp]
    rw [(hfx x hx).1]
    simp [Complex.mul_im, Φ.im_deriv_f_ofReal i (nbhd_subset_two hxn), hre _ (hfx x hx).2,
      Φ.im_nonlin_ofReal i hxn]
  refine ⟨?_, him, fun x hx => ?_⟩
  · obtain ⟨U, -, hU, -, hnl⟩ := Φ.exists_differentiableOn_nonlin i
    have h1 : DifferentiableOn ℂ (deriv (Φ.f i)) (nbhd ε) :=
      ((Φ.differentiableOn_f i).deriv (isOpen_nbhd _)).mono nbhd_subset_two
    have h2 : DifferentiableOn ℂ (fun z => h (Φ.f i z)) (nbhd ε) :=
      hd.comp ((Φ.differentiableOn_f i).mono nbhd_subset_two) (Φ.mapsTo_f i)
    exact (h1.mul h2).add (hnl.mono (subset_closure.trans hU))
  · have hxn := ofReal_mem_nbhd Φ.ε_pos hx
    have hy := hfx x hx
    have hhy : ‖h (Φ.f i x)‖ ≤ K := by
      rw [hy.1, ← Complex.abs_re_eq_norm.2 (hre _ hy.2)]
      exact abs_le.2 (hb _ hy.2)
    have hnorm : ‖Φ.dualOp i h x‖ ≤ Φ.cmax * K + M := by
      simp only [dualOp]
      refine (norm_add_le _ _).trans (add_le_add ?_ (hM i _ (subset_closure hxn)))
      rw [norm_mul]
      exact mul_le_mul (Φ.norm_deriv_le_cmax i (subset_closure hxn)) hhy (norm_nonneg _)
        Φ.cmax_nonneg
    exact abs_lt.1 ((Complex.abs_re_le_norm _).trans_lt (hnorm.trans_lt hK))

/-- Lemma 2.5: (a) the dual IFS satisfies the SSC if and only if (b) there are `k < K` and
`n ≥ 1` with `F_i cl (k,K) ⊆ (k,K)` for every `i` and `F_i(k,K) ∩ F_j(k,K) = ∅`, in the sense of
(2.2), for all `i, j ∈ Σ_n` with `i₁ ≠ j₁`; and if and only if (c) there is `δ > 0` with
`sup_{x ∈ [0,1]} |H_i(x) - H_j(x)| > δ` for all `i, j ∈ Σ` with `i₁ ≠ j₁`. -/
theorem lemma_2_5 (hN : 0 < N) :
    (Φ.DualSSC ↔ ∃ k K : ℝ, k < K ∧ ∃ n : ℕ,
      (∀ i, MapsTo (Φ.dualOp i) (dualCylClosed ε k K) (dualCyl ε k K)) ∧
      ∀ i j : Fin (n + 1) → Fin N, i 0 ≠ j 0 →
        Φ.DualCylDisjoint k K (List.ofFn i) (List.ofFn j)) ∧
    (Φ.DualSSC ↔ ∃ δ > 0, ∀ i j : ℕ → Fin N, i 0 ≠ j 0 →
      δ < ⨆ x : I, ‖Φ.dualProj (.inf i) ((x : ℝ) : ℂ) - Φ.dualProj (.inf j) ((x : ℝ) : ℂ)‖) := by
  refine ⟨⟨fun hssc => ?_, ?_⟩, Φ.dualSSC_iff_exists_delta hN⟩
  · -- (a) ⇒ (b), through (c): cylinder intervals of level `n + 1` are shorter than `δ / 2`
    obtain ⟨M, hM0, hM⟩ := Φ.exists_nonlin_bound
    have hc := Φ.cmax_lt_one
    set K := M / (1 - Φ.cmax) + 1 with hK_def
    have hK0 : 0 < K := by
      have : 0 ≤ M / (1 - Φ.cmax) := div_nonneg hM0 (by linarith)
      linarith
    have hK : Φ.cmax * K + M < K := by
      have h1 : (1 - Φ.cmax) * (M / (1 - Φ.cmax)) = M := mul_div_cancel₀ _ (by linarith)
      nlinarith
    have hmaps := Φ.mapsTo_dualOp_dualCylClosed hM hK
    have hH := Φ.re_dualProj_mem_Icc (by linarith) hmaps
    obtain ⟨δ, hδ, hsep⟩ := (Φ.dualSSC_iff_exists_delta hN).1 hssc
    have hK2 : 0 < 2 * (K - -K) := by linarith
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hδ hK2) hc
    have hn' : Φ.cmax ^ (n + 1) * (2 * (K - -K)) < δ :=
      ((lt_div_iff₀ hK2).1 hn).trans_le' (mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one Φ.cmax_nonneg hc.le (Nat.le_succ n)) hK2.le)
    refine ⟨-K, K, by linarith, n, hmaps, fun i j hij => ?_⟩
    -- extend `i` and `j` to infinite words
    let z₀ : ℕ → Fin N := fun _ => ⟨0, hN⟩
    obtain ⟨i', hi', hi0⟩ : ∃ i' : ℕ → Fin N,
        (Word.inf z₀).prepend (List.ofFn i) = .inf i' ∧ i' 0 = i 0 := ⟨_, rfl, by simp⟩
    obtain ⟨j', hj', hj0⟩ : ∃ j' : ℕ → Fin N,
        (Word.inf z₀).prepend (List.ofFn j) = .inf j' ∧ j' 0 = j 0 := ⟨_, rfl, by simp⟩
    have : Nonempty I := ⟨⟨0, left_mem_Icc.2 zero_le_one⟩⟩
    obtain ⟨⟨x, hx⟩, hlt⟩ := exists_lt_of_lt_ciSup (hsep i' j' (by rw [hi0, hj0]; exact hij))
    refine ⟨x, hx, Set.disjoint_left.2 fun p hpi hpj => ?_⟩
    have h1 := Φ.re_dualProj_prepend_mem_dualCylAt hH (List.ofFn i) z₀ hx
    have h2 := Φ.re_dualProj_prepend_mem_dualCylAt hH (List.ofFn j) z₀ hx
    rw [hi'] at h1
    rw [hj'] at h2
    have e1 := Φ.abs_sub_le_cmax_pow_of_mem_dualCylAt (by linarith) _ hx h1 hpi
    have e2 := Φ.abs_sub_le_cmax_pow_of_mem_dualCylAt (by linarith) _ hx hpj h2
    rw [List.length_ofFn] at e1 e2
    have hxn := ofReal_mem_nbhd Φ.ε_pos hx
    have hnorm : ‖Φ.dualProj (.inf i') (x : ℂ) - Φ.dualProj (.inf j') (x : ℂ)‖ ≤
        |(Φ.dualProj (.inf i') (x : ℂ)).re - (Φ.dualProj (.inf j') (x : ℂ)).re| := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans_eq ?_
      simp [Φ.im_dualProj_ofReal _ hxn]
    have e3 := abs_sub_le (Φ.dualProj (.inf i') (x : ℂ)).re p (Φ.dualProj (.inf j') (x : ℂ)).re
    simp only at hlt
    linarith
  · -- (b) ⇒ (a): `H_i` and `H_j` lie in disjoint cylinder intervals at some `x`
    rintro ⟨k, K, hkK, n, hmaps, hdisj⟩
    rw [Φ.dualSSC_iff_ne hN]
    intro i j hij
    obtain ⟨x, hx, hd⟩ := hdisj (fun m => i m) (fun m => j m) (by simpa using hij)
    have hH := Φ.re_dualProj_mem_Icc hkK.le hmaps
    have h1 := Φ.re_dualProj_prepend_mem_dualCylAt hH (List.ofFn fun m : Fin (n + 1) => i m)
      (fun m => i (m + (n + 1))) hx
    have h2 := Φ.re_dualProj_prepend_mem_dualCylAt hH (List.ofFn fun m : Fin (n + 1) => j m)
      (fun m => j (m + (n + 1))) hx
    rw [← cyl_inf_eq_prepend_ofFn] at h1 h2
    refine ⟨x, hx, fun heq => ?_⟩
    rw [heq] at h1
    exact Set.disjoint_left.1 hd h1 h2

end IFS

end AnalyticESC
