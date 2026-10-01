module

public import AnalyticESC.Main.Closeness
public import AnalyticESC.Dual.Attractor

@[expose] public section

/-!
# Theorems 1.5 and 2.2

If the strong exponential separation condition fails, either two infinite words with different
first letters have equal dual natural projections on `I`, or two finite words of equal length
with different last letters give equal compositions on `I`. Theorem 1.5 and Theorem 2.2 follow.

The failure of the SESC gives a sequence of pairs `a_k u_k`, `b_k u_k` of words of length `n_k`,
with `|a_k| = |b_k| ≥ 1` and different last letters of `a_k` and `b_k`, whose compositions are
`η_k`-close on `I`, where `η_k` is super-exponentially small in `n_k` (a `CondSeq`). Along a
subsequence the left endpoints `p_k` of `f_{u_k}(I) = [p_k, q_k]` converge to some `p₀ ∈ I`. If
`|a_k|` is bounded, then along a subsequence `a_k = a` and `b_k = b` are constant, all derivatives
of `f_a` and `f_b` agree at `p₀` by (3.3), and `f_a = f_b`. Otherwise `a_k^← → i` and `b_k^← → j`
along a subsequence, and all derivatives of `H_i` and `H_j` agree at `p₀` by (3.2) and (3.3).
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-! ## Super-exponentially small sequences -/

/-- `η k` is eventually below `θ ^ n k`, for every `θ > 0`. -/
def SupExpSmall (n : ℕ → ℕ) (η : ℕ → ℝ) : Prop :=
  ∀ θ > 0, ∀ᶠ k in atTop, η k ≤ θ ^ n k

namespace SupExpSmall

variable {n : ℕ → ℕ} {η : ℕ → ℝ}

theorem comp (h : SupExpSmall n η) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    SupExpSmall (n ∘ φ) (η ∘ φ) := fun θ hθ => hφ.eventually (h θ hθ)

theorem eventually_le (hn : ∀ k, 1 ≤ n k) (h : SupExpSmall n η) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k in atTop, η k ≤ δ := by
  filter_upwards [h (min δ 1) (lt_min hδ one_pos)] with k hk
  calc η k ≤ min δ 1 ^ n k := hk
    _ ≤ min δ 1 :=
      pow_le_of_le_one (le_min hδ.le zero_le_one) (min_le_right _ _) (by have := hn k; omega)
    _ ≤ δ := min_le_left _ _

theorem eventually_lt_pow (hn : ∀ k, 1 ≤ n k) (h : SupExpSmall n η) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ k in atTop, η k < c ^ n k := by
  filter_upwards [h (c / 2) (half_pos hc)] with k hk
  exact hk.trans_lt (pow_lt_pow_left₀ (half_lt_self hc) (half_pos hc).le (by have := hn k; omega))

/-- `K A^{n_k} η_k^s` is super-exponentially small along with `η_k`. -/
theorem mul_pow_rpow (hn : ∀ k, 1 ≤ n k) (h : SupExpSmall n η) (hη : ∀ k, 0 ≤ η k) (K : ℝ)
    {A s : ℝ} (hA : 0 ≤ A) (hs : 0 < s) :
    SupExpSmall n fun k => K * A ^ n k * η k ^ s := by
  intro θ hθ
  set L := max K 1 * (A + 1) with hL_def
  have hL : 0 < L := by positivity
  have hθL : 0 < θ / L := div_pos hθ hL
  have hθ' : 0 < (θ / L) ^ s⁻¹ := Real.rpow_pos_of_pos hθL _
  filter_upwards [h _ hθ'] with k hk
  have hnk : n k ≠ 0 := by have := hn k; omega
  have h1 : η k ^ s ≤ (θ / L) ^ n k := by
    calc η k ^ s ≤ (((θ / L) ^ s⁻¹) ^ n k) ^ s := Real.rpow_le_rpow (hη k) hk hs.le
      _ = (θ / L) ^ n k := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hθL.le, ← Real.rpow_mul hθL.le,
          show s⁻¹ * (n k : ℝ) * s = n k by field_simp, Real.rpow_natCast]
  have h2 : K ≤ max K 1 ^ n k := (le_max_left _ _).trans (le_self_pow₀ (le_max_right _ _) hnk)
  have h3 : A ^ n k ≤ (A + 1) ^ n k := pow_le_pow_left₀ hA (by linarith) _
  calc K * A ^ n k * η k ^ s ≤ max K 1 ^ n k * (A + 1) ^ n k * (θ / L) ^ n k :=
        mul_le_mul (mul_le_mul h2 h3 (by positivity) (by positivity)) h1
          (Real.rpow_nonneg (hη k) _) (by positivity)
    _ = (L * (θ / L)) ^ n k := by rw [hL_def, mul_pow, mul_pow]
    _ = θ ^ n k := by rw [mul_div_cancel₀ _ hL.ne']

end SupExpSmall

/-! ## Two elementary lemmas -/

/-- Pigeonhole: a sequence frequently in a finite set frequently takes one value. -/
private theorem exists_frequently_eq_of_frequently_mem {α : Type*} {s : Set α} (hs : s.Finite)
    {f : ℕ → α} (h : ∃ᶠ k in atTop, f k ∈ s) : ∃ a ∈ s, ∃ᶠ k in atTop, f k = a := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hall : ∀ᶠ k in atTop, ∀ a ∈ s, f k ≠ a :=
    (eventually_all_finite hs).2 fun a ha => not_frequently.1 (hcon a ha)
  exact h (hall.mono fun k hk hks => hk _ hks rfl)

/-- Identity theorem along a convergent sequence: if all derivatives of two holomorphic maps are
asymptotically equal along points `p_k → p₀ ∈ I`, the maps agree on `B_ε`. -/
theorem eqOn_nbhd_of_iteratedDeriv_close {ε : ℝ} (hε : 0 < ε) {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (nbhd ε)) (hh : DifferentiableOn ℂ h (nbhd ε)) {p : ℕ → ℝ}
    {p₀ : ℝ} (hp₀ : p₀ ∈ I) (hp : Tendsto p atTop (𝓝 p₀))
    (hclose : ∀ r, ∀ δ > 0, ∀ᶠ k in atTop,
      ‖iteratedDeriv r g (p k) - iteratedDeriv r h (p k)‖ ≤ δ) :
    EqOn g h (nbhd ε) := by
  refine eqOn_nbhd_of_iteratedDeriv_eq hε hg hh hp₀ fun r => ?_
  have hmem : (p₀ : ℂ) ∈ nbhd ε := ofReal_mem_nbhd hε hp₀
  have hcont : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (nbhd ε) →
      Tendsto (fun k => iteratedDeriv r f (p k)) atTop (𝓝 (iteratedDeriv r f p₀)) := by
    intro f hf
    have : ContinuousAt (iteratedDeriv r f) p₀ := by
      rw [iteratedDeriv_eq_iterate]
      exact ((hf.analyticOnNhd (isOpen_nbhd ε)).iterated_deriv r _ hmem).continuousAt
    exact this.tendsto.comp ((Complex.continuous_ofReal.tendsto p₀).comp hp)
  have hlim := ((hcont g hg).sub (hcont h hh)).norm
  have hle : ∀ δ > 0, ‖iteratedDeriv r g p₀ - iteratedDeriv r h p₀‖ ≤ δ := fun δ hδ =>
    le_of_tendsto hlim (hclose r δ hδ)
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  exact le_of_forall_pos_le_add fun δ hδ => by simpa using hle δ hδ

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

private theorem norm_comp_sub_le_supDist (w v : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    ‖Φ.comp w x - Φ.comp v x‖ ≤ Φ.supDist w v := by
  obtain ⟨R, -, hR⟩ := Φ.exists_comp_bound
  have hmem : ∀ y : I, ((y : ℝ) : ℂ) ∈ closure (nbhd ε) := fun y =>
    subset_closure (ofReal_mem_nbhd Φ.ε_pos y.2)
  refine le_ciSup (f := fun y : I => ‖Φ.comp w ((y : ℝ) : ℂ) - Φ.comp v ((y : ℝ) : ℂ)‖)
    ⟨2 * R, ?_⟩ ⟨x, hx⟩
  rintro _ ⟨y, rfl⟩
  calc _ ≤ ‖Φ.comp w ((y : ℝ) : ℂ)‖ + ‖Φ.comp v ((y : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ R + R := add_le_add (hR _ _ (hmem y)) (hR _ _ (hmem y))
    _ = 2 * R := by ring

/-! ## Condensing sequences -/

/-- A condensing sequence, extracted from the failure of the SESC: words `a_k u_k` and `b_k u_k`
of length `n_k = |a_k| + |u_k|`, with `|a_k| = |b_k| ≥ 1` and different last letters of `a_k`
and `b_k`, whose compositions are `η_k`-close on `I`, where `η_k` is super-exponentially small
in `n_k`; together with `f_{u_k}(I) = [p_k, q_k]` and a limit `p_k → p₀`. -/
structure CondSeq where
  /-- The first words. -/
  a : ℕ → List (Fin N)
  /-- The second words. -/
  b : ℕ → List (Fin N)
  /-- The common suffixes. -/
  u : ℕ → List (Fin N)
  /-- The distances. -/
  η : ℕ → ℝ
  /-- The left endpoints of `f_{u_k}(I)`. -/
  p : ℕ → ℝ
  /-- The right endpoints of `f_{u_k}(I)`. -/
  q : ℕ → ℝ
  /-- The limit of the left endpoints. -/
  p₀ : ℝ
  length_eq : ∀ k, (a k).length = (b k).length
  length_pos : ∀ k, 0 < (a k).length
  getLast?_ne : ∀ k, (a k).getLast? ≠ (b k).getLast?
  η_pos : ∀ k, 0 < η k
  close : ∀ k, ∀ x ∈ I, ‖Φ.comp (a k ++ u k) x - Φ.comp (b k ++ u k) x‖ ≤ η k
  small : SupExpSmall (fun k => (a k).length + (u k).length) η
  p_nonneg : ∀ k, 0 ≤ p k
  p_lt_q : ∀ k, p k < q k
  q_le_one : ∀ k, q k ≤ 1
  cmin_pow_le : ∀ k, Φ.cmin ^ ((a k).length + (u k).length) ≤ q k - p k
  mem_image : ∀ k, ∀ y ∈ Icc (p k) (q k), ∃ x ∈ I, (y : ℂ) = Φ.comp (u k) x
  p₀_mem : p₀ ∈ I
  tendsto_p : Tendsto p atTop (𝓝 p₀)

/-- The failure of the SESC gives a condensing sequence. -/
theorem nonempty_condSeq (h : ¬ Φ.SESC) : Nonempty Φ.CondSeq := by
  have h₁ : ∀ k : ℕ, ∃ n, ∃ i j : Fin n → Fin N, i ≠ j ∧
      Φ.supDist (List.ofFn i) (List.ofFn j) < ((k : ℝ) + 2)⁻¹ ^ n := by
    intro k
    by_contra hk
    simp only [not_exists, not_and, not_lt] at hk
    exact h ⟨_, by positivity, hk⟩
  have h₂ : ∀ k : ℕ, ∃ a b u : List (Fin N), a.length = b.length ∧ 0 < a.length ∧
      a.getLast? ≠ b.getLast? ∧ ∀ x ∈ I,
        ‖Φ.comp (a ++ u) x - Φ.comp (b ++ u) x‖ ≤ ((k : ℝ) + 2)⁻¹ ^ (a.length + u.length) := by
    intro k
    obtain ⟨n, i, j, hij, hlt⟩ := h₁ k
    obtain ⟨a, b, u, hi, hj, hlen, hpos, hlast⟩ :=
      List.exists_decomp_of_ne (i := List.ofFn i) (j := List.ofFn j) (by simp)
        fun h => hij (List.ofFn_injective h)
    have hn : a.length + u.length = n := by rw [← List.length_append, ← hi, List.length_ofFn]
    refine ⟨a, b, u, hlen, hpos, hlast, fun x hx => ?_⟩
    rw [← hi, ← hj, hn]
    exact (Φ.norm_comp_sub_le_supDist _ _ hx).trans hlt.le
  choose a b u hlen hpos hlast hclose using h₂
  have hN : 0 < N := ((a 0).head (List.ne_nil_of_length_pos (hpos 0))).pos
  have hcmin : 0 < Φ.cmin := Φ.cmin_pos hN
  have hcmin1 : Φ.cmin ≤ 1 := (Φ.cmin_le_cmax hN).trans Φ.cmax_lt_one.le
  choose p q hp0 hpq hq1 hmin _ himg using fun k => Φ.exists_image_comp_eq_Icc (u k)
  have hpq' : ∀ k, p k < q k := fun k => by
    have := hmin k
    have := pow_pos hcmin (u k).length
    linarith
  have hsmall : SupExpSmall (fun k => (a k).length + (u k).length)
      fun k => ((k : ℝ) + 2)⁻¹ ^ ((a k).length + (u k).length) := by
    intro θ hθ
    obtain ⟨m, hm⟩ := exists_nat_gt θ⁻¹
    filter_upwards [eventually_ge_atTop m] with k hk
    have hk' : ((k : ℝ) + 2)⁻¹ ≤ θ := by
      rw [inv_le_comm₀ (by positivity) hθ]
      have : (m : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    exact pow_le_pow_left₀ (by positivity) hk' _
  obtain ⟨p₀, hp₀, φ, hφ, hlim⟩ :=
    isCompact_Icc.tendsto_subseq (x := p) fun k => ⟨hp0 k, (hpq k).trans (hq1 k)⟩
  exact ⟨{
    a := a ∘ φ
    b := b ∘ φ
    u := u ∘ φ
    η := fun k => ((φ k : ℝ) + 2)⁻¹ ^ ((a (φ k)).length + (u (φ k)).length)
    p := p ∘ φ
    q := q ∘ φ
    p₀ := p₀
    length_eq := fun k => hlen (φ k)
    length_pos := fun k => hpos (φ k)
    getLast?_ne := fun k => hlast (φ k)
    η_pos := fun k => by positivity
    close := fun k => hclose (φ k)
    small := hsmall.comp hφ.tendsto_atTop
    p_nonneg := fun k => hp0 (φ k)
    p_lt_q := fun k => hpq' (φ k)
    q_le_one := fun k => hq1 (φ k)
    cmin_pow_le := fun k =>
      (pow_le_pow_of_le_one hcmin.le hcmin1 (Nat.le_add_left _ _)).trans (hmin (φ k))
    mem_image := fun k y hy => by
      have hy' : y ∈ Icc (p (φ k)) (q (φ k)) := hy
      rw [← himg (φ k)] at hy'
      obtain ⟨x, hx, rfl⟩ := hy'
      exact ⟨x, hx, (Φ.comp_ofReal _ hx).symm⟩
    p₀_mem := hp₀
    tendsto_p := hlim }⟩

namespace CondSeq

variable {Φ}

/-- Reindexing a condensing sequence along a strictly increasing map. -/
def comp (S : Φ.CondSeq) (φ : ℕ → ℕ) (hφ : StrictMono φ) : Φ.CondSeq where
  a := S.a ∘ φ
  b := S.b ∘ φ
  u := S.u ∘ φ
  η := S.η ∘ φ
  p := S.p ∘ φ
  q := S.q ∘ φ
  p₀ := S.p₀
  length_eq k := S.length_eq (φ k)
  length_pos k := S.length_pos (φ k)
  getLast?_ne k := S.getLast?_ne (φ k)
  η_pos k := S.η_pos (φ k)
  close k := S.close (φ k)
  small := S.small.comp hφ.tendsto_atTop
  p_nonneg k := S.p_nonneg (φ k)
  p_lt_q k := S.p_lt_q (φ k)
  q_le_one k := S.q_le_one (φ k)
  cmin_pow_le k := S.cmin_pow_le (φ k)
  mem_image k := S.mem_image (φ k)
  p₀_mem := S.p₀_mem
  tendsto_p := S.tendsto_p.comp hφ.tendsto_atTop

theorem pos_N (S : Φ.CondSeq) : 0 < N :=
  ((S.a 0).head (List.ne_nil_of_length_pos (S.length_pos 0))).pos

theorem one_le_length (S : Φ.CondSeq) (k : ℕ) : 1 ≤ (S.a k).length + (S.u k).length := by
  have := S.length_pos k
  omega

theorem p_mem (S : Φ.CondSeq) (k : ℕ) : S.p k ∈ I :=
  ⟨S.p_nonneg k, (S.p_lt_q k).le.trans (S.q_le_one k)⟩

/-- Bounded case: if `a_k = a` and `b_k = b` are constant, then `f_a = f_b` on `I`. -/
theorem comp_eq_comp (S : Φ.CondSeq) {a b : List (Fin N)} (ha : ∀ k, S.a k = a)
    (hb : ∀ k, S.b k = b) : ∀ x ∈ I, Φ.comp a x = Φ.comp b x := by
  have hcmin := Φ.cmin_pos S.pos_N
  have hn := S.one_le_length
  have hη : ∀ k, 0 ≤ S.η k := fun k => (S.η_pos k).le
  have heq : EqOn (Φ.comp a) (Φ.comp b) (nbhd ε) := by
    refine eqOn_nbhd_of_iteratedDeriv_close Φ.ε_pos (Φ.differentiableOn_comp a)
      (Φ.differentiableOn_comp b) S.p₀_mem S.tendsto_p fun r δ hδ => ?_
    obtain ⟨K, Q, -, hKQ⟩ := Φ.exists_iteratedDeriv_comp_closeness r a b
    have hs : (0 : ℝ) < (2 : ℝ)⁻¹ ^ r := by positivity
    have h1 := S.small.eventually_le hn one_pos
    have h2 := (S.small.mul_pow_rpow hn hη (2 * (2 + Q)) zero_le_one hs).eventually_lt_pow hn hcmin
    have h3 := (S.small.mul_pow_rpow hn hη (max K 0) zero_le_one hs).eventually_le hn hδ
    filter_upwards [h1, h2, h3] with k h1 h2 h3
    simp only [one_pow, mul_one] at h2 h3
    have hclose : ∀ y ∈ Icc (S.p k) (S.q k), ‖Φ.comp a y - Φ.comp b y‖ ≤ S.η k := by
      intro y hy
      obtain ⟨x, hx, hxy⟩ := S.mem_image k y hy
      rw [hxy]
      simpa only [ha k, hb k, Φ.comp_append, Function.comp_apply] using S.close k x hx
    calc _ ≤ K * S.η k ^ ((2 : ℝ)⁻¹ ^ r) :=
          hKQ _ _ _ (S.p_nonneg k) (S.p_lt_q k) (S.q_le_one k) (S.η_pos k) h1
            (h2.trans_le (S.cmin_pow_le k)) hclose _ (left_mem_Icc.2 (S.p_lt_q k).le)
      _ ≤ max K 0 * S.η k ^ ((2 : ℝ)⁻¹ ^ r) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (hη k) _)
      _ ≤ δ := h3
  intro x hx
  exact heq (ofReal_mem_nbhd Φ.ε_pos hx)

/-- Unbounded case: if `a_k^← → i` and `b_k^← → j`, then `H_i = H_j` on `I`. -/
theorem dualProj_eq (S : Φ.CondSeq) {i j : ℕ → Fin N}
    (hi : Word.TendstoPrefix (fun k => .fin (S.a k).reverse) (.inf i))
    (hj : Word.TendstoPrefix (fun k => .fin (S.b k).reverse) (.inf j)) :
    ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x := by
  have hcmin := Φ.cmin_pos S.pos_N
  have hn := S.one_le_length
  obtain ⟨K₀, η₀, hη₀, hK₀⟩ := Φ.exists_dualProj_closeness
  obtain ⟨C, -, -, hC⟩ := Φ.exists_iteratedDeriv_bounds
  set η' : ℕ → ℝ := fun k => max K₀ 1 * (Φ.cmin⁻¹ ^ 2) ^ ((S.a k).length + (S.u k).length) *
    S.η k ^ ((1 : ℝ) / 4)
  have hη'pos : ∀ k, 0 < η' k := fun k => by
    have := S.η_pos k
    have : 0 < max K₀ 1 := lt_max_of_lt_right one_pos
    positivity
  have hη'small : SupExpSmall (fun k => (S.a k).length + (S.u k).length) η' :=
    S.small.mul_pow_rpow hn (fun k => (S.η_pos k).le) _ (by positivity) (by norm_num)
  have hη'close : ∀ᶠ k in atTop, ∀ y ∈ Icc (S.p k) (S.q k),
      ‖Φ.dualProj (.fin (S.a k).reverse) y - Φ.dualProj (.fin (S.b k).reverse) y‖ ≤ η' k := by
    filter_upwards [S.small.eventually_le hn hη₀] with k hk
    intro y hy
    obtain ⟨x, hx, hxy⟩ := S.mem_image k y hy
    rw [hxy]
    calc _ ≤ K₀ * Φ.cmin⁻¹ ^ (2 * ((S.a k).length + (S.u k).length)) *
          S.η k ^ ((1 : ℝ) / 4) :=
          hK₀ _ _ _ (S.length_eq k) (S.length_pos k) (S.getLast?_ne k) _ (S.η_pos k) hk
            (S.close k) x hx
      _ ≤ η' k := by
          rw [pow_mul]
          have := S.η_pos k
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (by positivity)) (by positivity)
  have hη'nonneg : ∀ k, 0 ≤ η' k := fun k => (hη'pos k).le
  have heq : EqOn (Φ.dualProj (.inf i)) (Φ.dualProj (.inf j)) (nbhd ε) := by
    refine eqOn_nbhd_of_iteratedDeriv_close Φ.ε_pos (Φ.differentiableOn_dualProj _)
      (Φ.differentiableOn_dualProj _) S.p₀_mem S.tendsto_p fun r δ hδ => ?_
    obtain ⟨K, Q, -, hKQ⟩ := Φ.exists_iteratedDeriv_dualProj_closeness r
    have hs : (0 : ℝ) < (2 : ℝ)⁻¹ ^ r := by positivity
    have hδ3 : 0 < δ / 3 := by positivity
    obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 * C r * Φ.cmax ^ m ≤ δ / 3 := by
      have : Tendsto (fun m : ℕ => 2 * C r * Φ.cmax ^ m) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg
          Φ.cmax_lt_one).const_mul (2 * C r)
      exact (this.eventually (ge_mem_nhds hδ3)).exists
    have h1 := hη'small.eventually_le hn one_pos
    have h2 := (hη'small.mul_pow_rpow hn hη'nonneg (2 * (2 + Q)) zero_le_one
      hs).eventually_lt_pow hn hcmin
    have h3 := (hη'small.mul_pow_rpow hn hη'nonneg (max K 0) zero_le_one hs).eventually_le hn hδ3
    filter_upwards [h1, h2, h3, hη'close, hi.eventually_le_commonPrefixLength rfl m,
      hj.eventually_le_commonPrefixLength rfl m] with k h1 h2 h3 h4 h5 h6
    simp only [one_pow, mul_one] at h2 h3
    have e1 := hC r _ (S.p_mem k) _ _ m h5
    have e2 := hC r _ (S.p_mem k) _ _ m h6
    have e3 := hKQ _ _ _ _ _ (S.p_nonneg k) (S.p_lt_q k) (S.q_le_one k) (hη'pos k) h1
      (h2.trans_le (S.cmin_pow_le k)) h4 _ (left_mem_Icc.2 (S.p_lt_q k).le)
    have e3' : K * η' k ^ ((2 : ℝ)⁻¹ ^ r) ≤ max K 0 * η' k ^ ((2 : ℝ)⁻¹ ^ r) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (hη'nonneg k) _)
    set A := iteratedDeriv r (Φ.dualProj (.fin (S.a k).reverse)) (S.p k)
    set B := iteratedDeriv r (Φ.dualProj (.fin (S.b k).reverse)) (S.p k)
    set Hi := iteratedDeriv r (Φ.dualProj (.inf i)) (S.p k)
    set Hj := iteratedDeriv r (Φ.dualProj (.inf j)) (S.p k)
    calc ‖Hi - Hj‖ = ‖-(A - Hi) + (A - B) + (B - Hj)‖ := by congr 1; ring
      _ ≤ ‖-(A - Hi)‖ + ‖A - B‖ + ‖B - Hj‖ := norm_add₃_le
      _ = ‖A - Hi‖ + ‖A - B‖ + ‖B - Hj‖ := by rw [norm_neg]
      _ ≤ δ / 3 + δ / 3 + δ / 3 := by gcongr <;> linarith
      _ = δ := by ring
  intro x hx
  exact heq (ofReal_mem_nbhd Φ.ε_pos hx)

/-- Unbounded case: if `|a_k| → ∞`, then two infinite words with different first letters have
equal dual natural projections on `I`. -/
theorem exists_dualProj_eq (S : Φ.CondSeq) (h : Tendsto (fun k => (S.a k).length) atTop atTop) :
    ∃ i j : ℕ → Fin N, i 0 ≠ j 0 ∧ ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x := by
  obtain ⟨φ₁, hφ₁, w₁, hw₁⟩ := Word.exists_subseq_tendstoPrefix fun k => Word.fin (S.a k).reverse
  obtain ⟨φ₂, hφ₂, w₂, hw₂⟩ :=
    Word.exists_subseq_tendstoPrefix fun k => Word.fin (S.b (φ₁ k)).reverse
  set T := S.comp (φ₁ ∘ φ₂) (hφ₁.comp hφ₂)
  have hT1 : Word.TendstoPrefix (fun k => Word.fin (T.a k).reverse) w₁ := hw₁.comp hφ₂
  have hT2 : Word.TendstoPrefix (fun k => Word.fin (T.b k).reverse) w₂ := hw₂
  have hTlen : Tendsto (fun k => (T.a k).length) atTop atTop :=
    h.comp (hφ₁.comp hφ₂).tendsto_atTop
  have hlen₁ : w₁.length = ⊤ := by
    refine hT1.tendsto_length (ENat.tendsto_nhds_top_iff_natCast_lt.2 fun n => ?_)
    filter_upwards [hTlen.eventually_gt_atTop n] with k hk
    simpa using hk
  have hlen₂ : w₂.length = ⊤ := by
    rw [← hT1.length_eq hT2 fun k => by simp [T.length_eq k]]
    exact hlen₁
  obtain ⟨i, rfl⟩ := Word.eq_inf_of_length_eq_top hlen₁
  obtain ⟨j, rfl⟩ := Word.eq_inf_of_length_eq_top hlen₂
  refine ⟨i, j, fun hij => ?_, T.dualProj_eq hT1 hT2⟩
  obtain ⟨k, hk1, hk2⟩ := ((hT1.eventually_get?_eq 0).and (hT2.eventually_get?_eq 0)).exists
  apply T.getLast?_ne k
  simp only [Word.get?_fin, Word.get?_inf, ← List.head?_eq_getElem?, List.head?_reverse]
    at hk1 hk2
  rw [hk1, hk2, hij]

end CondSeq

/-- The condensation dichotomy behind the proofs of Theorems 1.5 and 2.2. -/
theorem condensation_dichotomy (h : ¬ Φ.SESC) :
    (∃ i j : ℕ → Fin N, i 0 ≠ j 0 ∧ ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x) ∨
      ∃ a b : List (Fin N), a.length = b.length ∧ 0 < a.length ∧ a.getLast? ≠ b.getLast? ∧
        ∀ x ∈ I, Φ.comp a x = Φ.comp b x := by
  obtain ⟨S⟩ := Φ.nonempty_condSeq h
  by_cases hB : ∃ B, ∃ᶠ k in atTop, (S.a k).length ≤ B
  · right
    obtain ⟨B, hB⟩ := hB
    have hfin := (List.finite_length_le (Fin N) B).prod (List.finite_length_le (Fin N) B)
    obtain ⟨⟨a, b⟩, -, hab⟩ := exists_frequently_eq_of_frequently_mem hfin
      (f := fun k => (S.a k, S.b k))
      (hB.mono fun k hk => ⟨hk, (S.length_eq k ▸ hk : (S.b k).length ≤ B)⟩)
    obtain ⟨φ, hφ, hφab⟩ := extraction_of_frequently_atTop hab
    set T := S.comp φ hφ
    have ha : ∀ k, T.a k = a := fun k => congrArg Prod.fst (hφab k)
    have hb : ∀ k, T.b k = b := fun k => congrArg Prod.snd (hφab k)
    refine ⟨a, b, ?_, ?_, ?_, T.comp_eq_comp ha hb⟩
    · rw [← ha 0, ← hb 0]
      exact T.length_eq 0
    · rw [← ha 0]
      exact T.length_pos 0
    · rw [← ha 0, ← hb 0]
      exact T.getLast?_ne 0
  · left
    simp only [not_exists, not_frequently, not_le] at hB
    exact S.exists_dualProj_eq (tendsto_atTop.2 fun B => (hB B).mono fun k hk => hk.le)

/-- Theorem 1.5: if `sup_{x ∈ [0,1]} |H_i(x) - H_j(x)| > 0` for all distinct `i, j ∈ Σ ∪ Σ_*` with
`|i| = |j|`, then `Φ` satisfies the SESC. -/
theorem theorem_1_5
    (h : ∀ i j : Word N, i ≠ j → i.length = j.length →
      0 < ⨆ x : I, ‖Φ.dualProj i ((x : ℝ) : ℂ) - Φ.dualProj j ((x : ℝ) : ℂ)‖) :
    Φ.SESC := by
  by_contra hS
  rcases Φ.condensation_dichotomy hS with ⟨i, j, hij, heq⟩ | ⟨a, b, hlen, -, hlast, heq⟩
  · have hpos := h (.inf i) (.inf j) (fun hw => hij (congrFun (Word.inf.inj hw) 0)) rfl
    have h0 : ∀ x : I,
        ‖Φ.dualProj (.inf i) ((x : ℝ) : ℂ) - Φ.dualProj (.inf j) ((x : ℝ) : ℂ)‖ = 0 :=
      fun x => by rw [heq x x.2, sub_self, norm_zero]
    simp only [h0, Real.iSup_const_zero, lt_irrefl] at hpos
  · have hε := Φ.ε_pos
    have hEq : EqOn (Φ.comp a) (Φ.comp b) (nbhd ε) :=
      eqOn_nbhd_of_eqOn_Icc hε (Φ.differentiableOn_comp a) (Φ.differentiableOn_comp b)
        zero_lt_one subset_rfl heq
    have hD := hEq.deriv (isOpen_nbhd ε)
    have hDD := hD.deriv (isOpen_nbhd ε)
    have hne : Word.fin a.reverse ≠ Word.fin b.reverse := fun hw =>
      hlast (by rw [List.reverse_inj.1 (Word.fin.inj hw)])
    have hpos := h _ _ hne (by simp [hlen])
    have h0 : ∀ x : I,
        ‖Φ.dualProj (.fin a.reverse) ((x : ℝ) : ℂ) - Φ.dualProj (.fin b.reverse) ((x : ℝ) : ℂ)‖
          = 0 := by
      intro x
      have hx := ofReal_mem_nbhd hε x.2
      rw [Φ.dualProj_fin_reverse a (subset_closure hx),
        Φ.dualProj_fin_reverse b (subset_closure hx), hD hx, hDD hx, sub_self, norm_zero]
    simp only [h0, Real.iSup_const_zero, lt_irrefl] at hpos

/-- Theorem 2.2: if the dual IFS satisfies the SSC, then `Φ` satisfies the SESC. -/
theorem theorem_2_2 (h : Φ.DualSSC) : Φ.SESC := by
  by_contra hS
  rcases Φ.condensation_dichotomy hS with ⟨i, j, hij, heq⟩ | ⟨a, b, hlen, -, hlast, heq⟩
  · obtain ⟨x, hx, hne⟩ := (Φ.dualSSC_iff_ne (i 0).pos).1 h i j hij
    exact hne (heq x hx)
  · exact Φ.not_dualSSC_of_comp_eq hlen hlast heq h

end IFS

end AnalyticESC
