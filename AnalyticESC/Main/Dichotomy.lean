module

public import AnalyticESC.Separation
public import AnalyticESC.Main.Closeness
public import AnalyticESC.Dual.Attractor

@[expose] public section

/-!
# Theorems 1.5 and 2.2

The three cases in the proof of Theorem 2.2, after extracting pairs `a_k u_k`, `b_k u_k`
whose compositions are super-exponentially close:

1. Bounded common suffixes: fix `u_k = u`, pass to the limit on the nondegenerate interval
   `f_u(I)`, and apply the identity theorem.
2. Unbounded suffixes and finite limit words: finite order of vanishing at the limiting point
   contradicts the interval-length lower bound unless the two fixed compositions coincide.
3. Infinite limit words: (3.2), Lemma 3.1 and Lemma 2.9 give (3.3), including the denominator
   `|f_u'|^k`; Lemma 2.11 and analyticity then identify the limiting dual projections.

Theorem 1.5 follows from compactness, Lemma 2.6(c) and Theorem 2.2.
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
  length_tendsto : Tendsto (fun k => (a k).length + (u k).length) atTop atTop
  p_nonneg : ∀ k, 0 ≤ p k
  p_lt_q : ∀ k, p k < q k
  q_le_one : ∀ k, q k ≤ 1
  cmin_pow_le : ∀ k, Φ.cmin ^ ((a k).length + (u k).length) ≤ q k - p k
  cmax_pow_ge : ∀ k, q k - p k ≤ Φ.cmax ^ (u k).length
  image_eq : ∀ k, (fun x : ℝ => (Φ.comp (u k) x).re) '' I = Icc (p k) (q k)
  mem_image : ∀ k, ∀ y ∈ Icc (p k) (q k), ∃ x ∈ I, (y : ℂ) = Φ.comp (u k) x
  p₀_mem : p₀ ∈ I
  tendsto_p : Tendsto p atTop (𝓝 p₀)

/-- The failure of the SESC gives a condensing sequence. -/
theorem nonempty_condSeq (h : ¬ Φ.SESC) : Nonempty Φ.CondSeq := by
  have h₁ : ∀ k : ℕ, ∃ n ≥ k, ∃ i j : Fin n → Fin N, i ≠ j ∧
      Φ.supDist (List.ofFn i) (List.ofFn j) < ((k : ℝ) + 2)⁻¹ ^ n :=
    fun k => Φ.exists_close_pair_ge h (by positivity) k
  have h₂ : ∀ k : ℕ, ∃ a b u : List (Fin N), a.length = b.length ∧ 0 < a.length ∧
      a.getLast? ≠ b.getLast? ∧ k ≤ a.length + u.length ∧ ∀ x ∈ I,
        ‖Φ.comp (a ++ u) x - Φ.comp (b ++ u) x‖ ≤ ((k : ℝ) + 2)⁻¹ ^ (a.length + u.length) := by
    intro k
    obtain ⟨n, hnk, i, j, hij, hlt⟩ := h₁ k
    obtain ⟨a, b, u, hi, hj, hlen, hpos, hlast⟩ :=
      List.exists_decomp_of_ne (i := List.ofFn i) (j := List.ofFn j) (by simp)
        fun h => hij (List.ofFn_injective h)
    have hn : a.length + u.length = n := by rw [← List.length_append, ← hi, List.length_ofFn]
    refine ⟨a, b, u, hlen, hpos, hlast, hn ▸ hnk, fun x hx => ?_⟩
    rw [← hi, ← hj, hn]
    exact (Φ.norm_comp_sub_le_supDist _ _ hx).trans hlt.le
  choose a b u hlen hpos hlast hnk hclose using h₂
  have hN : 0 < N := ((a 0).head (List.ne_nil_of_length_pos (hpos 0))).pos
  have hcmin : 0 < Φ.cmin := Φ.cmin_pos hN
  have hcmin1 : Φ.cmin ≤ 1 := (Φ.cmin_le_cmax hN).trans Φ.cmax_lt_one.le
  choose p q hp0 hpq hq1 hmin hmax himg using fun k => Φ.exists_image_comp_eq_Icc (u k)
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
    length_tendsto := tendsto_atTop_mono (fun k => (hφ.id_le k).trans (hnk (φ k))) tendsto_id
    p_nonneg := fun k => hp0 (φ k)
    p_lt_q := fun k => hpq' (φ k)
    q_le_one := fun k => hq1 (φ k)
    cmin_pow_le := fun k =>
      (pow_le_pow_of_le_one hcmin.le hcmin1 (Nat.le_add_left _ _)).trans (hmin (φ k))
    cmax_pow_ge := fun k => hmax (φ k)
    image_eq := fun k => himg (φ k)
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
  length_tendsto := S.length_tendsto.comp hφ.tendsto_atTop
  p_nonneg k := S.p_nonneg (φ k)
  p_lt_q k := S.p_lt_q (φ k)
  q_le_one k := S.q_le_one (φ k)
  cmin_pow_le k := S.cmin_pow_le (φ k)
  cmax_pow_ge k := S.cmax_pow_ge (φ k)
  image_eq k := S.image_eq (φ k)
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

/-- Finite limit words: finite order of vanishing contradicts super-exponential
closeness on intervals whose lengths are at least `c_min^{n_k}`. -/
theorem comp_eq_comp (S : Φ.CondSeq) {a b : List (Fin N)} (ha : ∀ k, S.a k = a)
    (hb : ∀ k, S.b k = b) : ∀ x ∈ I, Φ.comp a x = Φ.comp b x := by
  have hcmin := Φ.cmin_pos S.pos_N
  have hz := ofReal_mem_nbhd Φ.ε_pos S.p₀_mem
  have hA := (Φ.differentiableOn_comp a).analyticOnNhd (isOpen_nbhd ε)
  have hB := (Φ.differentiableOn_comp b).analyticOnNhd (isOpen_nbhd ε)
  suffices heq : Φ.comp a =ᶠ[𝓝 (S.p₀ : ℂ)] Φ.comp b from
    fun x hx => hA.eqOn_of_preconnected_of_eventuallyEq hB (isPreconnected_nbhd ε) hz heq
      (ofReal_mem_nbhd Φ.ε_pos hx)
  by_contra hne
  have hne' : ¬ ∀ᶠ z in 𝓝 (S.p₀ : ℂ), Φ.comp a z - Φ.comp b z = 0 := by
    simpa only [Filter.EventuallyEq, sub_eq_zero] using hne
  obtain ⟨m, g, hg, hg0, hfactor⟩ :=
    ((hA _ hz).sub (hB _ hz)).exists_eventuallyEq_pow_smul_nonzero_iff.2 hne'
  let D := ‖g S.p₀‖ / 2
  have hD : 0 < D := half_pos (norm_pos_iff.2 hg0)
  have hgne : ∀ᶠ z in 𝓝 (S.p₀ : ℂ), D ≤ ‖g z‖ :=
    hg.continuousAt.norm.eventually (le_mem_nhds (half_lt_self (norm_pos_iff.2 hg0)))
  have hu : Tendsto (fun k => (S.u k).length) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro B
    filter_upwards [S.length_tendsto.eventually_ge_atTop (B + a.length)] with k hk
    rw [ha k] at hk
    omega
  have hwidth : Tendsto (fun k => S.q k - S.p k) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).comp hu)
      (fun k => (sub_pos.2 (S.p_lt_q k)).le) S.cmax_pow_ge
  have hq : Tendsto S.q atTop (𝓝 S.p₀) := by
    simpa using hwidth.add S.tendsto_p
  let r (k : ℕ) := if |S.q k - S.p₀| ≤ |S.p k - S.p₀| then S.p k else S.q k
  have hrmem : ∀ k, r k ∈ Icc (S.p k) (S.q k) := by
    intro k
    dsimp [r]
    split_ifs <;> exact ⟨by linarith [S.p_lt_q k], by linarith [S.p_lt_q k]⟩
  have hrlim : Tendsto (fun k => (r k : ℂ)) atTop (𝓝 (S.p₀ : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_of_tendsto_of_tendsto_of_le_of_le S.tendsto_p hq
        (fun k => (hrmem k).1) (fun k => (hrmem k).2))
  have hfar : ∀ k, (S.q k - S.p k) / 2 ≤ |r k - S.p₀| := by
    intro k
    have ht : S.q k - S.p k ≤ |S.q k - S.p₀| + |S.p k - S.p₀| := by
      calc _ = (S.q k - S.p₀) + -(S.p k - S.p₀) := by ring
        _ ≤ _ := add_le_add (le_abs_self _) (neg_le_abs _)
    dsimp [r]
    split_ifs with hr <;> linarith
  have hsmall := (S.small.mul_pow_rpow S.one_le_length (fun k => (S.η_pos k).le)
    ((2 : ℝ) ^ m / D) zero_le_one one_pos).eventually_lt_pow S.one_le_length (pow_pos hcmin m)
  obtain ⟨k, hkfac, hkg, hksmall⟩ :=
    ((hrlim.eventually hfactor).and ((hrlim.eventually hgne).and hsmall)).exists
  have hclose : ‖Φ.comp a (r k) - Φ.comp b (r k)‖ ≤ S.η k := by
    obtain ⟨x, hx, hxy⟩ := S.mem_image k _ (hrmem k)
    rw [hxy]
    simpa only [ha k, hb k, Φ.comp_append, Function.comp_apply] using S.close k x hx
  have hlower : D * (Φ.cmin ^ ((S.a k).length + (S.u k).length) / 2) ^ m ≤ S.η k := by
    calc _ ≤ ‖g (r k)‖ * |r k - S.p₀| ^ m :=
        mul_le_mul hkg (pow_le_pow_left₀ (by positivity)
          ((div_le_div_of_nonneg_right (S.cmin_pow_le k) (by norm_num)).trans (hfar k)) _)
          (by positivity) (norm_nonneg _)
      _ = ‖Φ.comp a (r k) - Φ.comp b (r k)‖ := by
        change ‖g (r k)‖ * |r k - S.p₀| ^ m = ‖(Φ.comp a - Φ.comp b) (r k)‖
        rw [hkfac, norm_smul, norm_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact mul_comm _ _
      _ ≤ S.η k := hclose
  simp only [one_pow, mul_one, Real.rpow_one] at hksmall
  rw [div_pow, ← mul_div_assoc] at hlower
  have hpow : (Φ.cmin ^ m) ^ ((S.a k).length + (S.u k).length) =
      (Φ.cmin ^ ((S.a k).length + (S.u k).length)) ^ m := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hpow] at hksmall
  have htwo : (0 : ℝ) < 2 ^ m := by positivity
  have hlo := (div_le_iff₀ htwo).1 hlower
  have hhi := (div_lt_iff₀ hD).1 (show (2 ^ m * S.η k) / D <
    (Φ.cmin ^ ((S.a k).length + (S.u k).length)) ^ m by simpa [div_mul_eq_mul_div] using hksmall)
  nlinarith

/-- Equation (3.2), with a positive super-exponentially small bound on the image interval. -/
theorem exists_dualProj_small (S : Φ.CondSeq) :
    ∃ η' : ℕ → ℝ, (∀ k, 0 < η' k) ∧
      SupExpSmall (fun k => (S.a k).length + (S.u k).length) η' ∧
      ∀ᶠ k in atTop, ∀ y ∈ Icc (S.p k) (S.q k),
        ‖Φ.dualProj (.fin (S.a k).reverse) y - Φ.dualProj (.fin (S.b k).reverse) y‖ ≤ η' k := by
  have hcmin := Φ.cmin_pos S.pos_N
  have hn := S.one_le_length
  obtain ⟨K₀, η₀, hη₀, hK₀⟩ := Φ.exists_dualProj_closeness
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
  exact ⟨η', hη'pos, hη'small, hη'close⟩

/-- Bounded common suffixes: pass to the limit on the fixed nondegenerate image
interval using Lemma 2.11, then use the analytic identity theorem. -/
theorem dualProj_eq_of_fixed_suffix (S : Φ.CondSeq) {u : List (Fin N)}
    (hu : ∀ k, S.u k = u) {i j : ℕ → Fin N}
    (hi : Word.TendstoPrefix (fun k => .fin (S.a k).reverse) (.inf i))
    (hj : Word.TendstoPrefix (fun k => .fin (S.b k).reverse) (.inf j)) :
    ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x := by
  obtain ⟨η', hη'pos, hη'small, hη'close⟩ := S.exists_dualProj_small
  obtain ⟨C, -, -, hC⟩ := Φ.exists_iteratedDeriv_bounds
  have hsub : Icc (S.p 0) (S.q 0) ⊆ I := Icc_subset_Icc (S.p_nonneg 0) (S.q_le_one 0)
  have heq : ∀ y ∈ Icc (S.p 0) (S.q 0), Φ.dualProj (.inf i) y = Φ.dualProj (.inf j) y := by
    intro y hy
    have hyk : ∀ k, y ∈ Icc (S.p k) (S.q k) := by
      intro k
      rw [← S.image_eq k, hu k, ← hu 0, S.image_eq 0]
      exact hy
    rw [← sub_eq_zero, ← norm_le_zero_iff]
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hδ3 : 0 < δ / 3 := by positivity
    obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 * C 0 * Φ.cmax ^ m ≤ δ / 3 := by
      have ht : Tendsto (fun m : ℕ => 2 * C 0 * Φ.cmax ^ m) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg
          Φ.cmax_lt_one).const_mul (2 * C 0)
      exact (ht.eventually (ge_mem_nhds hδ3)).exists
    obtain ⟨k, hkη, hkclose, hki, hkj⟩ := ((hη'small.eventually_le S.one_le_length hδ3).and
      (hη'close.and ((hi.eventually_le_commonPrefixLength rfl m).and
        (hj.eventually_le_commonPrefixLength rfl m)))).exists
    have e1 := hC 0 y (hsub hy) _ _ m hki
    have e2 := hC 0 y (hsub hy) _ _ m hkj
    simp only [iteratedDeriv_zero] at e1 e2
    have e3 := hkclose y (hyk k)
    set A := Φ.dualProj (.fin (S.a k).reverse) y
    set B := Φ.dualProj (.fin (S.b k).reverse) y
    set Hi := Φ.dualProj (.inf i) y
    set Hj := Φ.dualProj (.inf j) y
    calc ‖Hi - Hj‖ = ‖-(A - Hi) + (A - B) + (B - Hj)‖ := by congr 1; ring
      _ ≤ ‖-(A - Hi)‖ + ‖A - B‖ + ‖B - Hj‖ := norm_add₃_le
      _ = ‖A - Hi‖ + ‖A - B‖ + ‖B - Hj‖ := by rw [norm_neg]
      _ ≤ 0 + δ := by linarith
  intro x hx
  exact eqOn_nbhd_of_eqOn_Icc Φ.ε_pos (Φ.differentiableOn_dualProj _)
    (Φ.differentiableOn_dualProj _) (S.p_lt_q 0) hsub heq (ofReal_mem_nbhd Φ.ε_pos hx)

/-- Unbounded case: if `a_k^← → i` and `b_k^← → j`, then `H_i = H_j` on `I`. -/
theorem dualProj_eq (S : Φ.CondSeq) {i j : ℕ → Fin N}
    (hi : Word.TendstoPrefix (fun k => .fin (S.a k).reverse) (.inf i))
    (hj : Word.TendstoPrefix (fun k => .fin (S.b k).reverse) (.inf j)) :
    ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x := by
  have hcmin := Φ.cmin_pos S.pos_N
  have hn := S.one_le_length
  obtain ⟨η', hη'pos, hη'small, hη'close⟩ := S.exists_dualProj_small
  have hη'nonneg : ∀ k, 0 ≤ η' k := fun k => (hη'pos k).le
  obtain ⟨C, -, -, hC⟩ := Φ.exists_iteratedDeriv_bounds
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
    have h3 := (hη'small.mul_pow_rpow hn hη'nonneg (max K 0) (pow_nonneg (inv_nonneg.2 hcmin.le) r) hs).eventually_le hn hδ3
    filter_upwards [h1, h2, h3, hη'close, hi.eventually_le_commonPrefixLength rfl m,
      hj.eventually_le_commonPrefixLength rfl m] with k h1 h2 h3 h4 h5 h6
    simp only [one_pow, mul_one] at h2 h3
    have e1 := hC r _ (S.p_mem k) _ _ m h5
    have e2 := hC r _ (S.p_mem k) _ _ m h6
    have hall := hKQ _ _ _ _ _ (S.p_nonneg k) (S.p_lt_q k) (S.q_le_one k) (hη'pos k) h1
      (h2.trans_le (S.cmin_pow_le k)) h4
    obtain ⟨x, hx, hxp⟩ := S.mem_image k _ (left_mem_Icc.2 (S.p_lt_q k).le)
    have hwhole : ∀ y ∈ (fun t : ℝ => (Φ.comp (S.u k) t).re) '' I,
        ‖iteratedDeriv r (Φ.dualProj (.fin (S.a k).reverse)) y -
          iteratedDeriv r (Φ.dualProj (.fin (S.b k).reverse)) y‖ ≤
            max K 0 * η' k ^ ((2 : ℝ)⁻¹ ^ r) := by
      intro y hy
      rw [S.image_eq k] at hy
      exact (hall y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (hη'nonneg k) _))
    obtain ⟨e3a, e3b⟩ := Φ.norm_iteratedDeriv_sub_le_on_image S.pos_N r (S.u k)
      (le_max_right _ _) (Real.rpow_nonneg (hη'nonneg k) _) hwhole hx
    have hbase : 1 ≤ Φ.cmin⁻¹ ^ r := one_le_pow₀ ((one_le_inv₀ hcmin).2
      ((Φ.cmin_le_cmax S.pos_N).trans Φ.cmax_lt_one.le))
    have e3 := e3a.trans (e3b.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (Nat.le_add_left (S.u k).length (S.a k).length))
        (le_max_right _ _)) (Real.rpow_nonneg (hη'nonneg k) _)))
    rw [← hxp] at e3
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
theorem exists_dualProj_eq (S : Φ.CondSeq) (h : Tendsto (fun k => (S.a k).length) atTop atTop)
    (hcase : (∃ u, ∀ k, S.u k = u) ∨ Tendsto (fun k => (S.u k).length) atTop atTop) :
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
  have heq : ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x := by
    rcases hcase with ⟨u, hu⟩ | hu
    · exact T.dualProj_eq_of_fixed_suffix (fun k => hu ((φ₁ ∘ φ₂) k)) hT1 hT2
    · exact T.dualProj_eq hT1 hT2
  refine ⟨i, j, fun hij => ?_, heq⟩
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
  by_cases hU : ∃ B, ∃ᶠ k in atTop, (S.u k).length ≤ B
  · left
    obtain ⟨B, hB⟩ := hU
    obtain ⟨u, -, hu⟩ := exists_frequently_eq_of_frequently_mem
      (List.finite_length_le (Fin N) B) hB
    obtain ⟨φ, hφ, hφu⟩ := extraction_of_frequently_atTop hu
    let T := S.comp φ hφ
    have hTu : ∀ k, T.u k = u := hφu
    have hTa : Tendsto (fun k => (T.a k).length) atTop atTop := by
      apply Filter.tendsto_atTop.2
      intro B
      filter_upwards [T.length_tendsto.eventually_ge_atTop (B + u.length)] with k hk
      rw [hTu k] at hk
      omega
    exact T.exists_dualProj_eq hTa (Or.inl ⟨u, hTu⟩)
  · have hU : Tendsto (fun k => (S.u k).length) atTop atTop := by
      simp only [not_exists, not_frequently, not_le] at hU
      exact Filter.tendsto_atTop.2 fun B => (hU B).mono fun k hk => hk.le
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
      exact S.exists_dualProj_eq (Filter.tendsto_atTop.2 fun B => (hB B).mono fun k hk => hk.le) (Or.inr hU)

/-- Theorem 2.2: if the dual IFS satisfies the SSC, then `Φ` satisfies the SESC. -/
theorem theorem_2_2 (h : Φ.DualSSC) : Φ.SESC := by
  by_contra hS
  rcases Φ.condensation_dichotomy hS with ⟨i, j, hij, heq⟩ | ⟨a, b, hlen, -, hlast, heq⟩
  · obtain ⟨x, hx, hne⟩ := (Φ.dualSSC_iff_ne (i 0).pos).1 h i j hij
    exact hne (heq x hx)
  · exact Φ.not_dualSSC_of_comp_eq hlen hlast heq h

/-- Theorem 1.5: if `sup_{x ∈ [0,1]} |H_i(x) - H_j(x)| > 0` for all distinct `i, j ∈ Σ ∪ Σ_*` with
`|i| = |j|`, then `Φ` satisfies the SESC. -/
theorem theorem_1_5
    (h : ∀ i j : Word N, i ≠ j → i.length = j.length →
      0 < ⨆ x : I, ‖Φ.dualProj i ((x : ℝ) : ℂ) - Φ.dualProj j ((x : ℝ) : ℂ)‖) :
    Φ.SESC := by
  by_cases hN : 0 < N
  · apply Φ.theorem_2_2
    apply (Φ.dualSSC_iff_exists_delta hN).2
    apply Φ.dualProj_ne_iff_exists_delta.1
    intro i j hij
    by_contra heq
    push Not at heq
    have hpos := h (.inf i) (.inf j) (fun hw => hij (congrFun (Word.inf.inj hw) 0)) rfl
    have h0 : ∀ x : I,
        ‖Φ.dualProj (.inf i) ((x : ℝ) : ℂ) - Φ.dualProj (.inf j) ((x : ℝ) : ℂ)‖ = 0 :=
      fun x => by rw [heq x x.2, sub_self, norm_zero]
    simp only [h0, Real.iSup_const_zero, lt_irrefl] at hpos
  · refine ⟨1, one_pos, fun n i j hij => ?_⟩
    exfalso
    apply hij
    funext k
    exact False.elim (hN (i k).pos)

end IFS

end AnalyticESC
