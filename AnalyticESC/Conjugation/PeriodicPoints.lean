module

public import AnalyticESC.Conjugation.ExactOverlaps
public import AnalyticESC.Conjugation.Zeros

@[expose] public section

/-!
# Theorem 1.12 (a) along periodic points

The paper's proof of Theorem 1.12 (a). Let `g` be analytic and injective on `[0,1]` with
`g ∘ f_k = λ_k g + t_k` there for every letter `k`, so that `g ∘ f_w = λ_w g + t_w` for every
finite word `w`.

1. Differentiating gives `g'(f_k(x)) f_k'(x) = λ_k g'(x)`, so every `f_k` maps the zero set of
   `g'` in `[0,1]` into itself. This set is closed and `π(i) = lim f_{i₁ ⋯ iₙ}(x)` for every
   `x ∈ [0,1]`, so it contains the attractor once it is nonempty. A non-singleton attractor is
   infinite, and the identity theorem would give `g' ≡ 0`, against injectivity. Hence `g' ≠ 0`
   on `[0,1]`.
2. At the fixed point `p` of `f_w`, `f_w'(p) = λ_w`, and differentiating twice with (2.7) gives
   `g''(p)/g'(p) = H_{w^←}(p)/(1 - f_w'(p))`.
3. For `i, j ∈ Σ` let `kₙ = i₁ ⋯ iₙ jₙ ⋯ j₁`. The fixed point `p_{kₙ}` lies in
   `f_{i₁ ⋯ iₙ}([0,1])`, so `p_{kₙ} → π(i)`; `f_{kₙ}'(p_{kₙ}) → 0`; and
   `H_{j₁ ⋯ jₙ iₙ ⋯ i₁}(p_{kₙ}) → H_j(π(i))` by the bound of Lemma 2.4, which is uniform on
   `cl B_ε` and holds for a finite and an infinite word with a common prefix, and the continuity
   of `H_j`. As `g''/g'` is continuous at `π(i)`, `g''/g' = H_j` on the attractor for every `j`,
   and the identity theorem gives `H_j = H_k` on `[0,1]`.

The converse follows the paper as well: `H = H_{k^∞} = Ĥ_{f_k}` for every letter `k`, Lemma 5.1
gives an invertible `g` with `g'' = H g'`, and the second part of Lemma 5.1 conjugates each `f_k`
to `y ↦ f_k'(p_k) y + g(p_k)(1 - f_k'(p_k))`. `theorem_1_12` states Theorem 1.12 (a) and (b) for
systems whose attractor is not a singleton.
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-! ## Analytic maps on `[0,1]` -/

/-- A map analytic near `[0,1]` with infinitely many zeros in `[0,1]` vanishes on `[0,1]`. -/
private theorem periodic_eqOn_zero_of_infinite {u : ℝ → ℝ} (hu : AnalyticOnNhd ℝ u I)
    (hinf : (I ∩ u ⁻¹' {0}).Infinite) : EqOn u 0 I := by
  obtain ⟨x₀, hx₀, hacc⟩ := hinf.exists_accPt_of_subset_isCompact isCompact_Icc inter_subset_left
  exact hu.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_Icc hx₀
    ((accPt_iff_frequently_nhdsNE.1 hacc).mono fun z hz => hz.2)

/-- Maps that agree on `[0,1]` and have derivatives at a point of `[0,1]` have the same
derivative there. -/
private theorem periodic_hasDerivAt_unique {u v : ℝ → ℝ} {a b x : ℝ} (hx : x ∈ I)
    (hu : HasDerivAt u a x) (hv : HasDerivAt v b x) (huv : ∀ y ∈ I, u y = v y) : a = b :=
  (uniqueDiffOn_Icc zero_lt_one x hx).eq_deriv _ hu.hasDerivWithinAt
    (hv.hasDerivWithinAt.congr huv (huv x hx))

/-- At points of `[0,1]`, the derivative of a map of the class is real, nonzero and of modulus
less than one. -/
private theorem periodic_re_deriv_ne_zero_abs_lt_one {ε : ℝ} {f : ℂ → ℂ} (hε : 0 < ε)
    (hf : InClass ε f) {x : ℝ} (hx : x ∈ I) :
    (deriv f x).re ≠ 0 ∧ |(deriv f x).re| < 1 := by
  have hcl : (x : ℂ) ∈ closure (nbhd ε) := subset_closure (ofReal_mem_nbhd hε hx)
  have him : (deriv f x).im = 0 := im_deriv_eq_zero (isOpen_nbhd _) hf.differentiableOn
    hf.im_eq_zero (ofReal_mem_nbhd (by linarith) hx)
  exact ⟨fun h => hf.deriv_ne_zero _ hcl (Complex.ext h him),
    (Complex.abs_re_le_norm _).trans_lt (hf.norm_deriv_lt_one _ hcl)⟩

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-! ## Compositions on `[0,1]` -/

/-- `f_{k w} = f_k ∘ f_w` on `[0,1]`, for the real maps. -/
private theorem periodic_re_comp_cons (k : Fin N) (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    (Φ.comp (k :: w) x).re = Φ.realMaps k (Φ.comp w x).re := by
  show (Φ.f k (Φ.comp w x)).re = (Φ.f k ((Φ.comp w x).re : ℂ)).re
  rw [← Φ.comp_ofReal w hx]

/-- `|f_w(x) - f_w(y)| ≤ c_max^{|w|} |x - y|` on `[0,1]`. -/
private theorem periodic_abs_re_comp_sub_le (w : List (Fin N)) {x y : ℝ} (hx : x ∈ I)
    (hy : y ∈ I) : |(Φ.comp w x).re - (Φ.comp w y).re| ≤ Φ.cmax ^ w.length * |x - y| := by
  have h := Φ.norm_comp_sub_le w (ofReal_mem_nbhd Φ.ε_pos hx) (ofReal_mem_nbhd Φ.ε_pos hy)
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  rw [← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans h

/-- `π(i) = lim f_{i₁ ⋯ i_{mₙ}}(zₙ)` for points `zₙ ∈ [0,1]` and lengths `mₙ → ∞`. -/
theorem tendsto_re_comp_natProj (i : ℕ → Fin N) {m : ℕ → ℕ} (hm : Tendsto m atTop atTop)
    {z : ℕ → ℝ} (hz : ∀ n, z n ∈ I) :
    Tendsto (fun n => (Φ.comp (List.ofFn fun k : Fin (m n) => i k) (z n)).re) atTop
      (𝓝 (Φ.natProj i)) := by
  have h0 : (0 : ℝ) ∈ I := left_mem_Icc.2 zero_le_one
  refine ((Φ.tendsto_natProj i).comp hm).congr_dist (squeeze_zero (fun n => dist_nonneg)
    (fun n => ?_) ((tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).comp hm))
  have h := Φ.periodic_abs_re_comp_sub_le (List.ofFn fun k : Fin (m n) => i k) h0 (hz n)
  rw [List.length_ofFn, Complex.ofReal_zero] at h
  have h1 : |0 - z n| ≤ 1 := by
    rw [zero_sub, abs_neg, abs_le]
    constructor <;> linarith [(hz n).1, (hz n).2]
  rw [Function.comp_apply, Function.comp_apply, Real.dist_eq]
  calc _ ≤ Φ.cmax ^ m n * |0 - z n| := h
    _ ≤ Φ.cmax ^ m n * 1 := mul_le_mul_of_nonneg_left h1 (pow_nonneg Φ.cmax_nonneg _)
    _ = _ := mul_one _

/-- `g ∘ f_w = λ_w g + t_w` on `[0,1]` for every finite word `w` if `g ∘ f_k = λ_k g + t_k` on
`[0,1]` for every letter `k`. -/
theorem exists_conj_comp {g : ℝ → ℝ} {lam t : Fin N → ℝ}
    (hconj : ∀ k, ∀ x ∈ I, g (Φ.realMaps k x) = lam k * g x + t k) (w : List (Fin N)) :
    ∃ a b : ℝ, ∀ x ∈ I, g (Φ.comp w x).re = a * g x + b := by
  induction w with
  | nil => exact ⟨1, 0, fun x _ => by simp⟩
  | cons k w ih =>
    obtain ⟨a, b, h⟩ := ih
    refine ⟨lam k * a, lam k * b + t k, fun x hx => ?_⟩
    rw [Φ.periodic_re_comp_cons k w hx, hconj k _ (Φ.re_comp_mem_I w hx), h x hx]
    ring

/-! ## The first step: `g'` has no zero -/

/-- Theorem 1.12 (a), first step of the proof: if `g` is analytic and injective on `[0,1]`,
`g ∘ f_k = λ_k g + t_k` on `[0,1]` for every `k`, and the attractor is not a singleton, then `g'`
has no zero in `[0,1]`. -/
theorem deriv_ne_zero_of_conj_of_nonsingleton (hN : 0 < N) (hnd : ¬ ∃ x, Φ.attractor = {x})
    {g : ℝ → ℝ} (hg : IsAnalyticCoord g) {lam t : Fin N → ℝ}
    (hconj : ∀ k, ∀ x ∈ I, g (Φ.realMaps k x) = lam k * g x + t k) :
    ∀ x ∈ I, deriv g x ≠ 0 := by
  obtain ⟨hga, hinj⟩ := hg
  intro z hz hgz
  set Z := I ∩ deriv g ⁻¹' {0} with hZ
  have hZc : IsClosed Z := ContinuousOn.preimage_isClosed_of_isClosed
    (fun x hx => (hga x hx).deriv.continuousAt.continuousWithinAt) isClosed_Icc isClosed_singleton
  -- `g'(f_k(x)) f_k'(x) = λ_k g'(x)` and `f_k' ≠ 0`, so every `f_k` maps `Z` into itself
  have hinv : ∀ k, MapsTo (Φ.realMaps k) Z Z := by
    rintro k x ⟨hx, hx0⟩
    have hFx : Φ.realMaps k x ∈ I := (Φ.inClass k).re_mem_I x hx
    have hd : HasDerivAt (Φ.realMaps k) (deriv (Φ.f k) x).re x :=
      hasDerivAt_re_ofReal (Φ.differentiableAt_f k (subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)))
    have hid := periodic_hasDerivAt_unique hx ((hga _ hFx).differentiableAt.hasDerivAt.comp x hd)
      (((hga x hx).differentiableAt.hasDerivAt.const_mul (lam k)).add_const (t k)) (hconj k)
    refine ⟨hFx, ?_⟩
    simp only [mem_preimage, mem_singleton_iff] at hx0 ⊢
    rw [hx0, mul_zero] at hid
    exact (mul_eq_zero.1 hid).resolve_right
      (periodic_re_deriv_ne_zero_abs_lt_one Φ.ε_pos (Φ.inClass k) hx).1
  -- hence so does every composition `f_w`
  have hinvw : ∀ w : List (Fin N), MapsTo (fun x : ℝ => (Φ.comp w x).re) Z Z := by
    intro w
    induction w with
    | nil => intro x hx; simpa using hx
    | cons k w ih =>
      intro x hx
      show (Φ.comp (k :: w) x).re ∈ Z
      rw [Φ.periodic_re_comp_cons k w hx.1]
      exact hinv k (ih hx)
  -- `Z` is closed and contains `z`, so it contains `π(i) = lim f_{i₁ ⋯ iₙ}(z)` for every `i`
  have hΛ : Φ.attractor ⊆ Z := by
    rintro _ ⟨i, rfl⟩
    exact hZc.mem_of_tendsto (Φ.tendsto_re_comp_natProj i tendsto_id fun _ => hz)
      (Eventually.of_forall fun n => hinvw _ ⟨hz, hgz⟩)
  -- the attractor is infinite, so `g' ≡ 0` on `[0,1]` and `g` is constant there
  have hzero := periodic_eqOn_zero_of_infinite (fun x hx => (hga x hx).deriv)
    ((Φ.attractor_infinite hN hnd).mono hΛ)
  have hconst : ∀ x ∈ I, g x = g 0 := by
    apply constant_of_derivWithin_zero
      (fun x hx => (hga x hx).differentiableAt.differentiableWithinAt)
    intro x hx
    have hxI : x ∈ I := Ico_subset_Icc_self hx
    rw [(hga x hxI).differentiableAt.derivWithin (uniqueDiffOn_Icc zero_lt_one x hxI)]
    exact hzero hxI
  exact one_ne_zero (hinj (right_mem_Icc.2 zero_le_one) (left_mem_Icc.2 zero_le_one)
    (hconst 1 (right_mem_Icc.2 zero_le_one)))

/-! ## The second step: periodic points -/

/-- Theorem 1.12 (a), second step of the proof: if `g ∘ f_w = λ g + t` on `[0,1]` for a nonempty
word `w` and `g'` does not vanish at the fixed point `p` of `f_w`, then `f_w'(p) = λ` and
`g''(p)/g'(p) = H_{w^←}(p)/(1 - f_w'(p))`. -/
theorem deriv_deriv_div_deriv_eq_of_fixedPoint {g : ℝ → ℝ} (hg : AnalyticOnNhd ℝ g I)
    {w : List (Fin N)} (hw : w ≠ []) {a b : ℝ}
    (hconj : ∀ x ∈ I, g (Φ.comp w x).re = a * g x + b) {p : ℝ} (hp : p ∈ I)
    (hfp : Φ.comp w p = p) (hgp : deriv g p ≠ 0) :
    (deriv (Φ.comp w) p).re = a ∧
      ((deriv (deriv g) p / deriv g p : ℝ) : ℂ) =
        Φ.dualProj (.fin w.reverse) p / (1 - deriv (Φ.comp w) p) := by
  have hmem : ∀ {x : ℝ}, x ∈ I → (x : ℂ) ∈ nbhd ε := fun hx => ofReal_mem_nbhd Φ.ε_pos hx
  obtain ⟨U, hUo, hU, hd⟩ := Φ.exists_differentiableOn_comp w
  have hUx : ∀ {x : ℝ}, x ∈ I → (x : ℂ) ∈ U := fun hx => hU (subset_closure (hmem hx))
  -- the real maps `F = Re f_w`, `F₁ = Re f_w'` and `F₂ = Re f_w''`
  set F : ℝ → ℝ := fun y => (Φ.comp w y).re with hF
  set F₁ : ℝ → ℝ := fun y => (deriv (Φ.comp w) y).re with hF₁
  set F₂ : ℝ → ℝ := fun y => (deriv (deriv (Φ.comp w)) y).re with hF₂
  have hFd : ∀ x ∈ I, HasDerivAt F (F₁ x) x := fun x hx =>
    hasDerivAt_re_ofReal ((hd _ (hUx hx)).differentiableAt (hUo.mem_nhds (hUx hx)))
  have hF₁d : ∀ x ∈ I, HasDerivAt F₁ (F₂ x) x := fun x hx =>
    hasDerivAt_re_ofReal (((hd.deriv hUo) _ (hUx hx)).differentiableAt (hUo.mem_nhds (hUx hx)))
  have hFI : ∀ x ∈ I, F x ∈ I := fun x hx => Φ.re_comp_mem_I w hx
  have hgd : ∀ y ∈ I, HasDerivAt g (deriv g y) y := fun y hy =>
    (hg y hy).differentiableAt.hasDerivAt
  have hg₁d : ∀ y ∈ I, HasDerivAt (deriv g) (deriv (deriv g) y) y := fun y hy =>
    (hg y hy).deriv.differentiableAt.hasDerivAt
  -- `g'(f_w(x)) f_w'(x) = λ g'(x)` on `[0,1]`
  have hA : ∀ x ∈ I, deriv g (F x) * F₁ x = a * deriv g x := fun x hx =>
    periodic_hasDerivAt_unique hx ((hgd _ (hFI x hx)).comp x (hFd x hx))
      (((hgd x hx).const_mul a).add_const b) hconj
  -- `g''(f_w(p)) f_w'(p)² + g'(f_w(p)) f_w''(p) = λ g''(p)`
  have hB : deriv (deriv g) (F p) * F₁ p * F₁ p + deriv g (F p) * F₂ p =
      a * deriv (deriv g) p :=
    periodic_hasDerivAt_unique hp (((hg₁d _ (hFI p hp)).comp p (hFd p hp)).mul (hF₁d p hp))
      ((hg₁d p hp).const_mul a) hA
  have hFp : F p = p := by
    show (Φ.comp w p).re = p
    rw [hfp, Complex.ofReal_re]
  -- `f_w'(p) = λ`, as `g'(p) ≠ 0`
  have hF₁p : F₁ p = a := by
    have h := hA p hp
    rw [hFp] at h
    exact mul_left_cancel₀ hgp (by rw [h, mul_comm])
  refine ⟨hF₁p, ?_⟩
  -- `f_w'(p)` and `f_w''(p)` are real, with `0 < |f_w'(p)| < 1`
  have hcl : (p : ℂ) ∈ closure (nbhd ε) := subset_closure (hmem hp)
  have h₁ : deriv (Φ.comp w) p = (F₁ p : ℂ) :=
    Complex.ext (by simp [hF₁]) (by simp [hF₁, Φ.im_deriv_comp_ofReal w (hmem hp)])
  have h₂ : deriv (deriv (Φ.comp w)) p = (F₂ p : ℂ) := by
    have him : (deriv (deriv (Φ.comp w)) p).im = 0 :=
      im_deriv_eq_zero (isOpen_nbhd ε) ((Φ.differentiableOn_comp w).deriv (isOpen_nbhd ε))
        (fun s hs => Φ.im_deriv_comp_ofReal w hs) (hmem hp)
    exact Complex.ext (by simp [hF₂]) (by simp [hF₂, him])
  have hne : F₁ p ≠ 0 := fun h0 =>
    Φ.deriv_comp_ne_zero w hcl (by rw [h₁, h0, Complex.ofReal_zero])
  have hlt : |F₁ p| < 1 :=
    calc |F₁ p| ≤ ‖deriv (Φ.comp w) p‖ := Complex.abs_re_le_norm _
      _ ≤ Φ.cmax ^ w.length := Φ.norm_deriv_comp_le w hcl
      _ < 1 := pow_lt_one₀ Φ.cmax_nonneg Φ.cmax_lt_one (List.length_pos_iff.2 hw).ne'
  have hne' : 1 - F₁ p ≠ 0 := fun h0 => by
    rw [sub_eq_zero] at h0
    rw [← h0, abs_one] at hlt
    exact lt_irrefl _ hlt
  -- (2.7): `H_{w^←}(p) = f_w''(p)/f_w'(p)`
  rw [Φ.dualProj_fin_reverse w hcl, h₁, h₂,
    show (F₂ p : ℂ) / (F₁ p : ℂ) / (1 - (F₁ p : ℂ)) = ((F₂ p / F₁ p / (1 - F₁ p) : ℝ) : ℂ) by
      push_cast; ring]
  congr 1
  rw [hFp, ← hF₁p] at hB
  rw [div_div, div_eq_div_iff hgp (mul_ne_zero hne hne')]
  linear_combination -hB

/-! ## The third step: the limit along periodic points -/

/-- Theorem 1.12 (a), third step of the proof: if `Φ` is conjugated to a self-similar IFS and its
attractor is not a singleton, then all dual natural projections agree on `[0,1]`. -/
theorem dualProj_eq_of_conjSelfSimilar (hnd : ¬ ∃ x, Φ.attractor = {x})
    (h : ConjSelfSimilar Φ.realMaps) :
    ∀ i j : ℕ → Fin N, ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x := by
  intro i₀ j₀
  have hN : 0 < N := (i₀ 0).pos
  have hε := Φ.ε_pos
  obtain ⟨g, hg, lam, t, hconj⟩ := h
  have hconj' : ∀ k, ∀ x ∈ I, g (Φ.realMaps k x) = lam k * g x + t k := fun k => (hconj k).2.2
  -- the first step
  have hg' := Φ.deriv_ne_zero_of_conj_of_nonsingleton hN hnd hg hconj'
  obtain ⟨M, -, -, hM⟩ := Φ.exists_dualProj_bounds
  have hc : Tendsto (fun n : ℕ => Φ.cmax ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).comp
      (tendsto_add_atTop_nat 1)
  -- `g''/g' = H_j` at `π(i)`
  have key : ∀ i j : ℕ → Fin N,
      ((deriv (deriv g) (Φ.natProj i) / deriv g (Φ.natProj i) : ℝ) : ℂ) =
        Φ.dualProj (.inf j) (Φ.natProj i) := by
    intro i j
    have hπ : Φ.natProj i ∈ I := Φ.attractor_subset_I ⟨i, rfl⟩
    -- the words `kₙ = i₁ ⋯ i_{n+1} j_{n+1} ⋯ j₁`
    set u : ℕ → List (Fin N) := fun n => List.ofFn fun m : Fin (n + 1) => i m with hu
    set v : ℕ → List (Fin N) := fun n => List.ofFn fun m : Fin (n + 1) => j m with hv
    set k : ℕ → List (Fin N) := fun n => u n ++ (v n).reverse with hk
    have hkne : ∀ n, k n ≠ [] := fun n => by simp [hk, hu]
    -- the fixed points `pₙ` of `f_{kₙ}`
    have hfix : ∀ n, ∃ p, p ∈ I ∧ Φ.comp (k n) p = p := fun n => by
      obtain ⟨ε', hε', hf⟩ := Φ.exists_inClass_comp (hkne n)
      exact (existsUnique_fixedPoint hε' hf).exists
    choose p hp hfp using hfix
    have hpcl : ∀ n, (p n : ℂ) ∈ closure (nbhd ε) := fun n =>
      subset_closure (ofReal_mem_nbhd hε (hp n))
    -- the second step at `pₙ`
    have hid : ∀ n, ((deriv (deriv g) (p n) / deriv g (p n) : ℝ) : ℂ) =
        Φ.dualProj (.fin (k n).reverse) (p n) / (1 - deriv (Φ.comp (k n)) (p n)) := fun n => by
      obtain ⟨a, b, hab⟩ := Φ.exists_conj_comp hconj' (k n)
      exact (Φ.deriv_deriv_div_deriv_eq_of_fixedPoint hg.1 (hkne n) hab (hp n) (hfp n)
        (hg' _ (hp n))).2
    -- `pₙ = f_{i₁ ⋯ i_{n+1}}(f_{j_{n+1} ⋯ j₁}(pₙ)) → π(i)`
    have hplim : Tendsto p atTop (𝓝 (Φ.natProj i)) := by
      refine (Φ.tendsto_re_comp_natProj i (tendsto_add_atTop_nat 1)
        (z := fun n => (Φ.comp (v n).reverse (p n)).re)
        fun n => Φ.re_comp_mem_I _ (hp n)).congr fun n => ?_
      show (Φ.comp (u n) ((Φ.comp (v n).reverse (p n)).re : ℂ)).re = p n
      rw [← Φ.comp_ofReal _ (hp n), ← Function.comp_apply (f := Φ.comp (u n)), ← Φ.comp_append]
      show (Φ.comp (k n) (p n)).re = p n
      rw [hfp n, Complex.ofReal_re]
    -- the left-hand side tends to `g''(π(i))/g'(π(i))`
    have hL : Tendsto (fun n => ((deriv (deriv g) (p n) / deriv g (p n) : ℝ) : ℂ)) atTop
        (𝓝 ((deriv (deriv g) (Φ.natProj i) / deriv g (Φ.natProj i) : ℝ) : ℂ)) := by
      have hcont : ContinuousAt (fun x => deriv (deriv g) x / deriv g x) (Φ.natProj i) :=
        (hg.1 _ hπ).deriv.deriv.continuousAt.div (hg.1 _ hπ).deriv.continuousAt (hg' _ hπ)
      exact (Complex.continuous_ofReal.tendsto _).comp (hcont.tendsto.comp hplim)
    -- `f_{kₙ}'(pₙ) → 0`
    have hD : Tendsto (fun n => deriv (Φ.comp (k n)) (p n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => (Φ.norm_deriv_comp_le _ (hpcl n)).trans
        (pow_le_pow_of_le_one Φ.cmax_nonneg Φ.cmax_lt_one.le ?_)) hc
      simp only [hk, hu, hv, List.length_append, List.length_reverse, List.length_ofFn]
      omega
    -- `H_{j₁ ⋯ j_{n+1} i_{n+1} ⋯ i₁}(pₙ) - H_j(pₙ) → 0`, by Lemma 2.4 for words with a common
    -- prefix of length `n + 1`
    have hH₁ : Tendsto (fun n => Φ.dualProj (.fin (k n).reverse) (p n) -
        Φ.dualProj (.inf j) (p n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => hM _ _ (n + 1) ?_ _ (hpcl n))
        (by simpa using hc.const_mul (2 * M))
      rw [Word.le_commonPrefixLength_iff]
      intro l hl
      have hl' : l < (v n).length := by simp only [hv, List.length_ofFn]; exact hl
      have hget : (Word.fin (k n).reverse).get? l = some (j l) := by
        simp only [hk, Word.get?_fin, List.reverse_append, List.reverse_reverse]
        rw [List.getElem?_append_left hl']
        show (List.ofFn fun m : Fin (n + 1) => j m)[l]? = some (j l)
        simp only [List.getElem?_ofFn, hl, ↓reduceDIte]
      rw [hget, Word.get?_inf]
      exact ⟨rfl, rfl⟩
    -- `H_j(pₙ) → H_j(π(i))`, as `H_j` is continuous
    have hH₂ : Tendsto (fun n => Φ.dualProj (.inf j) (p n)) atTop
        (𝓝 (Φ.dualProj (.inf j) (Φ.natProj i))) :=
      (((Φ.differentiableOn_dualProj _).differentiableAt ((isOpen_nbhd ε).mem_nhds
        (ofReal_mem_nbhd hε hπ))).continuousAt.tendsto).comp
        ((Complex.continuous_ofReal.tendsto _).comp hplim)
    have hR : Tendsto (fun n => Φ.dualProj (.fin (k n).reverse) (p n) /
        (1 - deriv (Φ.comp (k n)) (p n))) atTop (𝓝 (Φ.dualProj (.inf j) (Φ.natProj i))) := by
      have h := (hH₁.add hH₂).div
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).sub hD)
        (by rw [sub_zero]; exact one_ne_zero)
      rw [zero_add, sub_zero, div_one] at h
      exact h.congr fun n => by simp only [Pi.div_apply, sub_add_cancel]
    exact tendsto_nhds_unique hL (hR.congr fun n => (hid n).symm)
  -- `H_{i₀} = H_{j₀}` on the infinite attractor, so on `[0,1]` by the identity theorem
  intro x hx
  by_contra hne
  have hfin := finite_zeros hε ((Φ.differentiableOn_dualProj (.inf i₀)).sub
    (Φ.differentiableOn_dualProj (.inf j₀))) ⟨x, hx, sub_ne_zero.2 hne⟩
  refine Φ.attractor_infinite hN hnd (hfin.subset ?_)
  rintro _ ⟨i, rfl⟩
  refine ⟨Φ.attractor_subset_I ⟨i, rfl⟩, ?_⟩
  show Φ.dualProj (.inf i₀) (Φ.natProj i) - Φ.dualProj (.inf j₀) (Φ.natProj i) = 0
  rw [← key i i₀, ← key i j₀, sub_self]

/-! ## The converse -/

/-- `Ĥ_{f_k} = H_{k^∞}` on `[0,1]`. -/
private theorem periodic_hatH_f_eq_dualProj_const (k : Fin N) :
    ∀ x ∈ I, hatH (Φ.f k) x = Φ.dualProj (.inf fun _ => k) x := by
  intro x hx
  have h := Φ.hatH_comp_eq_dualProj one_pos ![k] x hx
  have hw : periodic one_pos (![k] ∘ Fin.rev) = fun _ => k :=
    funext fun n => by unfold periodic; exact Matrix.cons_val_fin_one k ![] _
  have hc : Φ.comp (List.ofFn ![k]) = Φ.f k := by simp
  rwa [hw, hc] at h

/-- Theorem 1.12 (a), the converse, along the paper: if all dual natural projections agree on
`[0,1]`, then Lemma 5.1 for `f_{k₀}` gives an invertible `g` with `g'' = H g'`, and the second
part of Lemma 5.1 conjugates each `f_k` by `g` to a similarity. -/
theorem conjSelfSimilar_of_dualProj_eq
    (h : ∀ i j : ℕ → Fin N, ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x) :
    ConjSelfSimilar Φ.realMaps := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact ⟨id, ⟨analyticOnNhd_id, injOn_id _⟩, 0, 0, fun j => j.elim0⟩
  have hε := Φ.ε_pos
  have hmem : ∀ {x : ℝ}, x ∈ I → (x : ℂ) ∈ nbhd ε := fun hx => ofReal_mem_nbhd hε hx
  set k₀ : Fin N := ⟨0, hN⟩
  choose p hp hfp using fun k => (existsUnique_fixedPoint hε (Φ.inClass k)).exists
  -- `H = H_{k^∞} = Ĥ_{f_k}` for every letter `k`
  have hH : ∀ k, ∀ x ∈ I, hatH (Φ.f k) x = hatH (Φ.f k₀) x := fun k x hx => by
    rw [Φ.periodic_hatH_f_eq_dualProj_const k x hx, Φ.periodic_hatH_f_eq_dualProj_const k₀ x hx]
    exact h _ _ x hx
  -- Lemma 5.1 for `f_{k₀}`, with `g(p_{k₀}) = 0` and `g'(p_{k₀}) = 1`: `g'' = H g'`
  obtain ⟨G, ⟨G', hG'd, -, -, hGG'⟩, hinj, hode, -, -⟩ :=
    (lemma_5_1 hε (Φ.inClass k₀) (hp k₀) (hfp k₀)).1 0 1 one_ne_zero
  have hGd : DifferentiableOn ℂ G (nbhd ε) := hG'd.congr fun z hz => by
    have := congrFun (congrArg UniformFun.toFun hGG') ⟨z, hz⟩
    simp only [toNbhd, UniformFun.toFun_ofFun] at this
    exact this
  have hG₁d : DifferentiableOn ℂ (deriv G) (nbhd ε) := hGd.deriv (isOpen_nbhd ε)
  set φ : ℝ → ℝ := fun x => (G x).re with hφ
  set ψ : ℝ → ℝ := fun x => (deriv G x).re with hψ
  have hφd : ∀ x ∈ I, HasDerivAt φ (ψ x) x := fun x hx =>
    hasDerivAt_re_ofReal (hGd.differentiableAt ((isOpen_nbhd ε).mem_nhds (hmem hx)))
  have hψd : ∀ x ∈ I, HasDerivAt ψ (deriv (deriv G) x).re x := fun x hx =>
    hasDerivAt_re_ofReal (hG₁d.differentiableAt ((isOpen_nbhd ε).mem_nhds (hmem hx)))
  have hφw : ∀ x ∈ I, derivWithin φ I x = ψ x := fun x hx =>
    (hφd x hx).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one x hx)
  have hψdiff : DifferentiableOn ℝ ψ I := fun x hx =>
    (hψd x hx).differentiableAt.differentiableWithinAt
  have hφwd : DifferentiableOn ℝ (derivWithin φ I) I := hψdiff.congr hφw
  -- the equation `g'' = Ĥ_{f_k} g'` within `[0,1]`, for every letter `k`
  have hodek : ∀ k, ∀ x ∈ I,
      derivWithin (derivWithin φ I) I x = (hatH (Φ.f k) x).re * derivWithin φ I x := by
    intro k x hx
    rw [derivWithin_congr hφw (hφw x hx),
      (hψd x hx).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one x hx), hφw x hx,
      hode x hx, hH k x hx, Complex.mul_re, im_hatH_ofReal hε (Φ.inClass k₀) (hmem hx),
      zero_mul, sub_zero]
  -- the second part of Lemma 5.1 for each `f_k`
  refine ⟨φ, ⟨analyticOnNhd_re_ofReal hε hGd, hinj⟩, fun k => (deriv (Φ.f k) (p k)).re,
    fun k => φ (p k) * (1 - (deriv (Φ.f k) (p k)).re), fun k =>
      ⟨(periodic_re_deriv_ne_zero_abs_lt_one hε (Φ.inClass k) (hp k)).1,
        (periodic_re_deriv_ne_zero_abs_lt_one hε (Φ.inClass k) (hp k)).2, ?_⟩⟩
  exact (lemma_5_1 hε (Φ.inClass k) (hp k) (hfp k)).2 φ
    (fun x hx => (hφd x hx).differentiableAt.differentiableWithinAt) hφwd (hodek k)

/-- In the singleton case, commutativity and (5.2) give one common linearising map;
differentiating its conjugacy equations twice makes all dual projections equal. -/
theorem dualProj_eq_of_conjSelfSimilar_singleton (hN : 0 < N) {p : ℝ}
    (hpA : Φ.attractor = {p}) (hconj : ConjSelfSimilar Φ.realMaps) :
    ∀ i j : ℕ → Fin N, ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x := by
  obtain ⟨g, ⟨hg, hinj⟩, lam, t, hc⟩ := hconj
  have hp : p ∈ I := Φ.attractor_subset_I (hpA ▸ mem_singleton p)
  have hfix := Φ.fixedPoint_of_attractor_singleton hpA
  let k₀ : Fin N := ⟨0, hN⟩
  obtain ⟨hG, hGd, -, -⟩ := char_re_koenigs_spec Φ.ε_pos (Φ.inClass k₀) hp (hfix k₀)
  have hGconj : ∀ k, ∀ x ∈ I,
      (koenigs (Φ.f k₀) p (Φ.f k x)).re =
        (deriv (Φ.f k) p).re * (koenigs (Φ.f k₀) p x).re := by
    intro k x hx
    have hr := comp_comm_of_conj hinj
      (fun y hy => (Φ.inClass k₀).re_mem_I y hy)
      (fun y hy => (Φ.inClass k).re_mem_I y hy) (hc k₀).2.2 (hc k).2.2 hp
      (by simpa [realMaps] using congrArg Complex.re (hfix k₀))
      (by simpa [realMaps] using congrArg Complex.re (hfix k))
    have hcomm : ∀ z ∈ nbhd ε, Φ.f k₀ (Φ.f k z) = Φ.f k (Φ.f k₀ z) := by
      apply eqOn_nbhd_of_eqOn_Icc Φ.ε_pos
        (((Φ.differentiableOn_f k₀).mono IFS.nbhd_subset_two).comp
          ((Φ.differentiableOn_f k).mono IFS.nbhd_subset_two) (Φ.mapsTo_f k))
        (((Φ.differentiableOn_f k).mono IFS.nbhd_subset_two).comp
          ((Φ.differentiableOn_f k₀).mono IFS.nbhd_subset_two) (Φ.mapsTo_f k₀))
        zero_lt_one subset_rfl
      intro y hy
      have hreal : ∀ l, ∀ z ∈ I, ((Φ.f l z).re : ℂ) = Φ.f l z := fun l z hz =>
        Complex.ext rfl (by simp [(Φ.inClass l).im_eq_zero z
          (ofReal_mem_nbhd (by linarith [Φ.ε_pos]) hz)])
      have he := congrArg (fun r : ℝ => (r : ℂ)) (hr y hy)
      rw [hreal k₀ _ ((Φ.inClass k).re_mem_I y hy),
        hreal k _ ((Φ.inClass k₀).re_mem_I y hy), hreal k y hy, hreal k₀ y hy] at he
      exact he
    have he := koenigs_commuting Φ.ε_pos (Φ.inClass k₀) (ofReal_mem_nbhd Φ.ε_pos hp)
      (hfix k₀) (Φ.inClass k) (hfix k) hcomm (ofReal_mem_nbhd Φ.ε_pos hx)
    rw [he, Complex.mul_re, im_koenigs_ofReal Φ.ε_pos (Φ.inClass k₀) hp (hfix k₀)
      (ofReal_mem_nbhd Φ.ε_pos hx), mul_zero, sub_zero]
  apply Φ.dualProj_eq_of_forall_const
  intro k l x hx
  rw [← Φ.periodic_hatH_f_eq_dualProj_const k x hx,
    ← Φ.periodic_hatH_f_eq_dualProj_const l x hx]
  apply char_hatH_eq_of_conj Φ.ε_pos (Φ.inClass k) Φ.ε_pos (Φ.inClass l)
    hG.1 (fun y hy => (hGd y hy).ne') (a₁ := (deriv (Φ.f k) p).re) (b₁ := 0)
    (a₂ := (deriv (Φ.f l) p).re) (b₂ := 0) ?_ ?_ x hx
  all_goals
    intro y hy
    have hr : ∀ j, ((Φ.f j y).re : ℂ) = Φ.f j y := fun j =>
      Complex.ext rfl (by simp [(Φ.inClass j).im_eq_zero y
        (ofReal_mem_nbhd (by linarith [Φ.ε_pos]) hy)])
    simpa only [hr, add_zero] using hGconj _ y hy

/-- Theorem 1.12 (a), extended to singleton attractors by the argument of Theorem 2.3. -/
theorem conjSelfSimilar_iff :
    ConjSelfSimilar Φ.realMaps ↔
      ∀ i j : ℕ → Fin N, ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x := by
  constructor
  · intro h
    by_cases hnd : ¬ ∃ p, Φ.attractor = {p}
    · exact Φ.dualProj_eq_of_conjSelfSimilar hnd h
    · obtain ⟨p, hp⟩ := not_not.1 hnd
      intro i j
      exact Φ.dualProj_eq_of_conjSelfSimilar_singleton (i 0).pos hp h i j
  · exact Φ.conjSelfSimilar_of_dualProj_eq

/-- Theorem 1.12 (b), for every system. -/
theorem subConjSelfSimilar_iff :
    Φ.SubConjSelfSimilar ↔
      ∃ (m : ℕ) (hm : 0 < m) (i j : Fin m → Fin N), i ≠ j ∧
        ∀ x ∈ I, Φ.dualProj (.inf (periodic hm i)) x = Φ.dualProj (.inf (periodic hm j)) x := by
  have hε := Φ.ε_pos
  have hne : ∀ {m : ℕ} (w : Fin m → Fin N), 0 < m → List.ofFn w ≠ [] := fun w hm h =>
    hm.ne' (List.ofFn_eq_nil_iff.1 h)
  have hrev : ∀ {m : ℕ} (w : Fin m → Fin N), (w ∘ Fin.rev) ∘ Fin.rev = w := fun w =>
    funext fun k => by simp
  have hrev_ne : ∀ {m : ℕ} {u v : Fin m → Fin N}, u ≠ v → u ∘ Fin.rev ≠ v ∘ Fin.rev :=
    fun {m u v} huv h => huv (by rw [← hrev u, h, hrev])
  constructor
  · rintro ⟨m, i, j, hij, g, ⟨hg, hinj⟩, lam, t, hconj⟩
    have hm : 0 < m := Nat.pos_of_ne_zero fun h => hij (by subst h; exact Subsingleton.elim _ _)
    obtain ⟨ε₁, hε₁, hf₁⟩ := Φ.exists_inClass_comp (hne i hm)
    obtain ⟨ε₂, hε₂, hf₂⟩ := Φ.exists_inClass_comp (hne j hm)
    obtain ⟨p₁, ⟨hp₁, hfp₁⟩, -⟩ := existsUnique_fixedPoint hε₁ hf₁
    obtain ⟨p₂, ⟨hp₂, hfp₂⟩, -⟩ := existsUnique_fixedPoint hε₂ hf₂
    have hci : ∀ x ∈ I, g (Φ.comp (List.ofFn i) x).re = lam 0 * g x + t 0 := (hconj 0).2.2
    have hcj : ∀ x ∈ I, g (Φ.comp (List.ofFn j) x).re = lam 1 * g x + t 1 := (hconj 1).2.2
    have hmi : MapsTo (fun x : ℝ => (Φ.comp (List.ofFn i) x).re) I I := fun x hx =>
      hf₁.re_mem_I x hx
    have hmj : MapsTo (fun x : ℝ => (Φ.comp (List.ofFn j) x).re) I I := fun x hx =>
      hf₂.re_mem_I x hx
    have hFi : (Φ.comp (List.ofFn i) p₁).re = p₁ := by rw [hfp₁, Complex.ofReal_re]
    have hFj : (Φ.comp (List.ofFn j) p₂).re = p₂ := by rw [hfp₂, Complex.ofReal_re]
    by_cases hpq : p₁ = p₂
    · -- a common fixed point: `f_i` and `f_j` commute on `[0,1]`, so `f_{ij} = f_{ji}` there
      subst hpq
      have hcomm := comp_comm_of_conj hinj hmi hmj hci hcj hp₁ hFi hFj
      have hm' : 0 < m + m := by omega
      have hcomp : ∀ {u v : Fin m → Fin N}, ∀ y ∈ I, Φ.comp (List.ofFn (Fin.append u v)) y =
          ((Φ.comp (List.ofFn u) ((Φ.comp (List.ofFn v) y).re : ℂ)).re : ℂ) := fun y hy => by
        rw [List.ofFn_fin_append, Φ.comp_append, Function.comp_apply]
        conv_lhs => rw [Φ.comp_ofReal _ hy]
        exact Φ.comp_ofReal _ (Φ.re_comp_mem_I _ hy)
      obtain ⟨ε₃, hε₃, hf₃⟩ := Φ.exists_inClass_comp (hne (Fin.append i j) hm')
      obtain ⟨ε₄, hε₄, hf₄⟩ := Φ.exists_inClass_comp (hne (Fin.append j i) hm')
      have hH := hatH_eq_of_eqOn_I hε₃ hf₃ hε₄ hf₄ fun y hy => by
        rw [hcomp y hy, hcomp y hy]
        exact congrArg _ (hcomm y hy)
      refine ⟨m + m, hm', Fin.append i j ∘ Fin.rev, Fin.append j i ∘ Fin.rev,
        hrev_ne fun h => hij (funext fun k => ?_), fun x hx => ?_⟩
      · simpa using congrFun h (Fin.castAdd m k)
      · rw [← Φ.hatH_comp_eq_dualProj hm' _ x hx, ← Φ.hatH_comp_eq_dualProj hm' _ x hx]
        exact hH x hx
    · -- Apply part (a) to the two-map subsystem, whose fixed points differ.
      let Ψ : IFS 2 (ε / 4) := ⟨![Φ.comp (List.ofFn i), Φ.comp (List.ofFn j)],
        by linarith [Φ.ε_pos], Fin.forall_fin_two.2
          ⟨Φ.inClass_comp (hne i hm), Φ.inClass_comp (hne j hm)⟩⟩
      have hnd : ¬ ∃ x, Ψ.attractor = {x} := by
        rintro ⟨x, hx⟩
        have hxI : x ∈ I := Ψ.attractor_subset_I (hx ▸ mem_singleton x)
        have hfix := Ψ.fixedPoint_of_attractor_singleton hx
        have hi : Φ.comp (List.ofFn i) x = x := by simpa [Ψ] using hfix 0
        have hj : Φ.comp (List.ofFn j) x = x := by simpa [Ψ] using hfix 1
        exact hpq (((existsUnique_fixedPoint hε₁ hf₁).unique ⟨hp₁, hfp₁⟩ ⟨hxI, hi⟩).trans
          ((existsUnique_fixedPoint hε₂ hf₂).unique ⟨hxI, hj⟩ ⟨hp₂, hfp₂⟩))
      have hall := Ψ.dualProj_eq_of_conjSelfSimilar hnd ⟨g, ⟨hg, hinj⟩, lam, t,
        Fin.forall_fin_two.2 ⟨by simpa [Ψ, realMaps] using hconj 0,
          by simpa [Ψ, realMaps] using hconj 1⟩⟩
      have hH : ∀ x ∈ I, hatH (Φ.comp (List.ofFn i)) x =
          hatH (Φ.comp (List.ofFn j)) x := by
        intro x hx
        have h := hall (fun _ => 0) (fun _ => 1) x hx
        rw [← Ψ.periodic_hatH_f_eq_dualProj_const 0 x hx,
          ← Ψ.periodic_hatH_f_eq_dualProj_const 1 x hx] at h
        simpa [Ψ] using h
      refine ⟨m, hm, i ∘ Fin.rev, j ∘ Fin.rev, hrev_ne hij, fun x hx => ?_⟩
      rw [← Φ.hatH_comp_eq_dualProj hm _ x hx, ← Φ.hatH_comp_eq_dualProj hm _ x hx]
      exact hH x hx
  · rintro ⟨m, hm, i, j, hij, h⟩
    have hH : ∀ x ∈ I, hatH (Φ.comp (List.ofFn (i ∘ Fin.rev))) x =
        hatH (Φ.comp (List.ofFn (j ∘ Fin.rev))) x := fun x hx => by
      rw [Φ.hatH_comp_eq_dualProj hm _ x hx, Φ.hatH_comp_eq_dualProj hm _ x hx, hrev, hrev]
      exact h x hx
    obtain ⟨ε₁, hε₁, hf₁⟩ := Φ.exists_inClass_comp (hne (i ∘ Fin.rev) hm)
    obtain ⟨ε₂, hε₂, hf₂⟩ := Φ.exists_inClass_comp (hne (j ∘ Fin.rev) hm)
    obtain ⟨p₁, ⟨hp₁, hfp₁⟩, -⟩ := existsUnique_fixedPoint hε₁ hf₁
    obtain ⟨p₂, ⟨hp₂, hfp₂⟩, -⟩ := existsUnique_fixedPoint hε₂ hf₂
    obtain ⟨hco, -, -, hode⟩ := char_re_koenigs_spec hε₁ hf₁ hp₁ hfp₁
    obtain ⟨l₁, t₁, c₁⟩ := char_exists_conj_of_ode hε₁ hf₁ hp₁ hfp₁ hco.1 hode
    obtain ⟨l₂, t₂, c₂⟩ := char_exists_conj_of_ode hε₂ hf₂ hp₂ hfp₂ hco.1 fun x hx => by
      rw [← hH x hx]; exact hode x hx
    exact ⟨m, i ∘ Fin.rev, j ∘ Fin.rev, hrev_ne hij, _, hco, ![l₁, l₂], ![t₁, t₂],
      Fin.forall_fin_two.2 ⟨c₁, c₂⟩⟩

/-! ## Theorem 1.12 -/

/-- Theorem 1.12 (a) and (b), for systems whose attractor is not a singleton. -/
theorem theorem_1_12 (hnd : ¬ ∃ x, Φ.attractor = {x}) :
    (ConjSelfSimilar Φ.realMaps ↔
      ∀ i j : ℕ → Fin N, ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x) ∧
    (Φ.SubConjSelfSimilar ↔
      ∃ (m : ℕ) (hm : 0 < m) (i j : Fin m → Fin N), i ≠ j ∧
        ∀ x ∈ I, Φ.dualProj (.inf (periodic hm i)) x = Φ.dualProj (.inf (periodic hm j)) x) :=
  ⟨⟨Φ.dualProj_eq_of_conjSelfSimilar hnd, Φ.conjSelfSimilar_of_dualProj_eq⟩,
    Φ.subConjSelfSimilar_iff⟩

end IFS

end AnalyticESC
