module

public import AnalyticESC.Dual.Attractor

@[expose] public section

/-!
# Lemma 2.7

The dual natural projection depends Lipschitz-continuously on the system in the `𝒞²` metric,
uniformly in the word (2.6), so the strong separation of the dual is an open condition.

We write `f_i = Φ.f i`, `g_i = Ψ.f i` and `d = d₂(Φ, Ψ)`, with `Φ ∈ 𝔖_N(ε)` and `Ψ ∈ 𝔖_N(ε')`
for arbitrary `ε, ε' > 0`; all constants depend on `Φ` only. The estimates (2.3)–(2.5) are proved
at the real points of `I`, where all compositions take values in `I`. Since `d₂(Φ, Ψ)` small does
not give `|g_i'| ≤ c_max`, the contraction ratio of `Ψ` on `I` is bounded by `c' = c_max + δ₀ < 1`
and `|g_i'|` from below by `c_min / 2`. Auxiliary results are in the namespace `IFS.Continuity`.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace IFS.Continuity

/-! ## The real points of `I` in `ℂ` -/

theorem isCompact_realI : IsCompact (((↑) : ℝ → ℂ) '' I) :=
  isCompact_Icc.image Complex.continuous_ofReal

theorem convex_realI : Convex ℝ (((↑) : ℝ → ℂ) '' I) := by
  have := (convex_Icc (0 : ℝ) 1).linear_image Complex.ofRealCLM.toLinearMap
  simpa using this

theorem image_I_subset_nbhd {δ : ℝ} (hδ : 0 < δ) : ((↑) : ℝ → ℂ) '' I ⊆ nbhd δ := by
  rintro _ ⟨y, hy, rfl⟩
  exact ofReal_mem_nbhd hδ hy

theorem image_I_subset_closure {δ : ℝ} (hδ : 0 < δ) :
    ((↑) : ℝ → ℂ) '' I ⊆ closure (nbhd δ) :=
  (image_I_subset_nbhd hδ).trans subset_closure

theorem ofReal_mem_closure {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : x ∈ I) :
    (x : ℂ) ∈ closure (nbhd δ) :=
  image_I_subset_closure hδ (mem_image_of_mem _ hx)

/-- A map holomorphic on an open set containing `I` is Lipschitz on `I`. -/
theorem exists_lipschitz_I {h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hIU : ((↑) : ℝ → ℂ) '' I ⊆ U) (hh : DifferentiableOn ℂ h U) :
    ∃ L, 0 ≤ L ∧ ∀ a ∈ I, ∀ b ∈ I, ‖h (a : ℂ) - h (b : ℂ)‖ ≤ L * ‖(a : ℂ) - b‖ := by
  obtain ⟨L, hL⟩ := isCompact_realI.exists_bound_of_continuousOn
    ((hh.deriv hU).continuousOn.mono hIU)
  refine ⟨max L 0, le_max_right _ _, fun a ha b hb => ?_⟩
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => hh.differentiableAt (hU.mem_nhds (hIU hz)))
    (fun z hz => (hL z hz).trans (le_max_left _ _)) convex_realI
    (mem_image_of_mem _ hb) (mem_image_of_mem _ ha)

/-- A finite family of maps holomorphic on open sets containing `I` is uniformly Lipschitz
on `I`. -/
theorem exists_lipschitz_I_fin {N : ℕ} {h : Fin N → ℂ → ℂ} (U : Fin N → Set ℂ)
    (hU : ∀ i, IsOpen (U i)) (hIU : ∀ i, ((↑) : ℝ → ℂ) '' I ⊆ U i)
    (hh : ∀ i, DifferentiableOn ℂ (h i) (U i)) :
    ∃ L, 0 ≤ L ∧ ∀ i, ∀ a ∈ I, ∀ b ∈ I, ‖h i (a : ℂ) - h i (b : ℂ)‖ ≤ L * ‖(a : ℂ) - b‖ := by
  choose L hL0 hL using fun i => exists_lipschitz_I (hU i) (hIU i) (hh i)
  refine ⟨∑ i, L i, Finset.sum_nonneg fun i _ => hL0 i, fun i a ha b hb => ?_⟩
  exact (hL i a ha b hb).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => hL0 j) (Finset.mem_univ i)) (norm_nonneg _))

theorem bddAbove_range_norm_sub {F G : ℂ → ℂ} {U : Set ℂ} (hIU : ((↑) : ℝ → ℂ) '' I ⊆ U)
    (hF : ContinuousOn F U) (hG : ContinuousOn G U) :
    BddAbove (range fun x : I => ‖F ((x : ℝ) : ℂ) - G ((x : ℝ) : ℂ)‖) := by
  have hU : ∀ x : I, ((x : ℝ) : ℂ) ∈ U := fun x => hIU (mem_image_of_mem _ x.2)
  have h1 : Continuous fun x : I => ((x : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp continuous_subtype_val
  exact (isCompact_range ((hF.comp_continuous h1 hU).sub (hG.comp_continuous h1 hU)).norm).bddAbove

variable {N : ℕ} {ε ε' : ℝ}

/-! ## Pointwise bounds from `d₂` -/

theorem d2Map_le_d2 (Φ : IFS N ε) (Ψ : IFS N ε') (i : Fin N) :
    d2Map (Φ.f i) (Ψ.f i) ≤ d2 Φ Ψ :=
  le_ciSup (f := fun i => d2Map (Φ.f i) (Ψ.f i)) (Set.finite_range _).bddAbove i

theorem d2_nonneg (Φ : IFS N ε) (Ψ : IFS N ε') : 0 ≤ d2 Φ Ψ :=
  Real.iSup_nonneg fun _ => add_nonneg (add_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _)
    (Real.iSup_nonneg fun _ => norm_nonneg _)) (Real.iSup_nonneg fun _ => norm_nonneg _)

/-- At a point of `I`, the maps, their derivatives and their second derivatives differ by at
most `d₂(Φ, Ψ)`. -/
theorem norm_sub_le_d2 (Φ : IFS N ε) (Ψ : IFS N ε') (i : Fin N) {x : ℝ} (hx : x ∈ I) :
    ‖Φ.f i x - Ψ.f i x‖ ≤ d2 Φ Ψ ∧ ‖deriv (Φ.f i) x - deriv (Ψ.f i) x‖ ≤ d2 Φ Ψ ∧
      ‖deriv (deriv (Φ.f i)) x - deriv (deriv (Ψ.f i)) x‖ ≤ d2 Φ Ψ := by
  -- Both systems are holomorphic on `U = B_{2ε} ∩ B_{2ε'}`, which contains `I`.
  have hU : ((↑) : ℝ → ℂ) '' I ⊆ nbhd (2 * ε) ∩ nbhd (2 * ε') :=
    subset_inter (image_I_subset_nbhd (by linarith [Φ.ε_pos]))
      (image_I_subset_nbhd (by linarith [Ψ.ε_pos]))
  have hO := isOpen_nbhd (2 * ε)
  have hO' := isOpen_nbhd (2 * ε')
  have hf := (Φ.inClass i).differentiableOn
  have hg := (Ψ.inClass i).differentiableOn
  have hl := inter_subset_left (s := nbhd (2 * ε)) (t := nbhd (2 * ε'))
  have hr := inter_subset_right (s := nbhd (2 * ε)) (t := nbhd (2 * ε'))
  have e0 : ‖Φ.f i x - Ψ.f i x‖ ≤ ⨆ y : I, ‖Φ.f i ((y : ℝ) : ℂ) - Ψ.f i ((y : ℝ) : ℂ)‖ :=
    le_ciSup (f := fun y : I => ‖Φ.f i ((y : ℝ) : ℂ) - Ψ.f i ((y : ℝ) : ℂ)‖)
      (bddAbove_range_norm_sub hU (hf.continuousOn.mono hl) (hg.continuousOn.mono hr)) ⟨x, hx⟩
  have e1 : ‖deriv (Φ.f i) x - deriv (Ψ.f i) x‖ ≤
      ⨆ y : I, ‖deriv (Φ.f i) ((y : ℝ) : ℂ) - deriv (Ψ.f i) ((y : ℝ) : ℂ)‖ :=
    le_ciSup (f := fun y : I => ‖deriv (Φ.f i) ((y : ℝ) : ℂ) - deriv (Ψ.f i) ((y : ℝ) : ℂ)‖)
      (bddAbove_range_norm_sub hU ((hf.deriv hO).continuousOn.mono hl)
        ((hg.deriv hO').continuousOn.mono hr)) ⟨x, hx⟩
  have e2 : ‖deriv (deriv (Φ.f i)) x - deriv (deriv (Ψ.f i)) x‖ ≤
      ⨆ y : I, ‖deriv (deriv (Φ.f i)) ((y : ℝ) : ℂ) - deriv (deriv (Ψ.f i)) ((y : ℝ) : ℂ)‖ :=
    le_ciSup (f := fun y : I =>
        ‖deriv (deriv (Φ.f i)) ((y : ℝ) : ℂ) - deriv (deriv (Ψ.f i)) ((y : ℝ) : ℂ)‖)
      (bddAbove_range_norm_sub hU (((hf.deriv hO).deriv hO).continuousOn.mono hl)
        (((hg.deriv hO').deriv hO').continuousOn.mono hr)) ⟨x, hx⟩
  have n0 := (norm_nonneg _).trans e0
  have n1 := (norm_nonneg _).trans e1
  have n2 := (norm_nonneg _).trans e2
  have hd := d2Map_le_d2 Φ Ψ i
  unfold d2Map at hd
  exact ⟨by linarith, by linarith, by linarith⟩

/-! ## The estimates (2.3)–(2.5) -/

/-- (2.4): `|f_v(x) - g_v(x)| ≤ d / (1 - c_max)` on `I`. -/
theorem norm_comp_sub_comp_le (Φ : IFS N ε) (Ψ : IFS N ε') (v : List (Fin N)) {x : ℝ}
    (hx : x ∈ I) :
    ‖Φ.comp v x - Ψ.comp v x‖ ≤ d2 Φ Ψ / (1 - Φ.cmax) := by
  have hc := Φ.cmax_lt_one
  have hc0 := Φ.cmax_nonneg
  have hd := d2_nonneg Φ Ψ
  have hc1 : 0 < 1 - Φ.cmax := by linarith
  induction v with
  | nil => simp only [comp_nil, id, sub_self, norm_zero]; positivity
  | cons i u ih =>
    obtain ⟨a, ha, hae⟩ : ∃ a ∈ I, Φ.comp u x = (a : ℂ) :=
      ⟨_, Φ.re_comp_mem_I u hx, Φ.comp_ofReal u hx⟩
    obtain ⟨b, hb, hbe⟩ : ∃ b ∈ I, Ψ.comp u x = (b : ℂ) :=
      ⟨_, Ψ.re_comp_mem_I u hx, Ψ.comp_ofReal u hx⟩
    rw [hae, hbe] at ih
    simp only [comp_cons, Function.comp_apply, hae, hbe]
    have h1 : ‖Φ.f i a - Φ.f i b‖ ≤ Φ.cmax * ‖(a : ℂ) - b‖ := by
      have := Φ.norm_comp_sub_le [i] (ofReal_mem_nbhd Φ.ε_pos ha) (ofReal_mem_nbhd Φ.ε_pos hb)
      simpa [comp_cons, comp_nil] using this
    have h2 := (norm_sub_le_d2 Φ Ψ i hb).1
    calc ‖Φ.f i a - Ψ.f i b‖ ≤ ‖Φ.f i a - Φ.f i b‖ + ‖Φ.f i b - Ψ.f i b‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ Φ.cmax * (d2 Φ Ψ / (1 - Φ.cmax)) + d2 Φ Ψ :=
          add_le_add (h1.trans (mul_le_mul_of_nonneg_left ih hc0)) h2
      _ = d2 Φ Ψ / (1 - Φ.cmax) := by field_simp; ring

/-- `|g_v'(x)| ≤ c'^{|v|}` on `I` if `|g_i'| ≤ c'` on `I` for all `i`. -/
theorem norm_deriv_comp_le_pow (Ψ : IFS N ε) {c' : ℝ} (hc'0 : 0 ≤ c')
    (hc' : ∀ i, ∀ y ∈ I, ‖deriv (Ψ.f i) (y : ℂ)‖ ≤ c') (v : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    ‖deriv (Ψ.comp v) x‖ ≤ c' ^ v.length := by
  induction v with
  | nil => simp [comp_nil]
  | cons i u ih =>
    obtain ⟨b, hb, hbe⟩ : ∃ b ∈ I, Ψ.comp u x = (b : ℂ) :=
      ⟨_, Ψ.re_comp_mem_I u hx, Ψ.comp_ofReal u hx⟩
    rw [Ψ.deriv_comp_cons i u (ofReal_mem_closure Ψ.ε_pos hx), hbe, norm_mul, List.length_cons,
      pow_succ']
    exact mul_le_mul (hc' i b hb) ih (norm_nonneg _) hc'0

/-- (2.5): `|f_v'(x) - g_v'(x)| ≤ |v| c'^{|v|} K d` on `I`, with
`K = (L / (1 - c_max) + 1) / c'` and `L` a Lipschitz constant of the `f_i'` on `I`. -/
theorem norm_deriv_comp_sub_le (Φ : IFS N ε) (Ψ : IFS N ε') {c' L : ℝ} (hc'0 : 0 < c')
    (hcc' : Φ.cmax ≤ c') (hc' : ∀ i, ∀ y ∈ I, ‖deriv (Ψ.f i) (y : ℂ)‖ ≤ c') (hL0 : 0 ≤ L)
    (hL : ∀ i, ∀ a ∈ I, ∀ b ∈ I,
      ‖deriv (Φ.f i) (a : ℂ) - deriv (Φ.f i) (b : ℂ)‖ ≤ L * ‖(a : ℂ) - b‖)
    (v : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    ‖deriv (Φ.comp v) x - deriv (Ψ.comp v) x‖ ≤
      v.length * c' ^ v.length * ((L / (1 - Φ.cmax) + 1) / c') * d2 Φ Ψ := by
  have hc := Φ.cmax_lt_one
  have hd := d2_nonneg Φ Ψ
  have hc1 : 0 < 1 - Φ.cmax := by linarith
  have hK0 : 0 ≤ (L / (1 - Φ.cmax) + 1) / c' := by positivity
  have hxc := ofReal_mem_closure Φ.ε_pos hx
  have hxc' := ofReal_mem_closure Ψ.ε_pos hx
  induction v with
  | nil => simp [comp_nil]
  | cons i u ih =>
    obtain ⟨a, ha, hae⟩ : ∃ a ∈ I, Φ.comp u x = (a : ℂ) :=
      ⟨_, Φ.re_comp_mem_I u hx, Φ.comp_ofReal u hx⟩
    obtain ⟨b, hb, hbe⟩ : ∃ b ∈ I, Ψ.comp u x = (b : ℂ) :=
      ⟨_, Ψ.re_comp_mem_I u hx, Ψ.comp_ofReal u hx⟩
    have hab : ‖(a : ℂ) - b‖ ≤ d2 Φ Ψ / (1 - Φ.cmax) := by
      rw [← hae, ← hbe]; exact norm_comp_sub_comp_le Φ Ψ u hx
    rw [Φ.deriv_comp_cons i u hxc, Ψ.deriv_comp_cons i u hxc', hae, hbe]
    set K := (L / (1 - Φ.cmax) + 1) / c' with hK
    set Df := deriv (Φ.comp u) x
    set Dg := deriv (Ψ.comp u) x
    have hA : ‖deriv (Φ.f i) a‖ ≤ c' :=
      (Φ.norm_deriv_le_cmax i (ofReal_mem_closure Φ.ε_pos ha)).trans hcc'
    have hB : ‖deriv (Φ.f i) a - deriv (Ψ.f i) b‖ ≤ K * c' * d2 Φ Ψ := by
      calc _ ≤ ‖deriv (Φ.f i) a - deriv (Φ.f i) b‖ + ‖deriv (Φ.f i) b - deriv (Ψ.f i) b‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ L * (d2 Φ Ψ / (1 - Φ.cmax)) + d2 Φ Ψ :=
            add_le_add ((hL i a ha b hb).trans (mul_le_mul_of_nonneg_left hab hL0))
              (norm_sub_le_d2 Φ Ψ i hb).2.1
        _ = K * c' * d2 Φ Ψ := by rw [hK]; field_simp
    have hDg : ‖Dg‖ ≤ c' ^ u.length := norm_deriv_comp_le_pow Ψ hc'0.le hc' u hx
    calc ‖deriv (Φ.f i) a * Df - deriv (Ψ.f i) b * Dg‖
        = ‖deriv (Φ.f i) a * (Df - Dg) + (deriv (Φ.f i) a - deriv (Ψ.f i) b) * Dg‖ := by
          congr 1; ring
      _ ≤ ‖deriv (Φ.f i) a‖ * ‖Df - Dg‖ + ‖deriv (Φ.f i) a - deriv (Ψ.f i) b‖ * ‖Dg‖ := by
          rw [← norm_mul, ← norm_mul]; exact norm_add_le _ _
      _ ≤ c' * (u.length * c' ^ u.length * K * d2 Φ Ψ) + (K * c' * d2 Φ Ψ) * c' ^ u.length :=
          add_le_add (mul_le_mul hA ih (norm_nonneg _) hc'0.le)
            (mul_le_mul hB hDg (norm_nonneg _) (by positivity))
      _ = (i :: u).length * c' ^ (i :: u).length * K * d2 Φ Ψ := by
          simp only [List.length_cons]; push_cast; ring

/-- (2.3): `|f_i''/f_i' - g_i''/g_i'| ≤ (1 + M) / m · d` on `I`, if `|g_i'| ≥ m > 0` on `I` and
`M` bounds `f_i''/f_i'` on `I`. -/
theorem norm_nonlin_sub_le (Φ : IFS N ε) (Ψ : IFS N ε') {m M : ℝ} (hm : 0 < m) (hM0 : 0 ≤ M)
    (hgm : ∀ i, ∀ y ∈ I, m ≤ ‖deriv (Ψ.f i) (y : ℂ)‖)
    (hM : ∀ i, ∀ y ∈ I, ‖Φ.nonlin i (y : ℂ)‖ ≤ M) (i : Fin N) {y : ℝ} (hy : y ∈ I) :
    ‖Φ.nonlin i y - Ψ.nonlin i y‖ ≤ (1 + M) / m * d2 Φ Ψ := by
  have hf : deriv (Φ.f i) y ≠ 0 :=
    (Φ.inClass i).deriv_ne_zero _ (ofReal_mem_closure Φ.ε_pos hy)
  have hg : deriv (Ψ.f i) y ≠ 0 :=
    (Ψ.inClass i).deriv_ne_zero _ (ofReal_mem_closure Ψ.ε_pos hy)
  have key : Φ.nonlin i y - Ψ.nonlin i y =
      ((deriv (deriv (Φ.f i)) y - deriv (deriv (Ψ.f i)) y) +
        Φ.nonlin i y * (deriv (Ψ.f i) y - deriv (Φ.f i) y)) / deriv (Ψ.f i) y := by
    simp only [nonlin]; field_simp; ring
  obtain ⟨-, h1, h2⟩ := norm_sub_le_d2 Φ Ψ i hy
  have hnum : ‖(deriv (deriv (Φ.f i)) y - deriv (deriv (Ψ.f i)) y) +
      Φ.nonlin i y * (deriv (Ψ.f i) y - deriv (Φ.f i) y)‖ ≤ (1 + M) * d2 Φ Ψ := by
    calc _ ≤ ‖deriv (deriv (Φ.f i)) y - deriv (deriv (Ψ.f i)) y‖ +
          ‖Φ.nonlin i y‖ * ‖deriv (Ψ.f i) y - deriv (Φ.f i) y‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ d2 Φ Ψ + M * d2 Φ Ψ :=
          add_le_add h2 (mul_le_mul (hM i y hy) (by rw [norm_sub_rev]; exact h1)
            (norm_nonneg _) hM0)
      _ = (1 + M) * d2 Φ Ψ := by ring
  rw [key, norm_div]
  calc _ ≤ (1 + M) * d2 Φ Ψ / m :=
        div_le_div₀ (by have := d2_nonneg Φ Ψ; positivity) hnum hm (hgm i y hy)
    _ = (1 + M) / m * d2 Φ Ψ := by ring

/-- The difference of the terms of the series (1.4) for `Φ` and `Ψ`: with `v` of length `n`,
`|(f_i''/f_i')(f_v(x)) f_v'(x) - (g_i''/g_i')(g_v(x)) g_v'(x)| ≤ (M K n + B) c'^n d`. -/
theorem norm_term_sub_le (Φ : IFS N ε) (Ψ : IFS N ε') {c' L₁ L₂ m M : ℝ} (hc'0 : 0 < c')
    (hcc' : Φ.cmax ≤ c') (hc' : ∀ i, ∀ y ∈ I, ‖deriv (Ψ.f i) (y : ℂ)‖ ≤ c')
    (hm : 0 < m) (hgm : ∀ i, ∀ y ∈ I, m ≤ ‖deriv (Ψ.f i) (y : ℂ)‖)
    (hM0 : 0 ≤ M) (hM : ∀ i, ∀ y ∈ I, ‖Φ.nonlin i (y : ℂ)‖ ≤ M)
    (hL₁0 : 0 ≤ L₁) (hL₁ : ∀ i, ∀ a ∈ I, ∀ b ∈ I,
      ‖deriv (Φ.f i) (a : ℂ) - deriv (Φ.f i) (b : ℂ)‖ ≤ L₁ * ‖(a : ℂ) - b‖)
    (hL₂0 : 0 ≤ L₂) (hL₂ : ∀ i, ∀ a ∈ I, ∀ b ∈ I,
      ‖Φ.nonlin i (a : ℂ) - Φ.nonlin i (b : ℂ)‖ ≤ L₂ * ‖(a : ℂ) - b‖)
    (i : Fin N) (v : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    ‖Φ.nonlin i (Φ.comp v x) * deriv (Φ.comp v) x -
        Ψ.nonlin i (Ψ.comp v x) * deriv (Ψ.comp v) x‖ ≤
      (M * ((L₁ / (1 - Φ.cmax) + 1) / c') * v.length + (L₂ / (1 - Φ.cmax) + (1 + M) / m)) *
        c' ^ v.length * d2 Φ Ψ := by
  have hc := Φ.cmax_lt_one
  have hd := d2_nonneg Φ Ψ
  have hc1 : 0 < 1 - Φ.cmax := by linarith
  set K := (L₁ / (1 - Φ.cmax) + 1) / c'
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨a, ha, hae⟩ : ∃ a ∈ I, Φ.comp v x = (a : ℂ) :=
    ⟨_, Φ.re_comp_mem_I v hx, Φ.comp_ofReal v hx⟩
  obtain ⟨b, hb, hbe⟩ : ∃ b ∈ I, Ψ.comp v x = (b : ℂ) :=
    ⟨_, Ψ.re_comp_mem_I v hx, Ψ.comp_ofReal v hx⟩
  have hab : ‖(a : ℂ) - b‖ ≤ d2 Φ Ψ / (1 - Φ.cmax) := by
    rw [← hae, ← hbe]; exact norm_comp_sub_comp_le Φ Ψ v hx
  rw [hae, hbe]
  set Df := deriv (Φ.comp v) x
  set Dg := deriv (Ψ.comp v) x
  have hDfg : ‖Df - Dg‖ ≤ v.length * c' ^ v.length * K * d2 Φ Ψ :=
    norm_deriv_comp_sub_le Φ Ψ hc'0 hcc' hc' hL₁0 hL₁ v hx
  have hDg : ‖Dg‖ ≤ c' ^ v.length := norm_deriv_comp_le_pow Ψ hc'0.le hc' v hx
  have hA : ‖Φ.nonlin i a‖ ≤ M := hM i a ha
  have hB : ‖Φ.nonlin i a - Ψ.nonlin i b‖ ≤ (L₂ / (1 - Φ.cmax) + (1 + M) / m) * d2 Φ Ψ := by
    calc _ ≤ ‖Φ.nonlin i a - Φ.nonlin i b‖ + ‖Φ.nonlin i b - Ψ.nonlin i b‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ L₂ * (d2 Φ Ψ / (1 - Φ.cmax)) + (1 + M) / m * d2 Φ Ψ :=
          add_le_add ((hL₂ i a ha b hb).trans (mul_le_mul_of_nonneg_left hab hL₂0))
            (norm_nonlin_sub_le Φ Ψ hm hM0 hgm hM i hb)
      _ = (L₂ / (1 - Φ.cmax) + (1 + M) / m) * d2 Φ Ψ := by ring
  calc ‖Φ.nonlin i a * Df - Ψ.nonlin i b * Dg‖
      = ‖Φ.nonlin i a * (Df - Dg) + (Φ.nonlin i a - Ψ.nonlin i b) * Dg‖ := by
        congr 1; ring
    _ ≤ ‖Φ.nonlin i a‖ * ‖Df - Dg‖ + ‖Φ.nonlin i a - Ψ.nonlin i b‖ * ‖Dg‖ := by
        rw [← norm_mul, ← norm_mul]; exact norm_add_le _ _
    _ ≤ M * (v.length * c' ^ v.length * K * d2 Φ Ψ) +
          ((L₂ / (1 - Φ.cmax) + (1 + M) / m) * d2 Φ Ψ) * c' ^ v.length :=
        add_le_add (mul_le_mul hA hDfg (norm_nonneg _) hM0)
          (mul_le_mul hB hDg (norm_nonneg _) (by positivity))
    _ = _ := by ring

theorem length_take_of_get?_eq_some {w : Word N} {n : ℕ} {i : Fin N}
    (h : w.get? n = some i) : (w.take n).length = n := by
  cases w with
  | fin l =>
    simp only [Word.get?, Word.take] at h ⊢
    rw [List.length_take]
    have := (List.getElem?_eq_some_iff.1 h).1
    omega
  | inf l => simp [Word.take]

/-- The termwise bound for the series (1.4). -/
theorem norm_dualTerm_sub_le (Φ : IFS N ε) (Ψ : IFS N ε') {c' L₁ L₂ m M : ℝ}
    (hc'0 : 0 < c') (hcc' : Φ.cmax ≤ c') (hc' : ∀ i, ∀ y ∈ I, ‖deriv (Ψ.f i) (y : ℂ)‖ ≤ c')
    (hm : 0 < m) (hgm : ∀ i, ∀ y ∈ I, m ≤ ‖deriv (Ψ.f i) (y : ℂ)‖)
    (hM0 : 0 ≤ M) (hM : ∀ i, ∀ y ∈ I, ‖Φ.nonlin i (y : ℂ)‖ ≤ M)
    (hL₁0 : 0 ≤ L₁) (hL₁ : ∀ i, ∀ a ∈ I, ∀ b ∈ I,
      ‖deriv (Φ.f i) (a : ℂ) - deriv (Φ.f i) (b : ℂ)‖ ≤ L₁ * ‖(a : ℂ) - b‖)
    (hL₂0 : 0 ≤ L₂) (hL₂ : ∀ i, ∀ a ∈ I, ∀ b ∈ I,
      ‖Φ.nonlin i (a : ℂ) - Φ.nonlin i (b : ℂ)‖ ≤ L₂ * ‖(a : ℂ) - b‖)
    (w : Word N) (n : ℕ) {x : ℝ} (hx : x ∈ I) :
    ‖Φ.dualTerm w n x - Ψ.dualTerm w n x‖ ≤
      (M * ((L₁ / (1 - Φ.cmax) + 1) / c') * n + (L₂ / (1 - Φ.cmax) + (1 + M) / m)) *
        c' ^ n * d2 Φ Ψ := by
  have hc := Φ.cmax_lt_one
  have hd := d2_nonneg Φ Ψ
  have hc1 : 0 < 1 - Φ.cmax := by linarith
  unfold dualTerm
  cases h : w.get? n with
  | none => simp only [sub_self, norm_zero]; positivity
  | some i =>
    have hlen : (w.take n).reverse.length = n := by
      rw [List.length_reverse, length_take_of_get?_eq_some h]
    have := norm_term_sub_le Φ Ψ hc'0 hcc' hc' hm hgm hM0 hM hL₁0 hL₁ hL₂0 hL₂ i
      (w.take n).reverse hx
    rw [hlen] at this
    exact this

end IFS.Continuity

namespace IFS

variable {N : ℕ} {ε : ℝ}

/-- (2.6): `|H_w(x) - Ĥ_w(x)| ≤ C' d₂(Φ, Ψ)` on `I`, for all words, when `Ψ` is close to `Φ`. -/
theorem exists_dualProj_sub_le_d2 (Φ : IFS N ε) :
    ∃ C' δ₀ : ℝ, 0 < δ₀ ∧ ∀ {ε' : ℝ} (Ψ : IFS N ε'), d2 Φ Ψ < δ₀ → ∀ (w : Word N), ∀ x ∈ I,
      ‖Φ.dualProj w x - Ψ.dualProj w x‖ ≤ C' * d2 Φ Ψ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- Without letters, every dual projection vanishes.
    refine ⟨0, 1, one_pos, fun Ψ _ w x _ => ?_⟩
    have h0 : ∀ {η : ℝ} (Θ : IFS 0 η) (n : ℕ) (z : ℂ), Θ.dualTerm w n z = 0 := by
      intro η Θ n z
      unfold dualTerm
      cases w.get? n with
      | none => rfl
      | some i => exact i.elim0
    simp [dualProj, h0]
  have hc0 := Φ.cmax_nonneg
  have hc1 := Φ.cmax_lt_one
  have hm := Φ.cmin_pos hN
  have hε2 : 0 < 2 * ε := by linarith [Φ.ε_pos]
  obtain ⟨M, hM0, hM⟩ := Φ.exists_nonlin_bound
  have hM' : ∀ i, ∀ y ∈ I, ‖Φ.nonlin i (y : ℂ)‖ ≤ M := fun i y hy =>
    hM i _ (Continuity.ofReal_mem_closure Φ.ε_pos hy)
  obtain ⟨L₁, hL₁0, hL₁⟩ := Continuity.exists_lipschitz_I_fin (h := fun i => deriv (Φ.f i))
    (fun _ => nbhd (2 * ε)) (fun _ => isOpen_nbhd _) (fun _ => Continuity.image_I_subset_nbhd hε2)
    (fun i => (Φ.differentiableOn_f i).deriv (isOpen_nbhd _))
  choose U hUo hUc _ hUd using Φ.exists_differentiableOn_nonlin
  obtain ⟨L₂, hL₂0, hL₂⟩ := Continuity.exists_lipschitz_I_fin (h := Φ.nonlin) U hUo
    (fun i => (Continuity.image_I_subset_closure Φ.ε_pos).trans (hUc i)) hUd
  set c := Φ.cmax
  set m := Φ.cmin
  set δ₀ := min ((1 - c) / 2) (m / 2)
  have hδ₀ : 0 < δ₀ := lt_min (by linarith) (by linarith)
  have hδ₀1 : δ₀ ≤ (1 - c) / 2 := min_le_left _ _
  have hδ₀2 : δ₀ ≤ m / 2 := min_le_right _ _
  set c' := c + δ₀
  have hc'0 : 0 < c' := by linarith
  have hc'1 : c' < 1 := by linarith
  set K := (L₁ / (1 - c) + 1) / c'
  set B := L₂ / (1 - c) + (1 + M) / (m / 2)
  have hsum : Summable fun n : ℕ => (M * K * n + B) * c' ^ n := by
    have h1 : Summable fun n : ℕ => (n : ℝ) ^ 1 * c' ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one 1
        (by rw [Real.norm_eq_abs, abs_of_pos hc'0]; exact hc'1)
    have h2 : Summable fun n : ℕ => c' ^ n := summable_geometric_of_lt_one hc'0.le hc'1
    convert (h1.mul_left (M * K)).add (h2.mul_left B) using 1
    ext n; ring
  refine ⟨∑' n : ℕ, (M * K * n + B) * c' ^ n, δ₀, hδ₀, fun {ε'} Ψ hΨ w x hx => ?_⟩
  have hd := Continuity.d2_nonneg Φ Ψ
  have hP1 : ∀ i, ∀ y ∈ I, ‖deriv (Ψ.f i) (y : ℂ)‖ ≤ c' := fun i y hy => by
    have h1 := (Continuity.norm_sub_le_d2 Φ Ψ i hy).2.1
    have h2 := Φ.norm_deriv_le_cmax i (Continuity.ofReal_mem_closure Φ.ε_pos hy)
    have h3 := norm_sub_norm_le (deriv (Ψ.f i) y) (deriv (Φ.f i) y)
    rw [norm_sub_rev] at h3
    linarith
  have hP2 : ∀ i, ∀ y ∈ I, m / 2 ≤ ‖deriv (Ψ.f i) (y : ℂ)‖ := fun i y hy => by
    have h1 := (Continuity.norm_sub_le_d2 Φ Ψ i hy).2.1
    have h2 := Φ.cmin_le_norm_deriv i (Continuity.ofReal_mem_closure Φ.ε_pos hy)
    have h3 := norm_sub_norm_le (deriv (Φ.f i) y) (deriv (Ψ.f i) y)
    linarith
  have hterm : ∀ n : ℕ, ‖Φ.dualTerm w n x - Ψ.dualTerm w n x‖ ≤
      (M * K * n + B) * c' ^ n * d2 Φ Ψ := fun n =>
    Continuity.norm_dualTerm_sub_le Φ Ψ hc'0 (by linarith) hP1 (by linarith) hP2 hM0 hM' hL₁0
      hL₁ hL₂0 hL₂ w n hx
  have hxc := Continuity.ofReal_mem_closure Φ.ε_pos hx
  have hxc' := Continuity.ofReal_mem_closure Ψ.ε_pos hx
  rw [dualProj, dualProj, ← (Φ.summable_dualTerm w hxc).tsum_sub (Ψ.summable_dualTerm w hxc')]
  exact tsum_of_norm_bounded (hsum.hasSum.mul_right _) hterm

/-- Lemma 2.7 for `𝔖_N`: if the dual of `Φ` satisfies the SSC, so does the dual of every
`Ψ ∈ 𝔖_N` close to `Φ` in the `𝒞²` metric. The radius depends only on `Φ`, and `Ψ` may lie in
`𝔖_N(ε')` for any `ε'`. -/
theorem lemma_2_7_union (Φ : IFS N ε) (h : Φ.DualSSC) :
    ∃ δ > 0, ∀ {ε' : ℝ} (Ψ : IFS N ε'), d2 Φ Ψ < δ → Ψ.DualSSC := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- Without letters, an attractor would be a nonempty empty union.
    exfalso
    obtain ⟨Λ, ⟨-, hne, -, heq⟩, -⟩ := h
    rw [heq] at hne
    simp at hne
  obtain ⟨δ, hδ, hsep⟩ := (Φ.dualSSC_iff_exists_delta hN).1 h
  obtain ⟨C', δ₀, hδ₀, hC'⟩ := Φ.exists_dualProj_sub_le_d2
  refine ⟨min δ₀ (δ / (3 * (|C'| + 1))), lt_min hδ₀ (by positivity), fun {ε'} Ψ hΨ => ?_⟩
  have hd := Continuity.d2_nonneg Φ Ψ
  have hΨδ₀ : d2 Φ Ψ < δ₀ := hΨ.trans_le (min_le_left _ _)
  have hsmall : C' * d2 Φ Ψ < δ / 3 := by
    have h1 : d2 Φ Ψ < δ / (3 * (|C'| + 1)) := hΨ.trans_le (min_le_right _ _)
    have h2 : C' * d2 Φ Ψ ≤ |C'| * d2 Φ Ψ := mul_le_mul_of_nonneg_right (le_abs_self _) hd
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith [abs_nonneg C']
  obtain ⟨MΨ, -, hMΨ, -⟩ := Ψ.exists_dualProj_bounds
  refine (Ψ.dualSSC_iff_exists_delta hN).2 ⟨δ / 3, by positivity, fun i j hij => ?_⟩
  obtain ⟨⟨x, hx⟩, hxδ⟩ := exists_lt_of_lt_ciSup (hsep i j hij)
  have hbdd : BddAbove (range fun y : I =>
      ‖Ψ.dualProj (.inf i) ((y : ℝ) : ℂ) - Ψ.dualProj (.inf j) ((y : ℝ) : ℂ)‖) := by
    refine ⟨2 * MΨ, ?_⟩
    rintro _ ⟨y, rfl⟩
    have hyc := Continuity.ofReal_mem_closure Ψ.ε_pos y.2
    calc _ ≤ ‖Ψ.dualProj (.inf i) ((y : ℝ) : ℂ)‖ + ‖Ψ.dualProj (.inf j) ((y : ℝ) : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ MΨ + MΨ := add_le_add (hMΨ _ _ hyc) (hMΨ _ _ hyc)
      _ = 2 * MΨ := by ring
  refine lt_of_lt_of_le ?_ (le_ciSup hbdd ⟨x, hx⟩)
  have hi := hC' Ψ hΨδ₀ (.inf i) x hx
  have hj := hC' Ψ hΨδ₀ (.inf j) x hx
  have tri := norm_sub_le_norm_sub_add_norm_sub (Φ.dualProj (.inf i) x)
    (Ψ.dualProj (.inf i) x) (Φ.dualProj (.inf j) x)
  have tri' := norm_sub_le_norm_sub_add_norm_sub (Ψ.dualProj (.inf i) x)
    (Ψ.dualProj (.inf j) x) (Φ.dualProj (.inf j) x)
  rw [norm_sub_rev (Ψ.dualProj (.inf j) x)] at tri'
  simp only at hxδ ⊢
  linarith

/-- Lemma 2.7: if the dual of `Φ` satisfies the SSC, so does the dual of every `Ψ ∈ 𝔖_N(ε)` close
to `Φ` in the `𝒞²` metric. -/
theorem lemma_2_7 (Φ : IFS N ε) (h : Φ.DualSSC) :
    ∃ δ > 0, ∀ Ψ : IFS N ε, d2 Φ Ψ < δ → Ψ.DualSSC :=
  let ⟨δ, hδ, hΨ⟩ := Φ.lemma_2_7_union h
  ⟨δ, hδ, fun Ψ => hΨ Ψ⟩

end IFS

end AnalyticESC
