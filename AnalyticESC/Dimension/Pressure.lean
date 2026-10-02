module

public import AnalyticESC.Dimension.Defs

@[expose] public section

/-!
# The pressure and the conformality dimension

The pressure `P(t) = lim_n (1/n) log ∑_{w ∈ Σ_n} ‖f_w'‖^t` of Section 1.2.1 exists for every `t`,
by sub-additivity, and vanishes at exactly one `t = s(Φ) ≥ 0`, the conformality dimension.
-/

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- `‖f_w'‖ > 0` for a nonempty alphabet. -/
private theorem pr_supDeriv_pos (hN : 0 < N) (w : List (Fin N)) : 0 < Φ.supDeriv w :=
  (pow_pos (Φ.cmin_pos hN) _).trans_le (Φ.cmin_pow_le_supDeriv w)

/-- Sub-multiplicativity `‖f_{uv}'‖ ≤ ‖f_u'‖ ‖f_v'‖`, from the chain rule and `f_v(I) ⊆ I`. -/
private theorem pr_supDeriv_append_le (u v : List (Fin N)) :
    Φ.supDeriv (u ++ v) ≤ Φ.supDeriv u * Φ.supDeriv v := by
  have : Nonempty I := ⟨⟨0, le_rfl, zero_le_one⟩⟩
  refine ciSup_le fun x => ?_
  have hx := x.2
  have hz : ((x : ℝ) : ℂ) ∈ closure (nbhd ε) := subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)
  have hu := Φ.norm_deriv_le_supDeriv u (Φ.re_comp_mem_I v hx)
  rw [Φ.deriv_comp_append u v hz, norm_mul, Φ.comp_ofReal v hx]
  exact mul_le_mul hu (Φ.norm_deriv_le_supDeriv v hx) (norm_nonneg _)
    ((norm_nonneg _).trans hu)

private theorem pr_pressureSum_pos (hN : 0 < N) (t : ℝ) (n : ℕ) : 0 < Φ.pressureSum t n :=
  Finset.sum_pos (fun _ _ => Real.rpow_pos_of_pos (Φ.pr_supDeriv_pos hN _) t)
    ⟨fun _ => ⟨0, hN⟩, Finset.mem_univ _⟩

/-- Each term of the pressure sum is at most the sum. -/
private theorem pr_term_le_pressureSum (hN : 0 < N) (t : ℝ) {n : ℕ} (v : Fin n → Fin N) :
    Φ.supDeriv (List.ofFn v) ^ t ≤ Φ.pressureSum t n :=
  Finset.single_le_sum (f := fun v : Fin n → Fin N => Φ.supDeriv (List.ofFn v) ^ t)
    (fun _ _ => (Real.rpow_pos_of_pos (Φ.pr_supDeriv_pos hN _) t).le) (Finset.mem_univ v)

/-- For `t ≥ 0`, the pressure sums are sub-multiplicative. -/
private theorem pr_pressureSum_add_le (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) (m n : ℕ) :
    Φ.pressureSum t (m + n) ≤ Φ.pressureSum t m * Φ.pressureSum t n := by
  rw [pressureSum, pressureSum, pressureSum, Finset.sum_mul_sum, ← Fintype.sum_prod_type',
    ← (Fin.appendEquiv m n).sum_comp]
  refine Finset.sum_le_sum fun p _ => ?_
  have hp : Fin.appendEquiv m n p = Fin.append p.1 p.2 := funext (Fin.appendEquiv_apply m n p)
  rw [hp, List.ofFn_fin_append, ← Real.mul_rpow (Φ.pr_supDeriv_pos hN _).le
    (Φ.pr_supDeriv_pos hN _).le]
  exact Real.rpow_le_rpow (Φ.pr_supDeriv_pos hN _).le (Φ.pr_supDeriv_append_le _ _) ht

/-- Raising the exponent from `t` to `t + h` multiplies each term by a factor between
`c_min^{nh}` and `c_max^{nh}`. -/
private theorem pr_log_pressureSum_add (hN : 0 < N) (t : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    Real.log (Φ.pressureSum t n) + n * (h * Real.log Φ.cmin) ≤
        Real.log (Φ.pressureSum (t + h) n) ∧
      Real.log (Φ.pressureSum (t + h) n) ≤
        Real.log (Φ.pressureSum t n) + n * (h * Real.log Φ.cmax) := by
  have hcmin := Φ.cmin_pos hN
  have hcmax : 0 < Φ.cmax := hcmin.trans_le (Φ.cmin_le_cmax hN)
  have hlog : ∀ c : ℝ, 0 < c → Real.log ((c ^ n) ^ h) = n * (h * Real.log c) := fun c hc => by
    rw [Real.log_rpow (pow_pos hc n), Real.log_pow]
    ring
  have hterm : ∀ v : Fin n → Fin N, Φ.supDeriv (List.ofFn v) ^ (t + h) =
      Φ.supDeriv (List.ofFn v) ^ t * Φ.supDeriv (List.ofFn v) ^ h := fun v =>
    Real.rpow_add (Φ.pr_supDeriv_pos hN _) t h
  have hP := Φ.pr_pressureSum_pos hN
  constructor
  · have hle : Φ.pressureSum t n * (Φ.cmin ^ n) ^ h ≤ Φ.pressureSum (t + h) n := by
      rw [pressureSum, pressureSum, Finset.sum_mul]
      refine Finset.sum_le_sum fun v _ => ?_
      rw [hterm]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos (Φ.pr_supDeriv_pos hN _) t).le
      have := Φ.cmin_pow_le_supDeriv (List.ofFn v)
      rw [List.length_ofFn] at this
      exact Real.rpow_le_rpow (pow_pos hcmin n).le this hh
    have := Real.log_le_log (mul_pos (hP t n) (Real.rpow_pos_of_pos (pow_pos hcmin n) h)) hle
    rwa [Real.log_mul (hP t n).ne' (Real.rpow_pos_of_pos (pow_pos hcmin n) h).ne',
      hlog _ hcmin] at this
  · have hle : Φ.pressureSum (t + h) n ≤ Φ.pressureSum t n * (Φ.cmax ^ n) ^ h := by
      rw [pressureSum, pressureSum, Finset.sum_mul]
      refine Finset.sum_le_sum fun v _ => ?_
      rw [hterm]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos (Φ.pr_supDeriv_pos hN _) t).le
      have := Φ.supDeriv_le (List.ofFn v)
      rw [List.length_ofFn] at this
      exact Real.rpow_le_rpow (Φ.pr_supDeriv_pos hN _).le this hh
    have := Real.log_le_log (hP (t + h) n) hle
    rwa [Real.log_mul (hP t n).ne' (Real.rpow_pos_of_pos (pow_pos hcmax n) h).ne',
      hlog _ hcmax] at this

/-- For `t ≥ 0`, `(1/n) log ∑_{w ∈ Σ_n} ‖f_w'‖^t` converges, by Fekete's lemma. -/
private theorem pr_exists_tendsto (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) :
    ∃ p, Tendsto (fun n : ℕ => Real.log (Φ.pressureSum t n) / n) atTop (𝓝 p) := by
  have hsub : Subadditive fun n => Real.log (Φ.pressureSum t n) := by
    intro m n
    have hP := Φ.pr_pressureSum_pos hN t
    rw [← Real.log_mul (hP m).ne' (hP n).ne']
    exact Real.log_le_log (hP _) (Φ.pr_pressureSum_add_le hN ht m n)
  refine ⟨hsub.lim, hsub.tendsto_lim ⟨t * Real.log Φ.cmin, ?_⟩⟩
  rintro _ ⟨n, rfl⟩
  have hlmin : Real.log Φ.cmin < 0 :=
    Real.log_neg (Φ.cmin_pos hN) ((Φ.cmin_le_cmax hN).trans_lt Φ.cmax_lt_one)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, div_zero]
    exact mul_nonpos_of_nonneg_of_nonpos ht hlmin.le
  · have h := (Φ.pr_log_pressureSum_add hN 0 ht n).1
    have h0 : Real.log (Φ.pressureSum 0 n) ≥ 0 := by
      refine Real.log_nonneg ?_
      have := Φ.pr_term_le_pressureSum hN 0 (fun _ : Fin n => (⟨0, hN⟩ : Fin N))
      rwa [Real.rpow_zero] at this
    rw [zero_add] at h
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hn']
    nlinarith

/-- The pressure has a unique zero `s(Φ) ≥ 0`: the limit `lim_n (1/n) log ∑_{w ∈ Σ_n} ‖f_w'‖^t`
exists and equals `0` exactly for `t = s(Φ)`. -/
theorem exists_pressure_zero (hN : 0 < N) :
    ∃ s : ℝ, 0 ≤ s ∧
      ∀ t, Tendsto (fun n : ℕ => Real.log (Φ.pressureSum t n) / n) atTop (𝓝 0) ↔ t = s := by
  set a : ℝ → ℕ → ℝ := fun t n => Real.log (Φ.pressureSum t n) / n with ha_def
  set P : ℝ → ℝ := fun t => limUnder atTop (a t) with hP_def
  have hP : ∀ t, 0 ≤ t → Tendsto (a t) atTop (𝓝 (P t)) := fun t ht =>
    tendsto_nhds_limUnder (Φ.pr_exists_tendsto hN ht)
  have hcmin := Φ.cmin_pos hN
  have hcmax : 0 < Φ.cmax := hcmin.trans_le (Φ.cmin_le_cmax hN)
  set lmin := Real.log Φ.cmin with hlmin_def
  set lmax := Real.log Φ.cmax with hlmax_def
  have hlmax : lmax < 0 := Real.log_neg hcmax Φ.cmax_lt_one
  have hlmin : lmin ≤ lmax := Real.log_le_log hcmin (Φ.cmin_le_cmax hN)
  -- `P(t) + h log c_min ≤ P(t + h) ≤ P(t) + h log c_max`
  have hmono : ∀ t h, 0 ≤ t → 0 ≤ h → P t + h * lmin ≤ P (t + h) ∧ P (t + h) ≤ P t + h * lmax := by
    intro t h ht hh
    have hev : ∀ᶠ n : ℕ in atTop, a t n + h * lmin ≤ a (t + h) n ∧
        a (t + h) n ≤ a t n + h * lmax := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      obtain ⟨h1, h2⟩ := Φ.pr_log_pressureSum_add hN t hh n
      simp only [ha_def]
      rw [div_add' _ _ _ hn'.ne', div_add' _ _ _ hn'.ne', div_le_div_iff_of_pos_right hn',
        div_le_div_iff_of_pos_right hn']
      constructor <;> linarith
    exact ⟨le_of_tendsto_of_tendsto ((hP t ht).add_const _) (hP (t + h) (by linarith))
        (hev.mono fun n hn => hn.1),
      le_of_tendsto_of_tendsto (hP (t + h) (by linarith)) ((hP t ht).add_const _)
        (hev.mono fun n hn => hn.2)⟩
  -- `P(0) ≥ 0`
  have hP0 : 0 ≤ P 0 := by
    refine ge_of_tendsto' (hP 0 le_rfl) fun n => div_nonneg (Real.log_nonneg ?_) n.cast_nonneg
    have := Φ.pr_term_le_pressureSum hN 0 (fun _ : Fin n => (⟨0, hN⟩ : Fin N))
    rwa [Real.rpow_zero] at this
  -- `P` is continuous on `[0, ∞)`
  have hcont : ContinuousOn P (Ici 0) := by
    refine (LipschitzOnWith.of_dist_le' (K := -lmin) fun x hx y hy => ?_).continuousOn
    rw [Real.dist_eq, Real.dist_eq]
    rcases le_total x y with hxy | hxy
    · obtain ⟨h1, h2⟩ := hmono x (y - x) hx (sub_nonneg.2 hxy)
      rw [add_sub_cancel] at h1 h2
      rw [abs_sub_comm x y, abs_of_nonneg (sub_nonneg.2 hxy), abs_le]
      constructor <;> nlinarith
    · obtain ⟨h1, h2⟩ := hmono y (x - y) hy (sub_nonneg.2 hxy)
      rw [add_sub_cancel] at h1 h2
      rw [abs_of_nonneg (sub_nonneg.2 hxy), abs_le]
      constructor <;> nlinarith
  -- the intermediate value theorem on `[0, T]` with `P(T) ≤ 0`
  set T := P 0 / -lmax with hT_def
  have hT : 0 ≤ T := div_nonneg hP0 (by linarith)
  have hPT : P T ≤ 0 := by
    have h2 := (hmono 0 T le_rfl hT).2
    rw [zero_add] at h2
    have : T * lmax = -P 0 := by
      rw [hT_def, div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self hlmax.ne, mul_one]
    linarith
  obtain ⟨s, hs, hPs⟩ : (0 : ℝ) ∈ P '' Icc 0 T :=
    intermediate_value_Icc' hT (hcont.mono fun x hx => hx.1) ⟨hPT, hP0⟩
  refine ⟨s, hs.1, fun t => ⟨fun h => ?_, ?_⟩⟩
  · rcases lt_or_ge t 0 with ht | ht
    · -- for `t < 0`, every term is at least `c_max^{nt} ≥ 1`
      exfalso
      have hpos : 0 < t * lmax := mul_pos_of_neg_of_neg ht hlmax
      have hev : ∀ᶠ n : ℕ in atTop, t * lmax ≤ a t n := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        have h1 := Φ.pr_term_le_pressureSum hN t (fun _ : Fin n => (⟨0, hN⟩ : Fin N))
        have h2 := Φ.supDeriv_le (List.ofFn fun _ : Fin n => (⟨0, hN⟩ : Fin N))
        rw [List.length_ofFn] at h2
        have h3 := Real.rpow_le_rpow_of_nonpos (Φ.pr_supDeriv_pos hN _) h2 ht.le
        have h4 := Real.log_le_log (Real.rpow_pos_of_pos (pow_pos hcmax n) t) (h3.trans h1)
        rw [Real.log_rpow (pow_pos hcmax n), Real.log_pow] at h4
        simp only [ha_def]
        rw [le_div_iff₀ hn']
        linarith
      have := ge_of_tendsto h hev
      linarith
    · have hPt : P t = 0 := tendsto_nhds_unique (hP t ht) h
      by_contra hts
      rcases lt_or_gt_of_ne hts with hts | hts
      · have := (hmono t (s - t) ht (sub_nonneg.2 hts.le)).2
        rw [add_sub_cancel] at this
        nlinarith
      · have := (hmono s (t - s) hs.1 (sub_nonneg.2 hts.le)).2
        rw [add_sub_cancel] at this
        nlinarith
  · rintro rfl
    rw [← hPs]
    exact hP t hs.1

end IFS

end AnalyticESC
