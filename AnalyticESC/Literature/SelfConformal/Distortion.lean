module

public import AnalyticESC.Literature.SelfConformal.Coding

@[expose] public section

/-!
# Bounded distortion

Lemma 2.1(1) of A. Rapaport, *Dimension of self-conformal measures associated to an exponentially
separated analytic IFS on ℝ*, arXiv:2412.16753v2, and its standard consequences, for a system
`φ` satisfying `AnalyticESC.RapaportHyp φ`.

## Main declarations

* `logLip`, `abs_log_abs_deriv_sub_le`: `log |φ_i'|` is `logLip φ`-Lipschitz on `I`.
* `distConst`, `one_lt_distConst`, `abs_deriv_realComp_le`: the bounded distortion property
  `|φ_u'(x)| ≤ C |φ_u'(y)|` for all words `u` and `x, y ∈ I`, with `C = distConst φ > 1`.
* `deriv_realComp_ne_zero`, `cmin_pow_le_abs_deriv_realComp`, `abs_deriv_realComp_le_cmax_pow`:
  `c_min^n ≤ |φ_u'(x)| ≤ c_max^n` for `|u| = n`.
* `abs_realComp_sub_le_distConst`, `distConst_inv_mul_le_abs_realComp_sub`:
  `C⁻¹ |φ_u'(z)| |x - y| ≤ |φ_u x - φ_u y| ≤ C |φ_u'(z)| |x - y|` on `I`.
* `abs_deriv_realComp_le_iSup`, `iSup_abs_deriv_realComp_le`: the sup norm of `φ_u'` on `I` lies
  between `|φ_u'(0)|` and `C |φ_u'(0)|`.
* `diam_image_realComp_le`, `distConst_inv_mul_le_diam_image_realComp`: `diam φ_u(I)` is comparable
  to `|φ_u'(0)|`.

Copied from the library `FractalGeometry` (module `FractalGeometry.SelfConformal.Distortion`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.SelfConformal

open MeasureTheory Set Filter Topology
open AnalyticESC (I realComp RapaportHyp IsProbVec)

variable {N : ℕ} {φ : Fin N → ℝ → ℝ}

/-! ### Lipschitz continuity of `log |φ_i'|` -/

/-- The second derivative of each map is continuous on `I`. -/
theorem continuousOn_deriv_deriv_map (hφ : RapaportHyp φ) (i : Fin N) :
    ContinuousOn (deriv (deriv (φ i))) I :=
  (analyticOnNhd_deriv_map hφ i).deriv.continuousOn

/-- The derivative of each map is differentiable at the points of `I`. -/
theorem differentiableAt_deriv_map (hφ : RapaportHyp φ) (i : Fin N) {x : ℝ} (hx : x ∈ I) :
    DifferentiableAt ℝ (deriv (φ i)) x :=
  (analyticOnNhd_deriv_map hφ i x hx).differentiableAt

/-- `max_{i, x ∈ I} |φ_i''(x)|`. -/
noncomputable def d2max (φ : Fin N → ℝ → ℝ) : ℝ := ⨆ i, ⨆ x : I, |deriv (deriv (φ i)) x|

/-- `|φ_i''(x)| ≤ d2max φ` on `I`. -/
theorem abs_deriv_deriv_le_d2max (hφ : RapaportHyp φ) (i : Fin N) {x : ℝ} (hx : x ∈ I) :
    |deriv (deriv (φ i)) x| ≤ d2max φ := by
  obtain ⟨_, _, hmax⟩ := isCompact_I.exists_isMaxOn ⟨0, zero_mem_I⟩
    (continuousOn_deriv_deriv_map hφ i).abs
  refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove i)
  exact le_ciSup (f := fun y : I => |deriv (deriv (φ i)) y|)
    ⟨_, forall_mem_range.2 fun y => isMaxOn_iff.1 hmax y y.2⟩ ⟨x, hx⟩

/-- `0 ≤ d2max φ`. -/
theorem d2max_nonneg : 0 ≤ d2max φ :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _

/-- The Lipschitz constant `d2max φ / c_min` of `log |φ_i'|` on `I`. -/
noncomputable def logLip (φ : Fin N → ℝ → ℝ) : ℝ := d2max φ / cmin φ

/-- `0 ≤ logLip φ`. -/
theorem logLip_nonneg : 0 ≤ logLip φ := div_nonneg d2max_nonneg cmin_nonneg

/-- `|log |φ_i'(x)| - log |φ_i'(y)|| ≤ logLip φ * |x - y|` on `I`. -/
theorem abs_log_abs_deriv_sub_le (hφ : RapaportHyp φ) (i : Fin N) {x y : ℝ} (hx : x ∈ I)
    (hy : y ∈ I) :
    |Real.log (|deriv (φ i) x|) - Real.log (|deriv (φ i) y|)| ≤ logLip φ * |x - y| := by
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by subst h; exact i.elim0
  have hne : ∀ z ∈ I, deriv (φ i) z ≠ 0 := fun z hz => abs_pos.1 (hφ.deriv_pos i z hz)
  have hd : ∀ z ∈ I, HasDerivAt (fun w => Real.log (deriv (φ i) w))
      (deriv (deriv (φ i)) z / deriv (φ i) z) z := fun z hz =>
    (differentiableAt_deriv_map hφ i hz).hasDerivAt.log (hne z hz)
  have h := convex_I.norm_image_sub_le_of_norm_deriv_le (f := fun w => Real.log (deriv (φ i) w))
    (C := logLip φ) (fun z hz => (hd z hz).differentiableAt) (fun z hz => by
      rw [(hd z hz).deriv, norm_div, Real.norm_eq_abs, Real.norm_eq_abs, logLip]
      exact div_le_div₀ d2max_nonneg (abs_deriv_deriv_le_d2max hφ i hz) (cmin_pos hφ hN)
        (cmin_le_abs_deriv i hz)) hy hx
  simpa only [Real.norm_eq_abs, Real.log_abs] using h

/-! ### Derivatives of compositions -/

/-- `φ_u'` does not vanish on `I`. -/
theorem deriv_realComp_ne_zero (hφ : RapaportHyp φ) (u : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    deriv (realComp φ u) x ≠ 0 := by
  induction u with
  | nil => simp
  | cons i u ih =>
    rw [deriv_realComp_cons hφ i u hx]
    exact mul_ne_zero (abs_pos.1 (hφ.deriv_pos i _ (mapsTo_realComp hφ u hx))) ih

/-- `|φ_u'(x)| ≤ c_max^{|u|}` on `I`. -/
theorem abs_deriv_realComp_le_cmax_pow (hφ : RapaportHyp φ) (u : List (Fin N)) {x : ℝ}
    (hx : x ∈ I) : |deriv (realComp φ u) x| ≤ cmax φ ^ u.length := by
  induction u with
  | nil => simp
  | cons i u ih =>
    rw [deriv_realComp_cons hφ i u hx, abs_mul, List.length_cons, pow_succ']
    exact mul_le_mul (abs_deriv_le_cmax hφ i (mapsTo_realComp hφ u hx)) ih (abs_nonneg _)
      cmax_nonneg

/-- `c_min^{|u|} ≤ |φ_u'(x)|` on `I`. -/
theorem cmin_pow_le_abs_deriv_realComp (hφ : RapaportHyp φ) (u : List (Fin N)) {x : ℝ}
    (hx : x ∈ I) : cmin φ ^ u.length ≤ |deriv (realComp φ u) x| := by
  induction u with
  | nil => simp
  | cons i u ih =>
    rw [deriv_realComp_cons hφ i u hx, abs_mul, List.length_cons, pow_succ']
    exact mul_le_mul (cmin_le_abs_deriv i (mapsTo_realComp hφ u hx)) ih
      (pow_nonneg cmin_nonneg _) (abs_nonneg _)

/-- `log |φ_u'(x)| - log |φ_u'(y)| ≤ logLip φ ∑_{k < |u|} c_max^k` on `I`. -/
theorem log_abs_deriv_realComp_sub_le (hφ : RapaportHyp φ) (u : List (Fin N)) {x y : ℝ}
    (hx : x ∈ I) (hy : y ∈ I) :
    Real.log |deriv (realComp φ u) x| - Real.log |deriv (realComp φ u) y| ≤
      logLip φ * ∑ k ∈ Finset.range u.length, cmax φ ^ k := by
  induction u with
  | nil => simp
  | cons i u ih =>
    have hx' := mapsTo_realComp hφ u hx
    have hy' := mapsTo_realComp hφ u hy
    have hi : ∀ z ∈ I, deriv (φ i) z ≠ 0 := fun z hz => abs_pos.1 (hφ.deriv_pos i z hz)
    rw [deriv_realComp_cons hφ i u hx, deriv_realComp_cons hφ i u hy, abs_mul, abs_mul,
      Real.log_mul (abs_ne_zero.2 (hi _ hx')) (abs_ne_zero.2 (deriv_realComp_ne_zero hφ u hx)),
      Real.log_mul (abs_ne_zero.2 (hi _ hy')) (abs_ne_zero.2 (deriv_realComp_ne_zero hφ u hy)),
      List.length_cons, Finset.sum_range_succ, mul_add]
    have h1 := (le_abs_self _).trans (abs_log_abs_deriv_sub_le hφ i hx' hy')
    have h2 : logLip φ * |realComp φ u x - realComp φ u y| ≤ logLip φ * cmax φ ^ u.length :=
      mul_le_mul_of_nonneg_left (abs_realComp_sub_le_pow hφ u hx hy) logLip_nonneg
    linarith

/-- `∑_{k < n} c_max^k ≤ (1 - c_max)⁻¹`. -/
theorem sum_cmax_pow_le (hφ : RapaportHyp φ) (n : ℕ) :
    ∑ k ∈ Finset.range n, cmax φ ^ k ≤ (1 - cmax φ)⁻¹ := by
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) cmax_nonneg (cmax_lt_one hφ)
  rwa [← Finset.range_eq_Ico, pow_zero, one_div] at h

/-- The bounded distortion constant `C = exp(logLip φ / (1 - c_max) + 1)`. -/
noncomputable def distConst (φ : Fin N → ℝ → ℝ) : ℝ :=
  Real.exp (logLip φ * (1 - cmax φ)⁻¹ + 1)

/-- `1 < C`. -/
theorem one_lt_distConst (hφ : RapaportHyp φ) : 1 < distConst φ := by
  rw [distConst, Real.one_lt_exp_iff]
  have : 0 ≤ logLip φ * (1 - cmax φ)⁻¹ :=
    mul_nonneg logLip_nonneg (inv_nonneg.2 (sub_nonneg.2 (cmax_lt_one hφ).le))
  linarith

/-- `0 < C`. -/
theorem distConst_pos : 0 < distConst φ := Real.exp_pos _

/-- `log |φ_u'(x)| - log |φ_u'(y)| ≤ log C` on `I`. -/
theorem log_abs_deriv_realComp_sub_le_log (hφ : RapaportHyp φ) (u : List (Fin N)) {x y : ℝ}
    (hx : x ∈ I) (hy : y ∈ I) :
    Real.log |deriv (realComp φ u) x| - Real.log |deriv (realComp φ u) y| ≤
      Real.log (distConst φ) := by
  rw [distConst, Real.log_exp]
  refine (log_abs_deriv_realComp_sub_le hφ u hx hy).trans ?_
  have := mul_le_mul_of_nonneg_left (sum_cmax_pow_le hφ u.length) (logLip_nonneg (φ := φ))
  linarith

/-- `|log |φ_u'(x)| - log |φ_u'(y)|| ≤ log C` on `I`. -/
theorem abs_log_abs_deriv_realComp_sub_le (hφ : RapaportHyp φ) (u : List (Fin N)) {x y : ℝ}
    (hx : x ∈ I) (hy : y ∈ I) :
    |Real.log (|deriv (realComp φ u) x|) - Real.log (|deriv (realComp φ u) y|)| ≤
      Real.log (distConst φ) :=
  abs_sub_le_iff.2 ⟨log_abs_deriv_realComp_sub_le_log hφ u hx hy,
    log_abs_deriv_realComp_sub_le_log hφ u hy hx⟩

/-- **Bounded distortion** (Rapaport, Lemma 2.1(1)): `|φ_u'(x)| ≤ C |φ_u'(y)|` for every word
`u` and `x, y ∈ I`. -/
theorem abs_deriv_realComp_le (hφ : RapaportHyp φ) (u : List (Fin N)) {x y : ℝ} (hx : x ∈ I)
    (hy : y ∈ I) : |deriv (realComp φ u) x| ≤ distConst φ * |deriv (realComp φ u) y| := by
  have hxpos := abs_pos.2 (deriv_realComp_ne_zero hφ u hx)
  have hypos := abs_pos.2 (deriv_realComp_ne_zero hφ u hy)
  have h := log_abs_deriv_realComp_sub_le_log hφ u hx hy
  rw [← Real.log_le_log_iff hxpos (mul_pos distConst_pos hypos), Real.log_mul distConst_pos.ne'
    hypos.ne']
  linarith

/-- Bounded distortion, existential form: there is `C > 1` with `|φ_u'(x)| ≤ C |φ_u'(y)|` for
every word `u` and `x, y ∈ I`. -/
theorem exists_bounded_distortion (hφ : RapaportHyp φ) :
    ∃ C > 1, ∀ (u : List (Fin N)), ∀ x ∈ I, ∀ y ∈ I,
      |deriv (realComp φ u) x| ≤ C * |deriv (realComp φ u) y| :=
  ⟨distConst φ, one_lt_distConst hφ, fun u _ hx _ hy => abs_deriv_realComp_le hφ u hx hy⟩

/-- The mean value theorem for `φ_u` on `I`. -/
theorem exists_realComp_sub_eq (hφ : RapaportHyp φ) (u : List (Fin N)) {x y : ℝ} (hx : x ∈ I)
    (hy : y ∈ I) :
    ∃ c ∈ I, realComp φ u x - realComp φ u y = deriv (realComp φ u) c * (x - y) := by
  have key : ∀ a ∈ I, ∀ b ∈ I, a < b →
      ∃ c ∈ I, realComp φ u b - realComp φ u a = deriv (realComp φ u) c * (b - a) := by
    intro a ha b hb hab
    have hsub : Icc a b ⊆ I := Icc_subset_Icc ha.1 hb.2
    obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope (realComp φ u) hab
      ((continuousOn_realComp hφ u).mono hsub)
      fun z hz =>
        (differentiableAt_realComp hφ u (hsub (Ioo_subset_Icc_self hz))).differentiableWithinAt
    refine ⟨c, hsub (Ioo_subset_Icc_self hc), ?_⟩
    rw [hc', div_mul_cancel₀ _ (sub_ne_zero.2 hab.ne')]
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · obtain ⟨c, hc, h⟩ := key x hx y hy hxy
    exact ⟨c, hc, by linarith⟩
  · exact ⟨x, hx, by ring⟩
  · exact key y hy x hx hxy

/-- `|φ_u x - φ_u y| ≤ C |φ_u'(z)| |x - y|` on `I`. -/
theorem abs_realComp_sub_le_distConst (hφ : RapaportHyp φ) (u : List (Fin N)) {x y z : ℝ}
    (hx : x ∈ I) (hy : y ∈ I) (hz : z ∈ I) :
    |realComp φ u x - realComp φ u y| ≤ distConst φ * |deriv (realComp φ u) z| * |x - y| := by
  obtain ⟨c, hc, h⟩ := exists_realComp_sub_eq hφ u hx hy
  rw [h, abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_deriv_realComp_le hφ u hc hz) (abs_nonneg _)

/-- `C⁻¹ |φ_u'(z)| |x - y| ≤ |φ_u x - φ_u y|` on `I`. -/
theorem distConst_inv_mul_le_abs_realComp_sub (hφ : RapaportHyp φ) (u : List (Fin N))
    {x y z : ℝ} (hx : x ∈ I) (hy : y ∈ I) (hz : z ∈ I) :
    (distConst φ)⁻¹ * |deriv (realComp φ u) z| * |x - y| ≤ |realComp φ u x - realComp φ u y| := by
  obtain ⟨c, hc, h⟩ := exists_realComp_sub_eq hφ u hx hy
  rw [h, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  rw [inv_mul_le_iff₀ distConst_pos]
  exact abs_deriv_realComp_le hφ u hz hc

/-! ### Sup norms and diameters -/

instance : Nonempty I := ⟨⟨0, zero_mem_I⟩⟩

/-- `|φ_u'|` is bounded above on `I`. -/
theorem bddAbove_abs_deriv_realComp (hφ : RapaportHyp φ) (u : List (Fin N)) :
    BddAbove (range fun x : I => |deriv (realComp φ u) x|) :=
  ⟨_, forall_mem_range.2 fun x => abs_deriv_realComp_le hφ u x.2 zero_mem_I⟩

/-- `|φ_u'(x)| ≤ ‖φ_u'‖_I` for `x ∈ I`. -/
theorem abs_deriv_realComp_le_iSup (hφ : RapaportHyp φ) (u : List (Fin N)) {x : ℝ}
    (hx : x ∈ I) : |deriv (realComp φ u) x| ≤ ⨆ y : I, |deriv (realComp φ u) y| :=
  le_ciSup (bddAbove_abs_deriv_realComp hφ u) ⟨x, hx⟩

/-- `‖φ_u'‖_I ≤ C |φ_u'(z)|` for `z ∈ I`. -/
theorem iSup_abs_deriv_realComp_le (hφ : RapaportHyp φ) (u : List (Fin N)) {z : ℝ}
    (hz : z ∈ I) : ⨆ y : I, |deriv (realComp φ u) y| ≤ distConst φ * |deriv (realComp φ u) z| :=
  ciSup_le fun y => abs_deriv_realComp_le hφ u y.2 hz

/-- `diam φ_u(I) ≤ C |φ_u'(z)|` for `z ∈ I`. -/
theorem diam_image_realComp_le (hφ : RapaportHyp φ) (u : List (Fin N)) {z : ℝ} (hz : z ∈ I) :
    Metric.diam (realComp φ u '' I) ≤ distConst φ * |deriv (realComp φ u) z| := by
  refine Metric.diam_le_of_forall_dist_le (mul_nonneg distConst_pos.le (abs_nonneg _)) ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [Real.dist_eq]
  refine (abs_realComp_sub_le_distConst hφ u hx hy hz).trans ?_
  exact mul_le_of_le_one_right (mul_nonneg distConst_pos.le (abs_nonneg _))
    (abs_sub_le_one_of_mem_I hx hy)

/-- `C⁻¹ |φ_u'(z)| ≤ diam φ_u(I)` for `z ∈ I`. -/
theorem distConst_inv_mul_le_diam_image_realComp (hφ : RapaportHyp φ) (u : List (Fin N)) {z : ℝ}
    (hz : z ∈ I) :
    (distConst φ)⁻¹ * |deriv (realComp φ u) z| ≤ Metric.diam (realComp φ u '' I) := by
  have hb : Bornology.IsBounded (realComp φ u '' I) :=
    (isCompact_I.image_of_continuousOn (continuousOn_realComp hφ u)).isBounded
  have h := distConst_inv_mul_le_abs_realComp_sub hφ u one_mem_I zero_mem_I hz
  rw [sub_zero, abs_one, mul_one] at h
  refine h.trans ?_
  rw [← Real.dist_eq]
  exact Metric.dist_le_diam_of_mem hb (mem_image_of_mem _ one_mem_I)
    (mem_image_of_mem _ zero_mem_I)

end FractalGeometry.SelfConformal
