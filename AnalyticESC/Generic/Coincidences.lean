module

public import AnalyticESC.Generic.Class
public import AnalyticESC.Analysis

@[expose] public section

/-!
# The interpolation in the proof of Theorem 1.4

A `d₂`-small perturbation of an IFS whose maps send `[0,1]` into `(0,1)` and whose compositions
along distinct finite words differ on `[0,1]`.

The perturbation is `f_i^t = (1 - t) f_i + t h_i` for a small `t > 0`, where the affine maps
`h_i(z) = a z + b_i` have pairwise disjoint images `h_i(I) ⊆ (0,1)`, so that distinct compositions
of the `h_i` differ on `I`. For fixed words and a
fixed point of `I`, compositions of the `f_i^t` are holomorphic in the complex parameter `t` on an
open set containing `[0,1]`, so two of them agree for finitely many `t ∈ [0,1]` only. A countable
union of finite sets misses some small `t > 0`. Auxiliary results are in the namespace
`IFS.Coincidences`.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace IFS.Coincidences

variable {N : ℕ} {ε : ℝ}

/-! ## The affine maps `h_i` -/

/-- The common slope `a = 1/(2(N+2))` of the affine maps `h_i`. -/
noncomputable def slope (N : ℕ) : ℝ := 1 / (2 * (N + 2))

/-- The offset `b_i = (i+1)/(N+2)` of the affine map `h_i`. -/
noncomputable def offset (i : Fin N) : ℝ := (((i : ℕ) : ℝ) + 1) / (N + 2)

/-- `a > 0`. -/
theorem slope_pos : 0 < slope N := by unfold slope; positivity

/-- `a < 1`. -/
theorem slope_lt_one : slope N < 1 := by
  unfold slope
  rw [div_lt_one (by positivity)]
  linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

/-- `b_i > 0`. -/
theorem offset_pos (i : Fin N) : 0 < offset i := by unfold offset; positivity

/-- `b_i + a = (2i + 3)/(2(N+2))`. -/
private theorem offset_add_slope_eq (i : Fin N) :
    offset i + slope N = (2 * ((i : ℕ) : ℝ) + 3) / (2 * (N + 2)) := by
  unfold offset slope
  field_simp
  ring

/-- `h_i(I) = [b_i, b_i + a] ⊆ (0,1)`. -/
theorem offset_add_slope_lt_one (i : Fin N) : offset i + slope N < 1 := by
  have hi : ((i : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast i.isLt
  rw [offset_add_slope_eq, div_lt_one (by positivity)]
  linarith

/-- The intervals `h_i(I) = [b_i, b_i + a]` are pairwise disjoint. -/
theorem offset_add_slope_lt_offset {i j : Fin N} (hij : i < j) : offset i + slope N < offset j := by
  have hij' : (i : ℕ) + 1 ≤ j := hij
  have hij'' : ((i : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast hij'
  have hj : offset j = (2 * ((j : ℕ) : ℝ) + 2) / (2 * (N + 2)) := by
    unfold offset
    field_simp
  rw [offset_add_slope_eq, hj]
  exact div_lt_div_of_pos_right (by linarith) (by positivity)

/-- The affine map `h_i(z) = a z + b_i`. -/
noncomputable def target (i : Fin N) (z : ℂ) : ℂ := slope N * z + offset i

/-- `h_i` is real at real points. -/
theorem target_ofReal (i : Fin N) (x : ℝ) : target i x = ((slope N * x + offset i : ℝ) : ℂ) := by
  simp [target]

/-! ## The perturbations `f_i^t` -/

variable (Φ : IFS N ε)

/-- The map `f_i^t = (1 - t) f_i + t h_i`, for a complex parameter `t`. -/
noncomputable def homotopy (t : ℂ) (i : Fin N) (z : ℂ) : ℂ := (1 - t) * Φ.f i z + t * target i z

/-- The composition `f^t_w = f^t_{w₁} ∘ ⋯ ∘ f^t_{w_k}` of the maps `f_i^t`. -/
noncomputable def compT (t : ℂ) (w : List (Fin N)) : ℂ → ℂ :=
  w.foldr (fun i g => homotopy Φ t i ∘ g) id

/-- `f^t_{iw} = f_i^t ∘ f^t_w`. -/
theorem compT_cons (t : ℂ) (i : Fin N) (w : List (Fin N)) :
    compT Φ t (i :: w) = homotopy Φ t i ∘ compT Φ t w :=
  rfl

/-- `f_i^1 = h_i`. -/
theorem homotopy_one (i : Fin N) (z : ℂ) : homotopy Φ 1 i z = target i z := by simp [homotopy]

/-- For real `t`, the map `f_i^t` is real at the real points of `B_{2ε}`. -/
theorem im_homotopy_ofReal (t : ℝ) (i : Fin N) {x : ℝ} (hx : (x : ℂ) ∈ nbhd (2 * ε)) :
    (homotopy Φ t i x).im = 0 := by
  simp [homotopy, target, Complex.mul_im, Φ.im_f_ofReal i hx]

/-- For real `t` and `x`, `Re f_i^t(x) = (1 - t) Re f_i(x) + t h_i(x)`. -/
theorem re_homotopy_ofReal (t : ℝ) (i : Fin N) (x : ℝ) :
    (homotopy Φ t i x).re = (1 - t) * (Φ.f i x).re + t * (slope N * x + offset i) := by
  simp [homotopy, target, Complex.mul_re]

/-- For `t ∈ [0,1]`, the map `f_i^t` sends `I` into `I`. -/
theorem re_homotopy_mem_I {t : ℝ} (ht : t ∈ I) (i : Fin N) {x : ℝ} (hx : x ∈ I) :
    (homotopy Φ t i x).re ∈ I := by
  rw [re_homotopy_ofReal]
  have hf := (Φ.inClass i).re_mem_I x hx
  have h1 := offset_pos i
  have h2 := offset_add_slope_lt_one i
  have h3 : 0 ≤ slope N * x := mul_nonneg slope_pos.le hx.1
  have h4 : slope N * x ≤ slope N := mul_le_of_le_one_right slope_pos.le hx.2
  obtain ⟨ht0, ht1⟩ := ht
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 ht1) hf.1]
  · nlinarith [mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hf.2)]

/-- For `t ∈ (0,1)`, the map `f_i^t` sends `I` into `(0,1)`. -/
theorem re_homotopy_mem_Ioo {t : ℝ} (ht : t ∈ Ioo 0 1) (i : Fin N) {x : ℝ} (hx : x ∈ I) :
    (homotopy Φ t i x).re ∈ Ioo 0 1 := by
  rw [re_homotopy_ofReal]
  have hf := (Φ.inClass i).re_mem_I x hx
  have h1 := offset_pos i
  have h2 := offset_add_slope_lt_one i
  have h3 : 0 ≤ slope N * x := mul_nonneg slope_pos.le hx.1
  have h4 : slope N * x ≤ slope N := mul_le_of_le_one_right slope_pos.le hx.2
  obtain ⟨ht0, ht1⟩ := ht
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 ht1.le) hf.1]
  · nlinarith [mul_nonneg (sub_nonneg.2 ht1.le) (sub_nonneg.2 hf.2)]

/-- For `t ∈ [0,1]`, the compositions `f^t_w` send real points of `I` to real points of `I`. -/
theorem exists_compT_ofReal {t : ℝ} (ht : t ∈ I) (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    ∃ y ∈ I, compT Φ t w x = y := by
  induction w with
  | nil => exact ⟨x, hx, rfl⟩
  | cons i w ih =>
    obtain ⟨y, hy, hyx⟩ := ih
    refine ⟨(homotopy Φ t i y).re, re_homotopy_mem_I Φ ht i hy, ?_⟩
    rw [compT_cons, Function.comp_apply, hyx]
    refine Complex.ext (by simp) ?_
    rw [Complex.ofReal_im]
    exact im_homotopy_ofReal Φ t i (ofReal_mem_nbhd (by linarith [Φ.ε_pos]) hy)

/-! ## Distinct compositions of the affine maps -/

/-- For `x ∈ I`, the point `h_{iw}(x)` lies in `h_i(I) = [b_i, b_i + a]`. -/
theorem re_compT_one_cons_mem (i : Fin N) (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    (compT Φ 1 (i :: w) x).re ∈ Icc (offset i) (offset i + slope N) := by
  obtain ⟨y, hy, hyx⟩ := exists_compT_ofReal Φ (t := 1) ⟨zero_le_one, le_rfl⟩ w hx
  rw [Complex.ofReal_one] at hyx
  rw [compT_cons, Function.comp_apply, hyx, homotopy_one, target_ofReal, Complex.ofReal_re]
  have h3 : 0 ≤ slope N * y := mul_nonneg slope_pos.le hy.1
  have h4 : slope N * y ≤ slope N := mul_le_of_le_one_right slope_pos.le hy.2
  constructor <;> linarith

/-- Compositions of the affine maps `h_i` along distinct finite words differ on `I`. -/
theorem exists_compT_one_ne (u v : List (Fin N)) (huv : u ≠ v) :
    ∃ x ∈ I, compT Φ 1 u x ≠ compT Φ 1 v x := by
  have h0 : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩
  -- a nonempty word sends `0` to a point with positive real part
  have hpos : ∀ i w, 0 < (compT Φ 1 (i :: w) ((0 : ℝ) : ℂ)).re := fun i w =>
    (offset_pos i).trans_le (re_compT_one_cons_mem Φ i w h0).1
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => exact absurd rfl huv
    | cons j v =>
      refine ⟨0, h0, fun h => (hpos j v).ne' ?_⟩
      rw [← h]
      simp [compT]
  | cons i u ih =>
    cases v with
    | nil =>
      refine ⟨0, h0, fun h => (hpos i u).ne' ?_⟩
      rw [h]
      simp [compT]
    | cons j v =>
      by_cases hij : i = j
      · -- equal first letters: `h_i` is injective
        subst hij
        obtain ⟨x, hx, hne⟩ := ih v fun h => huv (by rw [h])
        refine ⟨x, hx, fun h => hne ?_⟩
        rw [compT_cons, compT_cons, Function.comp_apply, Function.comp_apply, homotopy_one,
          homotopy_one] at h
        have ha : (slope N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 slope_pos.ne'
        exact mul_left_cancel₀ ha (add_right_cancel h)
      · -- distinct first letters: the images of `0` lie in disjoint intervals
        refine ⟨0, h0, fun h => ?_⟩
        have hi := re_compT_one_cons_mem Φ i u h0
        have hj := re_compT_one_cons_mem Φ j v h0
        rw [h] at hi
        rcases lt_or_gt_of_ne hij with hlt | hlt
        · linarith [offset_add_slope_lt_offset hlt, hi.2, hj.1]
        · linarith [offset_add_slope_lt_offset hlt, hi.1, hj.2]

/-! ## The perturbations lie in the class -/

/-- `(f_i^t)' = (1 - t) f_i' + t a` where `f_i` is differentiable. -/
theorem hasDerivAt_homotopy (t : ℂ) (i : Fin N) {z : ℂ} (hz : DifferentiableAt ℂ (Φ.f i) z) :
    HasDerivAt (homotopy Φ t i) ((1 - t) * deriv (Φ.f i) z + t * slope N) z := by
  have h := (hz.hasDerivAt.const_mul (1 - t)).add
    ((((hasDerivAt_id z).const_mul (slope N : ℂ)).add_const (offset i : ℂ)).const_mul t)
  exact h.congr_deriv (by simp)

/-- `(f_i^t)' = (1 - t) f_i' + t a` on `B_{2ε}`. -/
theorem deriv_homotopy (t : ℂ) (i : Fin N) {z : ℂ} (hz : z ∈ nbhd (2 * ε)) :
    deriv (homotopy Φ t i) z = (1 - t) * deriv (Φ.f i) z + t * slope N :=
  (hasDerivAt_homotopy Φ t i
    ((Φ.differentiableOn_f i).differentiableAt ((isOpen_nbhd _).mem_nhds hz))).deriv

/-- For `0 < t < c_min/(c_min + 1)`, the map `f_i^t` lies in `S^ω_ε(I)`. -/
theorem inClass_homotopy {t : ℝ} (ht0 : 0 < t) (ht : t * (Φ.cmin + 1) < Φ.cmin) (i : Fin N) :
    InClass ε (homotopy Φ t i) := by
  have hc := Φ.cmin_nonneg
  have ht1 : t < 1 := by nlinarith
  have ha := slope_pos (N := N)
  have ha1 := slope_lt_one (N := N)
  -- on `cl B_ε`, `(f_i^t)' = (1 - t) f_i' + t a`
  have hder : ∀ z ∈ closure (nbhd ε), deriv (homotopy Φ t i) z =
      ((1 - t : ℝ) : ℂ) * deriv (Φ.f i) z + ((t * slope N : ℝ) : ℂ) := by
    intro z hz
    rw [deriv_homotopy Φ t i (IFS.closure_nbhd_subset_two hz)]
    push_cast
    ring
  have hn1 : ∀ z, ‖((1 - t : ℝ) : ℂ) * deriv (Φ.f i) z‖ = (1 - t) * ‖deriv (Φ.f i) z‖ := by
    intro z
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hn2 : ‖((t * slope N : ℝ) : ℂ)‖ = t * slope N := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine InClass.of_deriv Φ.ε_pos ?_ ?_ ?_ ?_ ?_
  · intro z hz
    exact (hasDerivAt_homotopy Φ t i ((Φ.differentiableOn_f i).differentiableAt
      ((isOpen_nbhd _).mem_nhds hz))).differentiableAt.differentiableWithinAt
  · exact fun x hx => im_homotopy_ofReal Φ t i hx
  · exact fun x hx => re_homotopy_mem_I Φ ⟨ht0.le, ht1.le⟩ i hx
  · -- `|(f_i^t)'| ≥ (1 - t) c_min - t a > 0`
    intro z hz h0
    have hlow := Φ.cmin_le_norm_deriv i hz
    have h := norm_sub_le
      (((1 - t : ℝ) : ℂ) * deriv (Φ.f i) z + ((t * slope N : ℝ) : ℂ)) ((t * slope N : ℝ) : ℂ)
    rw [add_sub_cancel_right, ← hder z hz, h0, norm_zero, hn1, hn2] at h
    nlinarith [mul_le_mul_of_nonneg_left hlow (by linarith : (0 : ℝ) ≤ 1 - t),
      mul_lt_mul_of_pos_left ha1 ht0]
  · -- `|(f_i^t)'| ≤ (1 - t) |f_i'| + t a < 1`
    intro z hz
    have hup := (Φ.inClass i).norm_deriv_lt_one z hz
    rw [hder z hz]
    calc _ ≤ ‖((1 - t : ℝ) : ℂ) * deriv (Φ.f i) z‖ + ‖((t * slope N : ℝ) : ℂ)‖ :=
          norm_add_le _ _
      _ = (1 - t) * ‖deriv (Φ.f i) z‖ + t * slope N := by rw [hn1, hn2]
      _ < 1 := by
          nlinarith [mul_lt_mul_of_pos_left hup (by linarith : (0 : ℝ) < 1 - t),
            mul_lt_mul_of_pos_left ha1 ht0]

/-! ## The distance to the perturbation -/

/-- A common bound for the second derivatives `f_i''` on `I`. -/
theorem exists_deriv_deriv_bound :
    ∃ K, 0 ≤ K ∧ ∀ i, ∀ x ∈ I, ‖deriv (deriv (Φ.f i)) x‖ ≤ K := by
  have hO := isOpen_nbhd (2 * ε)
  have hIU : ((↑) : ℝ → ℂ) '' I ⊆ nbhd (2 * ε) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ofReal_mem_nbhd (by linarith [Φ.ε_pos]) hx
  have h : ∀ i, ∃ C, ∀ z ∈ ((↑) : ℝ → ℂ) '' I, ‖deriv (deriv (Φ.f i)) z‖ ≤ C := fun i =>
    isCompact_image_I.exists_bound_of_continuousOn
      ((((Φ.differentiableOn_f i).deriv hO).deriv hO).continuousOn.mono hIU)
  choose C hC using h
  refine ⟨∑ i, |C i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun i x hx => ?_⟩
  calc ‖deriv (deriv (Φ.f i)) x‖ ≤ C i := hC i x (mem_image_of_mem _ hx)
    _ ≤ |C i| := le_abs_self _
    _ ≤ ∑ i, |C i| :=
        Finset.single_le_sum (f := fun i => |C i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)

/-- `d₂(f_i, f_i^t) ≤ t (4 + K)` for `t ∈ [0,1]`, where `K` bounds `|f_i''|` on `I`. -/
theorem d2Map_homotopy_le (i : Fin N) {K : ℝ} (hK : 0 ≤ K)
    (hK' : ∀ x ∈ I, ‖deriv (deriv (Φ.f i)) x‖ ≤ K) {t : ℝ} (ht : t ∈ I) :
    d2Map (Φ.f i) (homotopy Φ t i) ≤ t * (4 + K) := by
  have hmem : ∀ x : I, ((x : ℝ) : ℂ) ∈ nbhd (2 * ε) := fun x =>
    ofReal_mem_nbhd (by linarith [Φ.ε_pos]) x.2
  have hcl : ∀ x : I, ((x : ℝ) : ℂ) ∈ closure (nbhd ε) := fun x =>
    subset_closure (ofReal_mem_nbhd Φ.ε_pos x.2)
  have ht0 := ht.1
  have hnt : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_of_nonneg ht0]
  -- the values differ by `t (f_i - h_i)`
  have e0 : ∀ x : I, ‖Φ.f i ((x : ℝ) : ℂ) - homotopy Φ t i ((x : ℝ) : ℂ)‖ ≤ t * 2 := by
    intro x
    have hf : ‖Φ.f i ((x : ℝ) : ℂ)‖ ≤ 1 := by
      have hre := (Φ.inClass i).re_mem_I x x.2
      rw [← Complex.re_add_im (Φ.f i _), Φ.im_f_ofReal i (hmem x), Complex.ofReal_zero,
        zero_mul, add_zero, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hre.1, hre.2]
    have hh : ‖target i ((x : ℝ) : ℂ)‖ ≤ 1 := by
      have h3 : 0 ≤ slope N * x := mul_nonneg slope_pos.le x.2.1
      have h4 : slope N * x ≤ slope N := mul_le_of_le_one_right slope_pos.le x.2.2
      rw [target_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [offset_pos i, offset_add_slope_lt_one i]
    have e : Φ.f i ((x : ℝ) : ℂ) - homotopy Φ t i ((x : ℝ) : ℂ) =
        t * (Φ.f i ((x : ℝ) : ℂ) - target i ((x : ℝ) : ℂ)) := by
      unfold homotopy
      ring
    rw [e, norm_mul, hnt]
    exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by linarith)) ht0
  -- the first derivatives differ by `t (f_i' - a)`
  have e1 : ∀ x : I,
      ‖deriv (Φ.f i) ((x : ℝ) : ℂ) - deriv (homotopy Φ t i) ((x : ℝ) : ℂ)‖ ≤ t * 2 := by
    intro x
    have h1 := (Φ.inClass i).norm_deriv_lt_one _ (hcl x)
    have h2 : ‖(slope N : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg slope_pos.le]
      exact slope_lt_one.le
    have e : deriv (Φ.f i) ((x : ℝ) : ℂ) - deriv (homotopy Φ t i) ((x : ℝ) : ℂ) =
        t * (deriv (Φ.f i) ((x : ℝ) : ℂ) - slope N) := by
      rw [deriv_homotopy Φ t i (hmem x)]
      ring
    rw [e, norm_mul, hnt]
    exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by linarith)) ht0
  -- the second derivatives differ by `t f_i''`
  have e2 : ∀ x : I, ‖deriv (deriv (Φ.f i)) ((x : ℝ) : ℂ) -
      deriv (deriv (homotopy Φ t i)) ((x : ℝ) : ℂ)‖ ≤ t * K := by
    intro x
    have heq : deriv (homotopy Φ t i) =ᶠ[𝓝 ((x : ℝ) : ℂ)]
        fun z => (1 - t) * deriv (Φ.f i) z + t * slope N := by
      filter_upwards [(isOpen_nbhd _).mem_nhds (hmem x)] with z hz using deriv_homotopy Φ t i hz
    have hd : DifferentiableAt ℂ (deriv (Φ.f i)) ((x : ℝ) : ℂ) :=
      ((Φ.differentiableOn_f i).deriv (isOpen_nbhd _)).differentiableAt
        ((isOpen_nbhd _).mem_nhds (hmem x))
    rw [heq.deriv_eq, deriv_add_const, deriv_const_mul _ hd]
    have e : deriv (deriv (Φ.f i)) ((x : ℝ) : ℂ) - (1 - t) * deriv (deriv (Φ.f i)) ((x : ℝ) : ℂ) =
        t * deriv (deriv (Φ.f i)) ((x : ℝ) : ℂ) := by ring
    rw [e, norm_mul, hnt]
    exact mul_le_mul_of_nonneg_left (hK' x x.2) ht0
  have s0 := Real.iSup_le e0 (by positivity)
  have s1 := Real.iSup_le e1 (by positivity)
  have s2 := Real.iSup_le e2 (by positivity)
  unfold d2Map
  linarith

/-! ## Coincidences for finitely many parameters -/

/-- For a fixed word `w` and `x ∈ I`, the map `t ↦ f^t_w(x)` is holomorphic on an open set
containing `[0,1]`. -/
theorem exists_differentiableOn_compT (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    ∃ O : Set ℂ, IsOpen O ∧ ((↑) : ℝ → ℂ) '' I ⊆ O ∧
      DifferentiableOn ℂ (fun t => compT Φ t w x) O := by
  induction w with
  | nil => exact ⟨univ, isOpen_univ, subset_univ _, differentiableOn_const _⟩
  | cons i w ih =>
    obtain ⟨O, hO, hIO, hd⟩ := ih
    refine ⟨O ∩ (fun t => compT Φ t w x) ⁻¹' nbhd (2 * ε),
      hd.continuousOn.isOpen_inter_preimage hO (isOpen_nbhd _), ?_, ?_⟩
    · -- for `t ∈ [0,1]`, `f^t_w(x)` is a point of `I`
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨y, hy, hyx⟩ := exists_compT_ofReal Φ hs w hx
      refine ⟨hIO (mem_image_of_mem _ hs), ?_⟩
      show compT Φ s w x ∈ nbhd (2 * ε)
      rw [hyx]
      exact ofReal_mem_nbhd (by linarith [Φ.ε_pos]) hy
    · have hg := hd.mono (inter_subset_left (t := (fun t => compT Φ t w x) ⁻¹' nbhd (2 * ε)))
      have hf : DifferentiableOn ℂ (fun t => Φ.f i (compT Φ t w x))
          (O ∩ (fun t => compT Φ t w x) ⁻¹' nbhd (2 * ε)) :=
        (Φ.differentiableOn_f i).comp hg fun t ht => ht.2
      show DifferentiableOn ℂ
        (fun t => (1 - t) * Φ.f i (compT Φ t w x) + t * (slope N * compT Φ t w x + offset i)) _
      fun_prop

/-- If `h_u(x) ≠ h_v(x)`, then `f^t_u(x) = f^t_v(x)` for finitely many `t ∈ [0,1]` only. -/
theorem finite_compT_eq {u v : List (Fin N)} {x : ℝ} (hx : x ∈ I)
    (hne : compT Φ 1 u x ≠ compT Φ 1 v x) :
    {t : ℝ | t ∈ I ∧ compT Φ t u x = compT Φ t v x}.Finite := by
  obtain ⟨Ou, hOu, hIu, hdu⟩ := exists_differentiableOn_compT Φ u hx
  obtain ⟨Ov, hOv, hIv, hdv⟩ := exists_differentiableOn_compT Φ v hx
  obtain ⟨ρ, hρ, hsub⟩ :=
    isCompact_image_I.exists_thickening_subset_open (hOu.inter hOv) (subset_inter hIu hIv)
  have hsub' : nbhd ρ ⊆ Ou ∩ Ov := hsub
  have hd : DifferentiableOn ℂ (fun t => compT Φ t u x - compT Φ t v x) (nbhd ρ) :=
    (hdu.mono (hsub'.trans inter_subset_left)).sub (hdv.mono (hsub'.trans inter_subset_right))
  refine (finite_zeros hρ hd ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩).subset ?_
  · simpa [sub_eq_zero] using hne
  · rintro t ⟨ht, heq⟩
    exact ⟨ht, sub_eq_zero.2 heq⟩

end IFS.Coincidences

namespace IFS

open Coincidences

variable {N : ℕ} {ε : ℝ}

/-- The interpolation at the start of the density proof of Theorem 1.4. Every `Φ ∈ 𝔖_N(ε)` has, for
every `r > 0`, a perturbation `Ψ ∈ 𝔖_N(ε)` with `d₂(Φ, Ψ) < r` whose maps send `[0,1]` into `(0,1)`
and whose compositions along distinct finite words differ on `[0,1]`. -/
theorem lemma_4_2 (Φ : IFS N ε) {r : ℝ} (hr : 0 < r) :
    ∃ Ψ : IFS N ε, d2 Φ Ψ < r ∧ (∀ i, ∀ x ∈ I, (Ψ.f i x).re ∈ Ioo 0 1) ∧ Ψ.NoCoincidence := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · -- without maps, `Ψ = Φ` works: every word is empty
    subst hN
    have hw : ∀ w : List (Fin 0), w = [] := fun w => by
      cases w with
      | nil => rfl
      | cons i _ => exact i.elim0
    refine ⟨Φ, ?_, fun i => i.elim0, fun u v huv => absurd (by rw [hw u, hw v]) huv⟩
    rw [d2, Real.iSup_of_isEmpty]
    exact hr
  set c := Φ.cmin
  have hc : 0 < c := Φ.cmin_pos hN
  obtain ⟨K, hK, hK'⟩ := exists_deriv_deriv_bound Φ
  -- the parameters `t ∈ [0,1]` at which two compositions along distinct words coincide on `I`
  set B : Set ℝ := ⋃ p : List (Fin N) × List (Fin N),
    {t | t ∈ I ∧ p.1 ≠ p.2 ∧ ∀ x ∈ I, compT Φ t p.1 x = compT Φ t p.2 x}
  have hB : B.Countable := by
    refine countable_iUnion fun p => Finite.countable ?_
    by_cases hp : p.1 = p.2
    · simp [hp]
    · obtain ⟨x, hx, hne⟩ := exists_compT_one_ne Φ p.1 p.2 hp
      exact (finite_compT_eq Φ hx hne).subset fun t ht => ⟨ht.1, ht.2.2 x hx⟩
  set t₀ := min (c / (c + 1)) (r / (4 + K))
  have ht₀ : 0 < t₀ := lt_min (by positivity) (by positivity)
  obtain ⟨t, htB, ht⟩ := (hB.dense_compl ℝ).exists_mem_open isOpen_Ioo (nonempty_Ioo.2 ht₀)
  have ht1 : t * (c + 1) < c :=
    (lt_div_iff₀ (by positivity)).1 (ht.2.trans_le (min_le_left _ _))
  have ht2 : t * (4 + K) < r :=
    (lt_div_iff₀ (by positivity)).1 (ht.2.trans_le (min_le_right _ _))
  have ht_lt : t < 1 := by nlinarith [ht.1]
  have htI : t ∈ I := ⟨ht.1.le, ht_lt.le⟩
  let Ψ : IFS N ε := ⟨homotopy Φ t, Φ.ε_pos, inClass_homotopy Φ ht.1 ht1⟩
  refine ⟨Ψ, ?_, fun i x hx => re_homotopy_mem_Ioo Φ ⟨ht.1, ht_lt⟩ i hx, ?_⟩
  · have h : ∀ i, d2Map (Φ.f i) (Ψ.f i) ≤ t * (4 + K) := fun i =>
      d2Map_homotopy_le Φ i hK (hK' i) htI
    exact (Real.iSup_le h (mul_nonneg ht.1.le (by linarith))).trans_lt ht2
  · -- `t ∉ B`
    intro u v huv
    by_contra h
    refine htB (mem_iUnion.2 ⟨(u, v), htI, huv, fun x hx => ?_⟩)
    by_contra hne
    exact h ⟨x, hx, hne⟩

end IFS

end AnalyticESC
