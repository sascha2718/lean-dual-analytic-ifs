module

public import AnalyticESC.Dual.Derivatives
public import AnalyticESC.Analysis

@[expose] public section

/-!
# Closeness estimates for the proof of Theorem 1.5

Section 3: if `f_{a u}` and `f_{b u}` are `η`-close on `I`, then `H_{a^←}` and `H_{b^←}` are close
on `f_u(I)` (the estimate (3.2)); and closeness of dual projections on an
interval of `I` passes to all their derivatives, as in (3.3).
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-- A complex number with zero imaginary part has norm the absolute value of its real part. -/
theorem norm_eq_abs_re_of_im_eq_zero {z : ℂ} (h : z.im = 0) : ‖z‖ = |z.re| := by
  conv_lhs => rw [← Complex.re_add_im z, h]
  simp

/-- Iterated derivatives of a map holomorphic on an open set are holomorphic there. -/
theorem differentiableOn_iteratedDeriv_of_isOpen {g : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hg : DifferentiableOn ℂ g V) (k : ℕ) : DifferentiableOn ℂ (iteratedDeriv k g) V := by
  induction k with
  | zero => simpa using hg
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv hV

/-- A holomorphic map that is real at the real points of an open set has real iterated
derivatives there. -/
theorem im_iteratedDeriv_eq_zero {g : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hg : DifferentiableOn ℂ g V) (hreal : ∀ t : ℝ, (t : ℂ) ∈ V → (g t).im = 0) (k : ℕ)
    {x : ℝ} (hx : (x : ℂ) ∈ V) : (iteratedDeriv k g x).im = 0 := by
  induction k generalizing x with
  | zero => simpa using hreal x hx
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact im_deriv_eq_zero hV (differentiableOn_iteratedDeriv_of_isOpen hV hg k)
      (fun t ht => ih ht) hx

/-- (3.3) for two maps holomorphic on `B_ε` and real at its real points: Lemma 3.1 iterated
`k` times, applied to their real restrictions. -/
theorem norm_iteratedDeriv_sub_le_of_real {ε : ℝ} (hε : 0 < ε) {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (nbhd ε)) (hh : DifferentiableOn ℂ h (nbhd ε))
    (hgr : ∀ t : ℝ, (t : ℂ) ∈ nbhd ε → (g t).im = 0)
    (hhr : ∀ t : ℝ, (t : ℂ) ∈ nbhd ε → (h t).im = 0) (k : ℕ) {p q η Q : ℝ} (hp : 0 ≤ p)
    (hq : q ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) (hQ : 0 ≤ Q)
    (hgQ : ∀ j ≤ k + 1, ∀ x ∈ Icc p q, ‖iteratedDeriv j g x‖ ≤ Q)
    (hhQ : ∀ j ≤ k + 1, ∀ x ∈ Icc p q, ‖iteratedDeriv j h x‖ ≤ Q)
    (hJ : 2 * (2 + Q) * η ^ ((2 : ℝ)⁻¹ ^ k) < q - p)
    (hgh : ∀ x ∈ Icc p q, ‖g x - h x‖ ≤ η) :
    ∀ x ∈ Icc p q, ‖iteratedDeriv k g x - iteratedDeriv k h x‖ ≤
      (2 + Q) ^ 2 * η ^ ((2 : ℝ)⁻¹ ^ k) := by
  have hV := isOpen_nbhd ε
  have hU : IsOpen {t : ℝ | (t : ℂ) ∈ nbhd ε} := hV.preimage Complex.continuous_ofReal
  have hsub : ∀ x ∈ Icc p q, (x : ℂ) ∈ nbhd ε := fun x hx =>
    ofReal_mem_nbhd hε (Icc_subset_Icc hp hq hx)
  have hdg : ∀ j, ∀ x ∈ Icc p q,
      iteratedDeriv j (fun t : ℝ => (g t).re) x = (iteratedDeriv j g x).re :=
    fun j x hx => iteratedDeriv_re_ofReal hV hg j (hsub x hx)
  have hdh : ∀ j, ∀ x ∈ Icc p q,
      iteratedDeriv j (fun t : ℝ => (h t).re) x = (iteratedDeriv j h x).re :=
    fun j x hx => iteratedDeriv_re_ofReal hV hh j (hsub x hx)
  have hcg : ContDiffOn ℝ (k + 1) (fun t : ℝ => (g t).re) {t : ℝ | (t : ℂ) ∈ nbhd ε} := by
    exact_mod_cast contDiffOn_re_ofReal hV hg (k + 1)
  have hch : ContDiffOn ℝ (k + 1) (fun t : ℝ => (h t).re) {t : ℝ | (t : ℂ) ∈ nbhd ε} := by
    exact_mod_cast contDiffOn_re_ofReal hV hh (k + 1)
  have key := abs_iteratedDeriv_sub_le k hU hsub hcg hch hη hη1 hQ
    (fun j hj x hx => by
      rw [hdg j x hx]; exact (Complex.abs_re_le_norm _).trans (hgQ j hj x hx))
    (fun j hj x hx => by
      rw [hdh j x hx]; exact (Complex.abs_re_le_norm _).trans (hhQ j hj x hx))
    hJ (fun x hx => by
      rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans (hgh x hx))
  intro x hx
  have him : (iteratedDeriv k g x - iteratedDeriv k h x).im = 0 := by
    rw [Complex.sub_im, im_iteratedDeriv_eq_zero hV hg hgr k (hsub x hx),
      im_iteratedDeriv_eq_zero hV hh hhr k (hsub x hx), sub_zero]
  rw [norm_eq_abs_re_of_im_eq_zero him, Complex.sub_re, ← hdg k x hx, ← hdh k x hx]
  exact key x hx

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- Equation (2.9) and the polynomial bounds from Lemma 2.8 give
`|f_w^{(k+1)}| ≤ E_k c_max^{|w|}`. For `k = 1, 2` these are the second- and
third-derivative bounds used at the start of Section 3. -/
theorem exists_iteratedDeriv_comp_decay (k : ℕ) :
    ∃ E ≥ 0, ∀ w : List (Fin N), ∀ x ∈ I,
      ‖iteratedDeriv (k + 1) (Φ.comp w) x‖ ≤ E * Φ.cmax ^ w.length := by
  obtain ⟨C, hC0, hC, -⟩ := Φ.exists_iteratedDeriv_bounds
  obtain ⟨E, hE0, hE⟩ := exists_norm_aeval_le_of_supported (gPoly_mem_supported k)
    C (fun ℓ _ => (hC0 ℓ).le)
  refine ⟨E, hE0, fun w x hx => ?_⟩
  have hz := ofReal_mem_nbhd Φ.ε_pos hx
  have heq := Φ.iteratedDeriv_succ_comp_reverse w.reverse k hz
  simp only [List.reverse_reverse] at heq
  rw [heq, norm_mul]
  calc _ ≤ Φ.cmax ^ w.length * E :=
      mul_le_mul (Φ.norm_deriv_comp_le w (subset_closure hz))
        (hE _ fun ℓ _ => hC ℓ x hx _) (norm_nonneg _) (pow_nonneg Φ.cmax_nonneg _)
    _ = _ := mul_comm _ _

/-- A common bound on `I` for the derivatives of order at most `k` of all compositions,
obtained from the polynomial identity and Lemma 2.8. -/
theorem exists_iteratedDeriv_comp_bound (k : ℕ) :
    ∃ Q, 0 ≤ Q ∧ ∀ j ≤ k, ∀ w : List (Fin N), ∀ x ∈ I, ‖iteratedDeriv j (Φ.comp w) x‖ ≤ Q := by
  choose E hE0 hE using Φ.exists_iteratedDeriv_comp_decay
  have hb : ∀ j, ∃ B ≥ 0, ∀ w : List (Fin N), ∀ x ∈ I,
      ‖iteratedDeriv j (Φ.comp w) x‖ ≤ B := by
    intro j
    cases j with
    | zero =>
      refine ⟨1, zero_le_one, fun w x hx => ?_⟩
      simp only [iteratedDeriv_zero]
      rw [Φ.comp_ofReal w hx, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Φ.re_comp_mem_I w hx).1]
      exact (Φ.re_comp_mem_I w hx).2
    | succ j =>
      refine ⟨E j, hE0 j, fun w x hx => (hE j w x hx).trans ?_⟩
      exact mul_le_of_le_one_right (hE0 j)
        (pow_le_one₀ Φ.cmax_nonneg Φ.cmax_lt_one.le)
  choose B hB0 hB using hb
  refine ⟨∑ j ∈ Finset.range (k + 1), B j,
    Finset.sum_nonneg fun j _ => hB0 j, fun j hj w x hx => ?_⟩
  exact (hB j w x hx).trans (Finset.single_le_sum (fun j _ => hB0 j)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))

/-- The estimate (3.2): with `|a| = |b| ≥ 1` and different last letters, `η`-closeness of `f_{a u}`
and `f_{b u}` on `I` gives closeness `K c_min^{-2n} η^{1/4}` of `H_{a^←}` and `H_{b^←}` along
`f_u`, where `n = |a| + |u|`. -/
theorem exists_dualProj_closeness :
    ∃ K η₀ : ℝ, 0 < η₀ ∧ ∀ a b u : List (Fin N), a.length = b.length → 0 < a.length →
      a.getLast? ≠ b.getLast? → ∀ η : ℝ, 0 < η → η ≤ η₀ →
        (∀ x ∈ I, ‖Φ.comp (a ++ u) x - Φ.comp (b ++ u) x‖ ≤ η) →
          ∀ x ∈ I, ‖Φ.dualProj (.fin a.reverse) (Φ.comp u x) - Φ.dualProj (.fin b.reverse) (Φ.comp u x)‖
            ≤ K * Φ.cmin⁻¹ ^ (2 * (a.length + u.length)) * η ^ ((1 : ℝ) / 4) := by
  obtain ⟨Q, hQ0, hQ⟩ := Φ.exists_iteratedDeriv_comp_bound 3
  obtain ⟨M, hM0, hM, -⟩ := Φ.exists_dualProj_bounds
  set c : ℝ := 1 / (4 * (2 + Q)) with hc_def
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by rw [hc_def, div_le_one (by positivity)]; linarith
  refine ⟨(M + 1) * (2 + Q) ^ 2, c ^ 4, by positivity,
    fun a b u hab ha _ η hη hη0 hclose x hx => ?_⟩
  -- Constants.
  have hN : 0 < N := by
    obtain ⟨i, -⟩ := List.exists_mem_of_length_pos ha
    exact i.pos
  have hcmin := Φ.cmin_pos hN
  have hcmin1 : Φ.cmin ≤ 1 := (Φ.cmin_le_cmax hN).trans Φ.cmax_lt_one.le
  have hcinv1 : 1 ≤ Φ.cmin⁻¹ := one_le_inv₀ hcmin |>.2 hcmin1
  -- Conditions on `η`.
  have hη1 : η ≤ 1 := hη0.trans (pow_le_one₀ hc0.le hc1)
  have h14 : η ^ ((1 : ℝ) / 4) ≤ c := by
    calc η ^ ((1 : ℝ) / 4) ≤ (c ^ 4) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow hη.le hη0 (by norm_num)
      _ = c := by rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have h12 : η ^ ((1 : ℝ) / 2) ≤ η ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_ge hη hη1 (by norm_num)
  have hcQ : 2 * (2 + Q) * c = 1 / 2 := by rw [hc_def]; field_simp; ring
  have hJ1 : 2 * (2 + Q) * η ^ ((2 : ℝ)⁻¹ ^ 1) < 1 - 0 := by
    have : ((2 : ℝ)⁻¹ ^ 1) = 1 / 2 := by norm_num
    rw [this]
    calc 2 * (2 + Q) * η ^ ((1 : ℝ) / 2) ≤ 2 * (2 + Q) * c := by gcongr; exact h12.trans h14
      _ < 1 - 0 := by rw [hcQ]; norm_num
  have hJ2 : 2 * (2 + Q) * η ^ ((2 : ℝ)⁻¹ ^ 2) < 1 - 0 := by
    have : ((2 : ℝ)⁻¹ ^ 2) = 1 / 4 := by norm_num
    rw [this]
    calc 2 * (2 + Q) * η ^ ((1 : ℝ) / 4) ≤ 2 * (2 + Q) * c := by gcongr
      _ < 1 - 0 := by rw [hcQ]; norm_num
  -- Closeness of first and second derivatives of `f_{a u}` and `f_{b u}`.
  set i := a ++ u with hi
  set j := b ++ u with hj
  have hlen : j.length = i.length := by simp [i, j, hab]
  have hQi : ∀ l ≤ 2 + 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv l (Φ.comp i) y‖ ≤ Q :=
    fun l hl y hy => hQ l hl i y hy
  have hQj : ∀ l ≤ 2 + 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv l (Φ.comp j) y‖ ≤ Q :=
    fun l hl y hy => hQ l hl j y hy
  have hri : ∀ t : ℝ, (t : ℂ) ∈ nbhd ε → (Φ.comp i t).im = 0 := fun t ht => Φ.im_comp_ofReal i ht
  have hrj : ∀ t : ℝ, (t : ℂ) ∈ nbhd ε → (Φ.comp j t).im = 0 := fun t ht => Φ.im_comp_ofReal j ht
  have hd1 := norm_iteratedDeriv_sub_le_of_real Φ.ε_pos (Φ.differentiableOn_comp i)
    (Φ.differentiableOn_comp j) hri hrj 1 le_rfl le_rfl hη hη1 hQ0
    (fun l hl => hQi l (by omega)) (fun l hl => hQj l (by omega)) hJ1 hclose x hx
  have hd2 := norm_iteratedDeriv_sub_le_of_real Φ.ε_pos (Φ.differentiableOn_comp i)
    (Φ.differentiableOn_comp j) hri hrj 2 le_rfl le_rfl hη hη1 hQ0 hQi hQj hJ2 hclose x hx
  rw [iteratedDeriv_one, iteratedDeriv_one] at hd1
  rw [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one] at hd2
  have e1 : ((2 : ℝ)⁻¹ ^ 1) = 1 / 2 := by norm_num
  have e2 : ((2 : ℝ)⁻¹ ^ 2) = 1 / 4 := by norm_num
  rw [e1] at hd1
  rw [e2] at hd2
  -- The distortions `f_{a u}''/f_{a u}'` and `f_{b u}''/f_{b u}'` at `x`.
  have hz : (x : ℂ) ∈ closure (nbhd ε) := subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)
  set A := deriv (Φ.comp i) x with hA_def
  set B := deriv (Φ.comp j) x with hB_def
  set A2 := deriv (deriv (Φ.comp i)) x with hA2_def
  set B2 := deriv (deriv (Φ.comp j)) x with hB2_def
  have hA : A ≠ 0 := Φ.deriv_comp_ne_zero i hz
  have hB : B ≠ 0 := Φ.deriv_comp_ne_zero j hz
  have hBn : Φ.cmin ^ i.length ≤ ‖B‖ := hlen ▸ Φ.cmin_pow_le_norm_deriv_comp j hz
  have hBinv : ‖B‖⁻¹ ≤ Φ.cmin⁻¹ ^ i.length := by
    rw [inv_pow]; exact inv_anti₀ (pow_pos hcmin _) hBn
  have hHi : Φ.dualProj (.fin i.reverse) x = A2 / A := Φ.dualProj_fin_reverse i hz
  have hHj : Φ.dualProj (.fin j.reverse) x = B2 / B := Φ.dualProj_fin_reverse j hz
  have hAM : ‖A2 / A‖ ≤ M := hHi ▸ hM _ _ hz
  set E := (2 + Q) ^ 2 * η ^ ((1 : ℝ) / 4) with hE
  have hAB : ‖B - A‖ ≤ E := by
    rw [norm_sub_rev]
    exact hd1.trans (mul_le_mul_of_nonneg_left h12 (by positivity))
  have hdist : ‖A2 / A - B2 / B‖ ≤ (M + 1) * E * Φ.cmin⁻¹ ^ i.length := by
    have hid : A2 / A - B2 / B = (A2 / A * (B - A) + (A2 - B2)) / B := by
      field_simp; ring
    rw [hid, norm_div, div_eq_mul_inv]
    have hE0 : 0 ≤ E := by positivity
    calc ‖A2 / A * (B - A) + (A2 - B2)‖ * ‖B‖⁻¹ ≤ (M * E + E) * Φ.cmin⁻¹ ^ i.length := by
          refine mul_le_mul ?_ hBinv (by positivity) (by positivity)
          refine (norm_add_le _ _).trans (add_le_add ?_ hd2)
          rw [norm_mul]
          exact mul_le_mul hAM hAB (norm_nonneg _) hM0
      _ = (M + 1) * E * Φ.cmin⁻¹ ^ i.length := by ring
  -- The cocycle identity.
  have hcoc : ∀ v : List (Fin N), Φ.dualProj (.fin (v ++ u).reverse) x =
      Φ.dualProj (.fin u.reverse) x +
        deriv (Φ.comp u) x * Φ.dualProj (.fin v.reverse) (Φ.comp u x) := by
    intro v
    have := Φ.dualProj_prepend u.reverse (.fin v.reverse) hz
    rw [List.reverse_reverse] at this
    simpa [Word.prepend, List.reverse_append] using this
  have hdiff : A2 / A - B2 / B = deriv (Φ.comp u) x *
      (Φ.dualProj (.fin a.reverse) (Φ.comp u x) - Φ.dualProj (.fin b.reverse) (Φ.comp u x)) := by
    rw [← hHi, ← hHj, hi, hj, hcoc a, hcoc b]; ring
  -- Divide by `f_u'(x)`.
  have hu : Φ.cmin ^ u.length ≤ ‖deriv (Φ.comp u) x‖ := Φ.cmin_pow_le_norm_deriv_comp u hz
  have hu0 : 0 < ‖deriv (Φ.comp u) x‖ := (pow_pos hcmin _).trans_le hu
  have huinv : ‖deriv (Φ.comp u) x‖⁻¹ ≤ Φ.cmin⁻¹ ^ i.length := by
    calc ‖deriv (Φ.comp u) x‖⁻¹ ≤ Φ.cmin⁻¹ ^ u.length := by
          rw [inv_pow]; exact inv_anti₀ (pow_pos hcmin _) hu
      _ ≤ Φ.cmin⁻¹ ^ i.length := pow_le_pow_right₀ hcinv1 (by simp [i])
  have hilen : i.length = a.length + u.length := by simp [i]
  set D := Φ.dualProj (.fin a.reverse) (Φ.comp u x) - Φ.dualProj (.fin b.reverse) (Φ.comp u x)
  have hD : ‖D‖ = ‖A2 / A - B2 / B‖ * ‖deriv (Φ.comp u) x‖⁻¹ := by
    rw [hdiff, norm_mul]; field_simp
  rw [hD]
  calc ‖A2 / A - B2 / B‖ * ‖deriv (Φ.comp u) x‖⁻¹
      ≤ (M + 1) * E * Φ.cmin⁻¹ ^ i.length * Φ.cmin⁻¹ ^ i.length :=
        mul_le_mul hdist huinv (by positivity) (by positivity)
    _ = (M + 1) * (2 + Q) ^ 2 * Φ.cmin⁻¹ ^ (2 * (a.length + u.length)) * η ^ ((1 : ℝ) / 4) := by
        rw [hE, ← hilen, two_mul, pow_add]; ring

/-- (3.3) for dual projections: closeness `η` of `H_v` and `H_w` on `[p, q] ⊆ I` gives closeness
`K η^{2^{-k}}` of their `k`-th derivatives, provided the interval is long compared with
`η^{2^{-k}}`. -/
theorem exists_iteratedDeriv_dualProj_closeness (k : ℕ) :
    ∃ K Q : ℝ, 0 ≤ Q ∧ ∀ (v w : Word N) (p q η : ℝ), 0 ≤ p → p < q → q ≤ 1 → 0 < η → η ≤ 1 →
      2 * (2 + Q) * η ^ ((2 : ℝ)⁻¹ ^ k) < q - p →
      (∀ x ∈ Icc p q, ‖Φ.dualProj v x - Φ.dualProj w x‖ ≤ η) →
        ∀ x ∈ Icc p q, ‖iteratedDeriv k (Φ.dualProj v) x - iteratedDeriv k (Φ.dualProj w) x‖ ≤
          K * η ^ ((2 : ℝ)⁻¹ ^ k) := by
  obtain ⟨C, hCpos, hC, -⟩ := Φ.exists_iteratedDeriv_bounds
  set Q := ∑ j ∈ Finset.range (k + 2), C j with hQ_def
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun j _ => (hCpos j).le
  have hCQ : ∀ j ≤ k + 1, C j ≤ Q := fun j hj =>
    Finset.single_le_sum (fun i _ => (hCpos i).le) (Finset.mem_range.2 (by omega))
  refine ⟨(2 + Q) ^ 2, Q, hQ0, fun v w p q η hp _ hq hη hη1 hJ hvw => ?_⟩
  exact norm_iteratedDeriv_sub_le_of_real Φ.ε_pos (Φ.differentiableOn_dualProj v)
    (Φ.differentiableOn_dualProj w) (fun t ht => Φ.im_dualProj_ofReal v ht)
    (fun t ht => Φ.im_dualProj_ofReal w ht) k hp hq hη hη1 hQ0
    (fun j hj x hx => (hC j x (Icc_subset_Icc hp hq hx) v).trans (hCQ j hj))
    (fun j hj x hx => (hC j x (Icc_subset_Icc hp hq hx) w).trans (hCQ j hj)) hJ hvw

/-- The denominator in (3.3) is a norm, including for orientation-reversing words.
The interval estimate implies the displayed bound and its `c_min` bound. -/
theorem norm_iteratedDeriv_sub_le_on_image (hN : 0 < N) (k : ℕ) (u : List (Fin N))
    {v w : Word N} {K η : ℝ} (hK : 0 ≤ K) (hη : 0 ≤ η)
    (hclose : ∀ y ∈ (fun t : ℝ => (Φ.comp u t).re) '' I,
      ‖iteratedDeriv k (Φ.dualProj v) y - iteratedDeriv k (Φ.dualProj w) y‖ ≤ K * η)
    {x : ℝ} (hx : x ∈ I) :
    ‖iteratedDeriv k (Φ.dualProj v) (Φ.comp u x) -
      iteratedDeriv k (Φ.dualProj w) (Φ.comp u x)‖ ≤
        K / ‖deriv (Φ.comp u) x‖ ^ k * η ∧
      K / ‖deriv (Φ.comp u) x‖ ^ k * η ≤ K * (Φ.cmin⁻¹ ^ k) ^ u.length * η := by
  have hx' := subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)
  have hd0 := norm_pos_iff.2 (Φ.deriv_comp_ne_zero u hx')
  have hd1 : ‖deriv (Φ.comp u) x‖ ^ k ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) ((Φ.norm_deriv_comp_le u hx').trans
      (pow_le_one₀ Φ.cmax_nonneg Φ.cmax_lt_one.le))
  constructor
  · rw [Φ.comp_ofReal u hx]
    exact (hclose _ ⟨x, hx, rfl⟩).trans (mul_le_mul_of_nonneg_right
      ((le_div_iff₀ (pow_pos hd0 k)).2 (mul_le_of_le_one_right hK hd1)) hη)
  · have hc := Φ.cmin_pos hN
    have hlow := pow_le_pow_left₀ (pow_nonneg hc.le u.length) (Φ.cmin_pow_le_norm_deriv_comp u hx') k
    apply mul_le_mul_of_nonneg_right _ hη
    calc K / ‖deriv (Φ.comp u) x‖ ^ k ≤ K / (Φ.cmin ^ u.length) ^ k :=
        div_le_div_of_nonneg_left hK (by positivity) hlow
      _ = K * (Φ.cmin⁻¹ ^ k) ^ u.length := by
        rw [div_eq_mul_inv, ← inv_pow, ← inv_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]


end IFS

end AnalyticESC
