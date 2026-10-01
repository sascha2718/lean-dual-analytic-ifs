module

public import AnalyticESC.Generic.Class

@[expose] public section

/-!
# Proposition 4.4

A perturbation of a map of `S^ω(I)` that is small in `𝒞¹` on `[0,1]`, agrees with the map to
first order on a finite set `𝒴 ∪ 𝒵` and to second order on `𝒵`, and changes `f''/f'` by at least
`δ` at the points of `𝒴`, at a cost of `C δ` in the second derivative.

## Construction

The perturbation is additive: `g = f + D` with
`D(z) = ∑_{y ∈ 𝒴} δ f'(y) G_y(z) P_y(z)`, where `G_y(z) = (z - y)² e^{-(z - y)²/r²} / 2` is a
Gaussian bump of width `r` and `P_y(z) = ∏_{w ∈ 𝒴 ∪ 𝒵, w ≠ y} ((z - w)/(y - w))³`. Each term has a
double zero at its centre `y` with second derivative `δ f'(y)` there, and a triple zero at the
other points of `𝒴 ∪ 𝒵`. Hence `D` and `D'` vanish on `𝒴 ∪ 𝒵`, `D''` vanishes on `𝒵`, and
`D''(y) = δ f'(y)` for `y ∈ 𝒴`, for every width `r`. On a circle of radius `r` about a point of
`[0,1]`, the term of the nearest centre is at most `3 δ r²` and the others are `O(r⁴)`, so
`|D| ≤ 4 δ r²` there. Cauchy estimates give `|D|, |D'| = O(r)` and `|D''| ≤ 8 δ` on `[0,1]`, so
`C = 8` for every `f`. Lemma 4.1 (`exists_inClass`) places `g` in `S^ω(I)` once `r` is small.

The paper perturbs multiplicatively, `g = f e^{φ ψ A}`, and bounds the derivatives on `[0,1]`
term by term with the bound (4.3).
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace Bump

/-! ## The bump -/

/-- The Gaussian bump `G_{σ,y}(z) = (z - y)² e^{-(z - y)²/σ} / 2`. -/
noncomputable def gauss (σ y : ℝ) (z : ℂ) : ℂ :=
  (z - y) ^ 2 * Complex.exp (-(z - y) ^ 2 / σ) / 2

/-- The interpolation factor `P_y(z) = ∏_{v ∈ W, v ≠ y} ((z - v)/(y - v))³`. -/
noncomputable def interp (W : Finset ℝ) (y : ℝ) (z : ℂ) : ℂ :=
  ∏ v ∈ W.erase y, ((z - v) / (y - v)) ^ 3

/-- The perturbation `D(z) = ∑_{y ∈ Y} c_y G_{σ,y}(z) P_y(z)`. -/
noncomputable def pert (W Y : Finset ℝ) (c : ℝ → ℝ) (σ : ℝ) (z : ℂ) : ℂ :=
  ∑ y ∈ Y, (c y : ℂ) * gauss σ y z * interp W y z

/-- `G_{σ,y}` is entire. -/
theorem differentiable_gauss (σ y : ℝ) : Differentiable ℂ (gauss σ y) := by
  unfold gauss
  fun_prop

/-- `P_y` is entire. -/
theorem differentiable_interp (W : Finset ℝ) (y : ℝ) : Differentiable ℂ (interp W y) := by
  unfold interp
  fun_prop

/-- `D` is entire. -/
theorem differentiable_pert (W Y : Finset ℝ) (c : ℝ → ℝ) (σ : ℝ) :
    Differentiable ℂ (pert W Y c σ) := by
  unfold pert gauss interp
  fun_prop

/-- The derivative of an entire map is entire. -/
theorem differentiable_deriv {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (deriv F) := fun z =>
  differentiableWithinAt_univ.1 (hF.differentiableOn.deriv isOpen_univ z (mem_univ z))

/-- `P_y(y) = 1`. -/
theorem interp_self (W : Finset ℝ) (y : ℝ) : interp W y y = 1 := by
  refine Finset.prod_eq_one fun v hv => ?_
  have h : (y : ℂ) - v ≠ 0 :=
    sub_ne_zero.2 (by exact_mod_cast (Finset.ne_of_mem_erase hv).symm)
  rw [div_self h, one_pow]

/-- `D` is real at real points. -/
theorem im_pert_ofReal (W Y : Finset ℝ) (c : ℝ → ℝ) (σ x : ℝ) : (pert W Y c σ x).im = 0 := by
  have h : pert W Y c σ x = ((∑ y ∈ Y, c y * ((x - y) ^ 2 * Real.exp (-(x - y) ^ 2 / σ) / 2) *
      ∏ v ∈ W.erase y, ((x - v) / (y - v)) ^ 3 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [h, Complex.ofReal_im]

/-! ## Values at the interpolation points -/

/-- A map with a double zero at `w`: `h(w) = h'(w) = 0` and `h''(w) = 2 F(w)`. -/
theorem sq_mul_deriv {F : ℂ → ℂ} (hF : Differentiable ℂ F) (w : ℂ) :
    (fun z => (z - w) ^ 2 * F z) w = 0 ∧ deriv (fun z => (z - w) ^ 2 * F z) w = 0 ∧
      deriv (deriv fun z => (z - w) ^ 2 * F z) w = 2 * F w := by
  have hF' := differentiable_deriv hF
  have hd : deriv (fun z => (z - w) ^ 2 * F z) =
      fun z => (z - w) * (2 * F z + (z - w) * deriv F z) := by
    funext z
    have h1 : HasDerivAt (fun z => (z - w) ^ 2) (2 * (z - w)) z := by
      simpa using ((hasDerivAt_id' z).sub_const w).fun_pow 2
    rw [(h1.fun_mul (hF z).hasDerivAt).deriv]
    ring
  have hK := ((hasDerivAt_id' w).sub_const w).fun_mul
    (((hF w).hasDerivAt.const_mul 2).fun_add
      (((hasDerivAt_id' w).sub_const w).fun_mul (hF' w).hasDerivAt))
  refine ⟨by simp, by rw [hd]; simp, ?_⟩
  rw [hd, hK.deriv]
  simp

/-- At every `w ∈ W`, the term of `D` with centre `y` is `(z - w)² F(z)` with `F` entire,
`F(w) = c_w / 2` if `y = w` and `F(w) = 0` otherwise. -/
theorem exists_term_eq (W : Finset ℝ) (c : ℝ → ℝ) (σ : ℝ) {w : ℝ} (hw : w ∈ W) (y : ℝ) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ z, (c y : ℂ) * gauss σ y z * interp W y z = (z - w) ^ 2 * F z) ∧
      F w = if y = w then (c y : ℂ) / 2 else 0 := by
  by_cases hyw : y = w
  · subst hyw
    refine ⟨fun z => (c y : ℂ) * (Complex.exp (-(z - y) ^ 2 / σ) / 2) * interp W y z, ?_, ?_, ?_⟩
    · have := differentiable_interp W y
      fun_prop
    · intro z
      simp only [gauss]
      ring
    · simp [interp_self, div_eq_mul_inv]
  · have hw' : w ∈ W.erase y := Finset.mem_erase.2 ⟨Ne.symm hyw, hw⟩
    refine ⟨fun z => (c y : ℂ) * gauss σ y z * ((z - w) * ((y : ℂ) - w)⁻¹ ^ 3 *
      ∏ v ∈ (W.erase y).erase w, ((z - v) / (y - v)) ^ 3), ?_, ?_, ?_⟩
    · have := differentiable_gauss σ y
      fun_prop
    · intro z
      rw [interp, ← Finset.mul_prod_erase _ _ hw']
      ring
    · simp [hyw]

/-- `D` and `D'` vanish on `W`; `D''(w) = c_w` for `w ∈ Y` and `D''(w) = 0` otherwise. -/
theorem pert_deriv_of_mem (W Y : Finset ℝ) (c : ℝ → ℝ) (σ : ℝ) {w : ℝ} (hw : w ∈ W) :
    pert W Y c σ w = 0 ∧ deriv (pert W Y c σ) w = 0 ∧
      deriv (deriv (pert W Y c σ)) w = if w ∈ Y then (c w : ℂ) else 0 := by
  choose F hF hFeq hFw using exists_term_eq W c σ hw
  have hD : pert W Y c σ = fun z => (z - w) ^ 2 * ∑ y ∈ Y, F y z := by
    funext z
    simp only [pert, Finset.mul_sum, hFeq]
  have hG : Differentiable ℂ fun z => ∑ y ∈ Y, F y z := by fun_prop
  obtain ⟨h0, h1, h2⟩ := sq_mul_deriv hG w
  rw [hD]
  refine ⟨h0, h1, ?_⟩
  rw [h2, Finset.sum_congr rfl fun y _ => hFw y, Finset.sum_ite_eq']
  split_ifs <;> ring

/-! ## Bounds -/

/-- `(t + 1) e^{-t} ≤ 1`. -/
theorem add_one_mul_exp_neg_le (t : ℝ) : (t + 1) * Real.exp (-t) ≤ 1 := by
  have h := Real.add_one_le_exp t
  have h2 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc (t + 1) * Real.exp (-t) ≤ Real.exp t * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = 1 := h2

/-- `t (t + 1) e^{-t} ≤ 2` for `t ≥ 0`. -/
theorem mul_add_one_mul_exp_neg_le {t : ℝ} (ht : 0 ≤ t) : t * (t + 1) * Real.exp (-t) ≤ 2 := by
  have h := Real.quadratic_le_exp_of_nonneg ht
  have h2 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc t * (t + 1) * Real.exp (-t) ≤ (2 * Real.exp t) * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_pos _).le
    _ = 2 := by rw [mul_assoc, h2, mul_one]

/-- For `|Im z|² ≤ σ` and `t = (Re z - y)²/σ`: `|G_{σ,y}(z)| ≤ (3/2) σ (t + 1) e^{-t}`. -/
theorem norm_gauss_le {σ : ℝ} (hσ : 0 < σ) (y : ℝ) {z : ℂ} (hz : z.im ^ 2 ≤ σ) :
    ‖gauss σ y z‖ ≤
      3 / 2 * σ * (((z.re - y) ^ 2 / σ + 1) * Real.exp (-((z.re - y) ^ 2 / σ))) := by
  set a := z.re - y with ha
  set b := z.im with hb
  have hn : ‖(z - y : ℂ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    ring
  have hre : (-(z - y) ^ 2 / (σ : ℂ)).re = -(a ^ 2 / σ) + b ^ 2 / σ := by
    rw [Complex.div_ofReal_re, Complex.neg_re, sq, Complex.mul_re, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    ring
  have he : Real.exp (b ^ 2 / σ) ≤ 3 := by
    calc Real.exp (b ^ 2 / σ) ≤ Real.exp 1 := Real.exp_le_exp.2 ((div_le_one hσ).2 hz)
      _ ≤ 3 := by have := Real.exp_one_lt_d9; norm_num at this; linarith
  calc ‖gauss σ y z‖ = (a ^ 2 + b ^ 2) * (Real.exp (-(a ^ 2 / σ)) * Real.exp (b ^ 2 / σ)) / 2 := by
        rw [gauss, norm_div, norm_mul, norm_pow, Complex.norm_exp, hre, hn, Real.exp_add]
        norm_num
    _ ≤ (a ^ 2 + σ) * (Real.exp (-(a ^ 2 / σ)) * 3) / 2 := by gcongr
    _ = 3 / 2 * σ * ((a ^ 2 / σ + 1) * Real.exp (-(a ^ 2 / σ))) := by
        field_simp

/-- Near its centre, `|G_{σ,y}(z)| ≤ (3/2) σ` for `|Im z|² ≤ σ`. -/
theorem norm_gauss_le_near {σ : ℝ} (hσ : 0 < σ) (y : ℝ) {z : ℂ} (hz : z.im ^ 2 ≤ σ) :
    ‖gauss σ y z‖ ≤ 3 / 2 * σ :=
  (norm_gauss_le hσ y hz).trans
    (mul_le_of_le_one_right (by positivity) (add_one_mul_exp_neg_le _))

/-- Away from its centre, `|G_{σ,y}(z)| (Re z - y)² ≤ 3 σ²` for `|Im z|² ≤ σ`. -/
theorem norm_gauss_mul_sq_le {σ : ℝ} (hσ : 0 < σ) (y : ℝ) {z : ℂ} (hz : z.im ^ 2 ≤ σ) :
    ‖gauss σ y z‖ * (z.re - y) ^ 2 ≤ 3 * σ ^ 2 := by
  have h1 := norm_gauss_le hσ y hz
  set t := (z.re - y) ^ 2 / σ with ht
  have ht0 : 0 ≤ t := by positivity
  have ha : (z.re - y) ^ 2 = σ * t := by rw [ht]; field_simp
  have h2 := mul_add_one_mul_exp_neg_le ht0
  calc ‖gauss σ y z‖ * (z.re - y) ^ 2
      ≤ 3 / 2 * σ * ((t + 1) * Real.exp (-t)) * (σ * t) := by
        rw [ha]
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 3 / 2 * σ ^ 2 * (t * (t + 1) * Real.exp (-t)) := by ring
    _ ≤ 3 / 2 * σ ^ 2 * 2 := by gcongr
    _ = 3 * σ ^ 2 := by ring

/-- On a circle of radius `r` about a point of `I`, `|D| ≤ 4 δ r²` for `σ = r²`, once `r` is small
compared with the separation `ρ` of `Y` and with the bounds for the `P_y`. -/
theorem norm_pert_le {W Y : Finset ℝ} {c : ℝ → ℝ} {δ ρ Q r : ℝ} (hδ : 0 ≤ δ)
    (hc : ∀ y ∈ Y, |c y| ≤ δ) (hρ : 0 < ρ) (hQ0 : 0 ≤ Q)
    (hsep : ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → ρ ≤ |a - b|)
    (hnear : ∀ y ∈ Y, ∀ z : ℂ, ‖z - y‖ < ρ → ‖interp W y z‖ ≤ 2)
    (hQ : ∀ y ∈ Y, ∀ z : ℂ, ‖z‖ ≤ 2 → ‖interp W y z‖ ≤ Q)
    (hr : 0 < r) (hr1 : r ≤ 1) (hrρ : 4 * r ≤ ρ) (hrQ : 48 * Y.card * Q * r ^ 2 ≤ ρ ^ 2)
    {x : ℝ} (hx : x ∈ I) {z : ℂ} (hz : z ∈ sphere (x : ℂ) r) :
    ‖pert W Y c (r ^ 2) z‖ ≤ 4 * δ * r ^ 2 := by
  have hzx : ‖z - x‖ = r := mem_sphere_iff_norm.1 hz
  have hσ : 0 < r ^ 2 := by positivity
  have him : z.im ^ 2 ≤ r ^ 2 := by
    have h : |z.im| ≤ r := by
      have := Complex.abs_im_le_norm (z - x)
      rwa [hzx, Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hre : |z.re - x| ≤ r := by
    have := Complex.abs_re_le_norm (z - x)
    rwa [hzx, Complex.sub_re, Complex.ofReal_re] at this
  have hnorm : ‖z‖ ≤ 2 := by
    have h1 : ‖(x : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hx.1, hx.2]
    calc ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - x‖ + ‖(x : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 := by rw [hzx]; linarith
  set T : ℝ → ℝ := fun y => ‖(c y : ℂ) * gauss (r ^ 2) y z * interp W y z‖ with hT
  have hTeq : ∀ y, T y = |c y| * ‖gauss (r ^ 2) y z‖ * ‖interp W y z‖ := fun y => by
    simp only [hT, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  -- The term of a centre within `ρ / 2` of `x`.
  have hnearT : ∀ y ∈ Y.filter fun y => |x - y| < ρ / 2, T y ≤ 3 * δ * r ^ 2 := by
    intro y hy
    obtain ⟨hyY, hxy⟩ := Finset.mem_filter.1 hy
    have hzy : ‖z - y‖ < ρ := by
      calc ‖z - y‖ = ‖(z - x) + ((x : ℂ) - y)‖ := by ring_nf
        _ ≤ ‖z - x‖ + ‖(x : ℂ) - y‖ := norm_add_le _ _
        _ = r + |x - y| := by
            rw [hzx, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        _ < ρ := by linarith
    rw [hTeq]
    calc |c y| * ‖gauss (r ^ 2) y z‖ * ‖interp W y z‖ ≤ δ * (3 / 2 * r ^ 2) * 2 := by
          gcongr
          exacts [hc y hyY, norm_gauss_le_near hσ y him, hnear y hyY z hzy]
      _ = 3 * δ * r ^ 2 := by ring
  -- The terms of the other centres.
  have hfarT : ∀ y ∈ Y.filter fun y => ¬ |x - y| < ρ / 2,
      T y ≤ 48 * δ * Q * r ^ 4 / ρ ^ 2 := by
    intro y hy
    obtain ⟨hyY, hxy⟩ := Finset.mem_filter.1 hy
    replace hxy := not_lt.1 hxy
    have ha : ρ / 4 ≤ |z.re - y| := by
      have := abs_sub_le x z.re y
      rw [abs_sub_comm x z.re] at this
      linarith
    have ha2 : ρ ^ 2 ≤ 16 * (z.re - y) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) ha 2
      rw [sq_abs] at this
      linarith
    have hg := norm_gauss_mul_sq_le hσ y him
    have hg' : ‖gauss (r ^ 2) y z‖ ≤ 48 * r ^ 4 / ρ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      calc ‖gauss (r ^ 2) y z‖ * ρ ^ 2 ≤ ‖gauss (r ^ 2) y z‖ * (16 * (z.re - y) ^ 2) := by
            gcongr
        _ = 16 * (‖gauss (r ^ 2) y z‖ * (z.re - y) ^ 2) := by ring
        _ ≤ 16 * (3 * (r ^ 2) ^ 2) := by gcongr
        _ = 48 * r ^ 4 := by ring
    rw [hTeq]
    calc |c y| * ‖gauss (r ^ 2) y z‖ * ‖interp W y z‖ ≤ δ * (48 * r ^ 4 / ρ ^ 2) * Q := by
          gcongr
          exacts [hc y hyY, hQ y hyY z hnorm]
      _ = 48 * δ * Q * r ^ 4 / ρ ^ 2 := by ring
  -- At most one centre lies within `ρ / 2` of `x`.
  have hcard : (Y.filter fun y => |x - y| < ρ / 2).card ≤ 1 := by
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    obtain ⟨haY, hxa⟩ := Finset.mem_filter.1 ha
    obtain ⟨hbY, hxb⟩ := Finset.mem_filter.1 hb
    by_contra hab
    have h1 := hsep a haY b hbY hab
    have h2 : |a - b| < ρ := by
      calc |a - b| ≤ |a - x| + |x - b| := abs_sub_le a x b
        _ < ρ := by rw [abs_sub_comm a x]; linarith
    linarith
  have hsum : (Y.card : ℝ) * (48 * δ * Q * r ^ 4 / ρ ^ 2) ≤ δ * r ^ 2 := by
    have h1 : 48 * Y.card * Q * r ^ 2 / ρ ^ 2 ≤ 1 := (div_le_one (by positivity)).2 hrQ
    calc (Y.card : ℝ) * (48 * δ * Q * r ^ 4 / ρ ^ 2)
        = δ * r ^ 2 * (48 * Y.card * Q * r ^ 2 / ρ ^ 2) := by ring
      _ ≤ δ * r ^ 2 := mul_le_of_le_one_right (by positivity) h1
  calc ‖pert W Y c (r ^ 2) z‖ ≤ ∑ y ∈ Y, T y := norm_sum_le _ _
    _ = ∑ y ∈ Y with |x - y| < ρ / 2, T y + ∑ y ∈ Y with ¬ |x - y| < ρ / 2, T y :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ (Y.filter fun y => |x - y| < ρ / 2).card • (3 * δ * r ^ 2) +
          (Y.filter fun y => ¬ |x - y| < ρ / 2).card • (48 * δ * Q * r ^ 4 / ρ ^ 2) :=
        add_le_add (Finset.sum_le_card_nsmul _ _ _ hnearT) (Finset.sum_le_card_nsmul _ _ _ hfarT)
    _ ≤ 1 * (3 * δ * r ^ 2) + Y.card * (48 * δ * Q * r ^ 4 / ρ ^ 2) := by
        rw [nsmul_eq_mul, nsmul_eq_mul]
        gcongr
        · exact_mod_cast hcard
        · exact Finset.filter_subset _ _
    _ ≤ 4 * δ * r ^ 2 := by linarith

/-! ## Choice of the parameters -/

/-- Small radii separate the points of a finite set. -/
theorem eventually_sep (Y : Finset ℝ) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → ρ ≤ |a - b| := by
  refine (eventually_all_finset Y).2 fun a _ => (eventually_all_finset Y).2 fun b _ => ?_
  by_cases hab : a = b
  · exact Eventually.of_forall fun _ h => absurd hab h
  · have h : 0 < |a - b| := abs_pos.2 (sub_ne_zero.2 hab)
    filter_upwards [Ioo_mem_nhdsGT h] with ρ hρ _ using hρ.2.le

/-- Near its centre, `|P_y| ≤ 2`, uniformly over finitely many centres. -/
theorem eventually_interp_near (W Y : Finset ℝ) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ y ∈ Y, ∀ z : ℂ, ‖z - y‖ < ρ → ‖interp W y z‖ ≤ 2 := by
  refine (eventually_all_finset Y).2 fun y _ => ?_
  obtain ⟨ρ, hρ, h⟩ :=
    Metric.continuousAt_iff.1 (differentiable_interp W y).continuous.continuousAt 1 one_pos
  filter_upwards [Ioo_mem_nhdsGT hρ] with ρ' hρ' z hz
  have h1 := h (by rw [dist_eq_norm]; exact hz.trans hρ'.2)
  rw [interp_self, dist_eq_norm] at h1
  have h2 := norm_sub_norm_le (interp W y z) 1
  rw [norm_one] at h2
  linarith

/-- A common bound for the `P_y`, `y ∈ Y`, on the disc of radius `2`. -/
theorem exists_interp_bound (W Y : Finset ℝ) :
    ∃ Q, 0 ≤ Q ∧ ∀ y ∈ Y, ∀ z : ℂ, ‖z‖ ≤ 2 → ‖interp W y z‖ ≤ Q := by
  choose Q hQ using fun y => (isCompact_closedBall (0 : ℂ) 2).exists_bound_of_continuousOn
    (differentiable_interp W y).continuous.continuousOn
  refine ⟨∑ y ∈ Y, |Q y|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun y hy z hz => ?_⟩
  calc ‖interp W y z‖ ≤ Q y := hQ y z (mem_closedBall_zero_iff.2 hz)
    _ ≤ |Q y| := le_abs_self _
    _ ≤ ∑ y ∈ Y, |Q y| :=
        Finset.single_le_sum (f := fun y => |Q y|) (fun _ _ => abs_nonneg _) hy

/-- A continuous `g` with `g(0) = 0` is eventually below any `b > 0` near `0`. -/
theorem eventually_lt_of_zero {g : ℝ → ℝ} (hg : Continuous g) (h0 : g 0 = 0) {b : ℝ}
    (hb : 0 < b) : ∀ᶠ r in 𝓝 (0 : ℝ), g r < b :=
  (hg.tendsto 0).eventually (gt_mem_nhds (by rw [h0]; exact hb))

/-- The perturbation of Proposition 4.4 for coefficients `|c_y| ≤ δ`: an entire map, real on `ℝ`,
vanishing to first order on `Y ∪ Z`, with `D'' = 0` on `Z` and `D''(y) = c_y` on `Y`, and with
`|D|, |D'| < m` and `|D''| ≤ 8 δ` on `I`. -/
theorem exists_pert {Y Z : Finset ℝ} (hYZ : Disjoint Y Z) {c : ℝ → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : ∀ y ∈ Y, |c y| ≤ δ) {m : ℝ} (hm : 0 < m) :
    ∃ D : ℂ → ℂ, Differentiable ℂ D ∧ (∀ x : ℝ, (D x).im = 0) ∧
      (∀ w ∈ Y ∪ Z, D w = 0 ∧ deriv D w = 0) ∧ (∀ w ∈ Z, deriv (deriv D) w = 0) ∧
      (∀ y ∈ Y, deriv (deriv D) y = c y) ∧ (∀ x ∈ I, ‖D x‖ < m) ∧
      (∀ x ∈ I, ‖deriv D x‖ < m) ∧ ∀ x ∈ I, ‖deriv (deriv D) x‖ ≤ 8 * δ := by
  obtain ⟨ρ, ⟨hsep, hnear⟩, hρ⟩ :=
    (((eventually_sep Y).and (eventually_interp_near (Y ∪ Z) Y)).and self_mem_nhdsWithin).exists
  have hρ : 0 < ρ := hρ
  obtain ⟨Q, hQ0, hQ⟩ := exists_interp_bound (Y ∪ Z) Y
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ),
      r < 1 ∧ 4 * r < ρ ∧ 48 * Y.card * Q * r ^ 2 < ρ ^ 2 ∧ 4 * δ * r < m :=
    (eventually_lt_nhds one_pos).and <|
      (eventually_lt_of_zero (by fun_prop) (by simp) hρ).and <|
      (eventually_lt_of_zero (by fun_prop) (by simp) (by positivity)).and
      (eventually_lt_of_zero (by fun_prop) (by simp) hm)
  obtain ⟨r, ⟨hr1, hrρ, hrQ, hrm⟩, hr⟩ :=
    ((hev.filter_mono (nhdsWithin_le_nhds (s := Ioi 0))).and
      (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
  have hr : 0 < r := hr
  have hD := differentiable_pert (Y ∪ Z) Y c (r ^ 2)
  have hcauchy : ∀ k, ∀ x ∈ I, ‖iteratedDeriv k (pert (Y ∪ Z) Y c (r ^ 2)) x‖ ≤
      k.factorial * (4 * δ * r ^ 2) / r ^ k :=
    fun k x hx => Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr
      hD.diffContOnCl fun z hz =>
        norm_pert_le hδ hc hρ hQ0 hsep hnear hQ hr hr1.le hrρ.le hrQ.le hx hz
  refine ⟨pert (Y ∪ Z) Y c (r ^ 2), hD, im_pert_ofReal _ _ _ _, fun w hw => ?_, fun w hw => ?_,
    fun y hy => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · exact ⟨(pert_deriv_of_mem _ Y c _ hw).1, (pert_deriv_of_mem _ Y c _ hw).2.1⟩
  · rw [(pert_deriv_of_mem _ Y c _ (Finset.mem_union_right _ hw)).2.2,
      ite_eq_right (Finset.disjoint_right.1 hYZ hw)]
  · rw [(pert_deriv_of_mem _ Y c _ (Finset.mem_union_left _ hy)).2.2, ite_eq_left hy]
  · have h := hcauchy 0 x hx
    simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero,
      div_one] at h
    calc _ ≤ 4 * δ * r ^ 2 := h
      _ ≤ 4 * δ * r := by nlinarith [mul_nonneg (mul_nonneg hδ hr.le) (sub_nonneg.2 hr1.le)]
      _ < m := hrm
  · have h := hcauchy 1 x hx
    simp only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul, pow_one] at h
    calc _ ≤ 4 * δ * r ^ 2 / r := h
      _ = 4 * δ * r := by field_simp
      _ < m := hrm
  · have h := hcauchy 2 x hx
    rw [iteratedDeriv_succ, iteratedDeriv_one] at h
    calc _ ≤ (Nat.factorial 2 : ℝ) * (4 * δ * r ^ 2) / r ^ 2 := h
      _ = 8 * δ := by rw [Nat.factorial_two]; field_simp; ring

/-! ## Proof of Proposition 4.4 -/

/-- `(f + D)' = f' + D'` and `(f + D)'' = f'' + D''` at the points of an open set on which `f` is
holomorphic, for `D` entire. -/
theorem deriv_add_of_differentiable {U : Set ℂ} (hU : IsOpen U) {f D : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hD : Differentiable ℂ D) {z : ℂ} (hz : z ∈ U) :
    deriv (fun w => f w + D w) z = deriv f z + deriv D z ∧
      deriv (deriv fun w => f w + D w) z = deriv (deriv f) z + deriv (deriv D) z := by
  have h1 : ∀ w ∈ U, deriv (fun w => f w + D w) w = deriv f w + deriv D w := fun w hw =>
    deriv_add (hf.differentiableAt (hU.mem_nhds hw)) (hD w)
  refine ⟨h1 z hz, ?_⟩
  have heq : deriv (fun w => f w + D w) =ᶠ[𝓝 z] fun w => deriv f w + deriv D w :=
    Filter.eventually_of_mem (hU.mem_nhds hz) h1
  rw [heq.deriv_eq]
  exact deriv_add ((hf.deriv hU).differentiableAt (hU.mem_nhds hz))
    (differentiable_deriv hD z)

/-- A margin `m > 0` with `m ≤ f ≤ 1 - m` and `m ≤ |f'| ≤ 1 - m` on `I`. -/
theorem exists_margin {ε : ℝ} (hε : 0 < ε) {f : ℂ → ℂ} (hf : InClass ε f)
    (hI : ∀ x ∈ I, (f x).re ∈ Ioo 0 1) :
    ∃ m > 0, ∀ x ∈ I,
      m ≤ (f x).re ∧ (f x).re ≤ 1 - m ∧ m ≤ ‖deriv f x‖ ∧ ‖deriv f x‖ ≤ 1 - m := by
  have hmem : MapsTo ((↑) : ℝ → ℂ) I (nbhd (2 * ε)) := fun x hx =>
    ofReal_mem_nbhd (by positivity) hx
  have hf0 : ContinuousOn (fun x : ℝ => (f x).re) I :=
    Complex.continuous_re.comp_continuousOn
      (hf.differentiableOn.continuousOn.comp Complex.continuous_ofReal.continuousOn hmem)
  have hf1 : ContinuousOn (fun x : ℝ => ‖deriv f x‖) I :=
    ((hf.differentiableOn.deriv (isOpen_nbhd _)).continuousOn.comp
      Complex.continuous_ofReal.continuousOn hmem).norm
  set h : ℝ → ℝ := fun x =>
    min (min (f x).re (1 - (f x).re)) (min ‖deriv f x‖ (1 - ‖deriv f x‖)) with hh
  have hcont : ContinuousOn h I :=
    (hf0.inf (continuousOn_const.sub hf0)).inf (hf1.inf (continuousOn_const.sub hf1))
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, by norm_num⟩ hcont
  have hpos : ∀ x ∈ I, 0 < h x := fun x hx => by
    have hcl : (x : ℂ) ∈ closure (nbhd ε) := subset_closure (ofReal_mem_nbhd hε hx)
    have h1 := hI x hx
    have h2 := norm_pos_iff.2 (hf.deriv_ne_zero x hcl)
    have h3 := hf.norm_deriv_lt_one x hcl
    simp only [hh, lt_min_iff]
    exact ⟨⟨h1.1, by linarith [h1.2]⟩, h2, by linarith⟩
  refine ⟨h x₀, hpos x₀ hx₀, fun x hx => ?_⟩
  have h1 : h x₀ ≤ h x := isMinOn_iff.1 hmin x hx
  simp only [hh, le_min_iff] at h1 ⊢
  exact ⟨h1.1.1, by linarith [h1.1.2], h1.2.1, by linarith [h1.2.2]⟩

end Bump

/-- Proposition 4.4. Let `f ∈ S^ω(I)` with `f([0,1]) ⊆ (0,1)`. There is `C > 0` such that for all
finite disjoint `𝒴, 𝒵 ⊆ [0,1]`, `η > 0` and `δ > 0` there is `g ∈ S^ω(I)` with `g = f` and
`g' = f'` on `𝒴 ∪ 𝒵`, `g'' = f''` on `𝒵`, `|g''/g' - f''/f'| ≥ δ` on `𝒴`, `|g - f| < η` and
`|g' - f'| < η` on `[0,1]`, and `|g'' - f''| < C δ + η` on `[0,1]`. The paper writes `ε` for `η`. -/
theorem proposition_4_4 {ε : ℝ} (hε : 0 < ε) {f : ℂ → ℂ} (hf : InClass ε f)
    (hI : ∀ x ∈ I, (f x).re ∈ Ioo 0 1) :
    ∃ C > 0, ∀ Y Z : Finset ℝ, (∀ y ∈ Y, y ∈ I) → (∀ z ∈ Z, z ∈ I) → Disjoint Y Z →
      ∀ η > 0, ∀ δ > 0, ∃ g : ℂ → ℂ, (∃ ε' > 0, InClass ε' g) ∧
        (∀ y ∈ Y ∪ Z, g y = f y ∧ deriv g y = deriv f y) ∧
        (∀ z ∈ Z, deriv (deriv g) z = deriv (deriv f) z) ∧
        (∀ y ∈ Y, δ ≤ ‖deriv (deriv g) y / deriv g y - deriv (deriv f) y / deriv f y‖) ∧
        (∀ x ∈ I, ‖g x - f x‖ < η) ∧ (∀ x ∈ I, ‖deriv g x - deriv f x‖ < η) ∧
        (∀ x ∈ I, ‖deriv (deriv g) x - deriv (deriv f) x‖ < C * δ + η) := by
  obtain ⟨m₀, hm₀, hmar⟩ := Bump.exists_margin hε hf hI
  refine ⟨8, by norm_num, fun Y Z hY hZ hYZ η hη δ hδ => ?_⟩
  have h2ε : 0 < 2 * ε := by positivity
  have hmem : ∀ x ∈ I, (x : ℂ) ∈ nbhd (2 * ε) := fun x hx => ofReal_mem_nbhd h2ε hx
  have hcl : ∀ x ∈ I, (x : ℂ) ∈ closure (nbhd ε) := fun x hx =>
    subset_closure (ofReal_mem_nbhd hε hx)
  have hWI : ∀ w ∈ Y ∪ Z, w ∈ I := fun w hw => (Finset.mem_union.1 hw).elim (hY w) (hZ w)
  -- `f'` is real on `I`.
  have hreal : ∀ x ∈ I, (((deriv f x).re : ℝ) : ℂ) = deriv f x := fun x hx =>
    Complex.ext (by simp) (by
      simp [im_deriv_eq_zero (isOpen_nbhd _) hf.differentiableOn hf.im_eq_zero (hmem x hx)])
  -- The coefficients `c_y = δ f'(y)`.
  have hc : ∀ y ∈ Y, |δ * (deriv f y).re| ≤ δ := fun y hy => by
    rw [abs_mul, abs_of_pos hδ]
    exact mul_le_of_le_one_right hδ.le
      ((Complex.abs_re_le_norm _).trans (hf.norm_deriv_lt_one _ (hcl y (hY y hy))).le)
  obtain ⟨D, hD, hDre, hDW, hDZ, hDY, hD0, hD1, hD2⟩ :=
    Bump.exists_pert hYZ hδ.le hc (lt_min hη hm₀)
  have hderiv := fun x hx =>
    Bump.deriv_add_of_differentiable (isOpen_nbhd _) hf.differentiableOn hD (hmem x hx)
  refine ⟨fun z => f z + D z, ?_, fun w hw => ?_, fun w hw => ?_, fun y hy => ?_,
    fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · -- `g = f + D` lies in `S^ω(I)` by Lemma 4.1.
    refine exists_inClass (isOpen_nbhd (2 * ε)) ?_ (hf.differentiableOn.add hD.differentiableOn)
      (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
    · rintro _ ⟨x, hx, rfl⟩
      exact hmem x hx
    · simp [hf.im_eq_zero x hx, hDre x]
    · obtain ⟨h1, h2, -, -⟩ := hmar x hx
      have h3 := (Complex.abs_re_le_norm (D x)).trans_lt ((hD0 x hx).trans_le (min_le_right _ _))
      rw [abs_lt] at h3
      show (f x + D x).re ∈ I
      rw [Complex.add_re]
      constructor <;> linarith
    · obtain ⟨-, -, h1, -⟩ := hmar x hx
      have h2 := (hD1 x hx).trans_le (min_le_right _ _)
      rw [(hderiv x hx).1]
      intro h
      rw [eq_neg_iff_add_eq_zero.2 h, norm_neg] at h1
      linarith
    · obtain ⟨-, -, -, h1⟩ := hmar x hx
      have h2 := (hD1 x hx).trans_le (min_le_right _ _)
      rw [(hderiv x hx).1]
      linarith [norm_add_le (deriv f x) (deriv D x)]
  · obtain ⟨h0, h1⟩ := hDW w hw
    refine ⟨by simp [h0], ?_⟩
    rw [(hderiv w (hWI w hw)).1, h1, add_zero]
  · rw [(hderiv w (hZ w hw)).2, hDZ w hw, add_zero]
  · have hyI := hY y hy
    have hne := hf.deriv_ne_zero _ (hcl y hyI)
    rw [(hderiv y hyI).2, (hderiv y hyI).1, hDY y hy, (hDW y (Finset.mem_union_left _ hy)).2,
      add_zero, add_div, add_sub_cancel_left, Complex.ofReal_mul, hreal y hyI, mul_div_assoc,
      div_self hne, mul_one, Complex.norm_real, Real.norm_of_nonneg hδ.le]
  · show ‖f x + D x - f x‖ < η
    rw [add_sub_cancel_left]
    exact (hD0 x hx).trans_le (min_le_left _ _)
  · rw [(hderiv x hx).1, add_sub_cancel_left]
    exact (hD1 x hx).trans_le (min_le_left _ _)
  · rw [(hderiv x hx).2, add_sub_cancel_left]
    exact (hD2 x hx).trans_lt (by linarith)

end AnalyticESC
