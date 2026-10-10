module

public import AnalyticESC.Main.Criterion
public import AnalyticESC.Generic.Class

@[expose] public section

/-!
# The non-polynomial example of Section 1.2.2

The maps `(1 - exp(-x/2))/4`, `(sqrt(1+x) - 1)/4` and `x/6 + 5/6` satisfy the
SESC by Proposition 1.8, with separation at `x = 1`. The square root is the principal complex
branch, holomorphic on the neighbourhood `Re z > -1` of the unit interval.
-/

namespace AnalyticESC

open Set Metric Filter Topology
open ComplexOrder

noncomputable def nonPolynomialMaps : Fin 3 → ℂ → ℂ :=
  ![fun z => (1 - Complex.exp (-z / 2)) / 4,
    fun z => (Complex.sqrt (1 + z) - 1) / 4, fun z => z / 6 + 5 / 6]

private theorem fin_three (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by omega

private def exampleDomain : Set ℂ := {z | -1 < z.re}

private theorem exampleDomain_open : IsOpen exampleDomain :=
  isOpen_lt continuous_const Complex.continuous_re

private theorem exampleDomain_real {x : ℝ} (hx : x ∈ I) : (x : ℂ) ∈ exampleDomain := by
  change -1 < x
  linarith [hx.1]

private theorem sqrt_ne_zero {z : ℂ} (hz : z ∈ exampleDomain) : Complex.sqrt (1 + z) ≠ 0 := by
  have hsq : Complex.sqrt (1 + z) ^ 2 = 1 + z := Complex.cpow_nat_inv_pow _ (by norm_num)
  intro h
  rw [h, zero_pow (by decide)] at hsq
  have := congrArg Complex.re hsq
  simp only [Complex.zero_re, Complex.add_re, Complex.one_re] at this
  change -1 < z.re at hz
  linarith

private theorem sqrt_hasDerivAt {z : ℂ} (hz : z ∈ exampleDomain) :
    HasDerivAt (fun z : ℂ => Complex.sqrt (1 + z)) (1 / (2 * Complex.sqrt (1 + z))) z := by
  have hs : 1 + z ∈ Complex.slitPlane := Or.inl (by
    simp only [Complex.add_re, Complex.one_re]
    change -1 < z.re at hz
    linarith)
  have hd := (Complex.differentiableAt_sqrt hs).comp z (differentiableAt_const _ |>.add differentiableAt_id)
  have hsq : (fun z : ℂ => Complex.sqrt (1 + z) ^ 2) = fun z => 1 + z := by
    funext z
    exact Complex.cpow_nat_inv_pow _ (by norm_num)
  have h := hd.hasDerivAt.pow 2
  change HasDerivAt (fun z : ℂ => Complex.sqrt (1 + z) ^ 2) _ z at h
  rw [hsq] at h
  have he := h.unique ((hasDerivAt_id z).const_add 1)
  have hn := sqrt_ne_zero hz
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Function.comp_apply] at he
  apply hd.hasDerivAt.congr_deriv
  apply (eq_div_iff (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hn)).mpr
  linear_combination he

private theorem exp_hasDerivAt (z : ℂ) :
    HasDerivAt (nonPolynomialMaps 0) (Complex.exp (-z / 2) / 8) z := by
  have h := (((hasDerivAt_id z).neg.div_const 2).cexp.const_sub 1).div_const 4
  convert h using 1 <;> simp [nonPolynomialMaps]
  ring

private theorem root_hasDerivAt {z : ℂ} (hz : z ∈ exampleDomain) :
    HasDerivAt (nonPolynomialMaps 1) (1 / (8 * Complex.sqrt (1 + z))) z := by
  convert ((sqrt_hasDerivAt hz).sub_const 1).div_const 4 using 1 <;>
    simp [nonPolynomialMaps]
  ring

private theorem affine_hasDerivAt (z : ℂ) :
    HasDerivAt (nonPolynomialMaps 2) (1 / 6) z := by
  exact ((hasDerivAt_id z).div_const 6).add_const (5 / 6)

private theorem exp_ofReal (x : ℝ) :
    nonPolynomialMaps 0 x = (((1 - Real.exp (-x / 2)) / 4 : ℝ) : ℂ) := by
  simp only [nonPolynomialMaps, Matrix.cons_val_zero]
  push_cast
  rfl

private theorem sqrt_ofReal {x : ℝ} (hx : -1 < x) :
    Complex.sqrt (1 + (x : ℂ)) = (Real.sqrt (1 + x) : ℂ) := by
  have h : (0 : ℂ) ≤ 1 + (x : ℂ) := by
    exact RCLike.nonneg_iff_exists_ofReal.mpr ⟨1 + x, by linarith, by push_cast; rfl⟩
  simpa using Complex.sqrt_of_nonneg h

private theorem root_ofReal {x : ℝ} (hx : -1 < x) :
    nonPolynomialMaps 1 x = (((Real.sqrt (1 + x) - 1) / 4 : ℝ) : ℂ) := by
  simp only [nonPolynomialMaps, Matrix.cons_val_one, Matrix.cons_val_zero, sqrt_ofReal hx]
  push_cast
  rfl

private theorem maps_differentiableOn (i : Fin 3) :
    DifferentiableOn ℂ (nonPolynomialMaps i) exampleDomain := by
  intro z hz
  rcases fin_three i with rfl | rfl | rfl
  · exact (exp_hasDerivAt z).differentiableAt.differentiableWithinAt
  · exact (root_hasDerivAt hz).differentiableAt.differentiableWithinAt
  · exact (affine_hasDerivAt z).differentiableAt.differentiableWithinAt

private theorem maps_real (i : Fin 3) (x : ℝ) (hx : (x : ℂ) ∈ exampleDomain) :
    (nonPolynomialMaps i x).im = 0 := by
  rcases fin_three i with rfl | rfl | rfl
  · rw [exp_ofReal, Complex.ofReal_im]
  · rw [root_ofReal (show -1 < x from hx), Complex.ofReal_im]
  · simp [nonPolynomialMaps]

private theorem maps_mem_I (i : Fin 3) (x : ℝ) (hx : x ∈ I) :
    (nonPolynomialMaps i x).re ∈ I := by
  have hx0 := hx.1
  have hx1 := hx.2
  rcases fin_three i with rfl | rfl | rfl
  · rw [exp_ofReal, Complex.ofReal_re]
    have he0 := Real.exp_pos (-x / 2)
    have he1 := Real.exp_le_one_iff.mpr (by linarith : -x / 2 ≤ 0)
    constructor <;> linarith
  · rw [root_ofReal (by linarith), Complex.ofReal_re]
    have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 + x)
    have hs0 := Real.sqrt_nonneg (1 + x)
    constructor <;> nlinarith
  · change ((x : ℂ) / 6 + 5 / 6).re ∈ I
    norm_num [Complex.add_re, Complex.div_ofNat_re]
    constructor <;> linarith

private theorem maps_deriv_real (i : Fin 3) (x : ℝ) (hx : x ∈ I) :
    deriv (nonPolynomialMaps i) x =
      ((![Real.exp (-x / 2) / 8, 1 / (8 * Real.sqrt (1 + x)), 1 / 6] i : ℝ) : ℂ) := by
  rcases fin_three i with rfl | rfl | rfl
  · rw [(exp_hasDerivAt _).deriv]
    simp only [Matrix.cons_val_zero]
    push_cast
    rfl
  · rw [(root_hasDerivAt (exampleDomain_real hx)).deriv, sqrt_ofReal (by linarith [hx.1])]
    simp
  · rw [(affine_hasDerivAt _).deriv]
    simp

private theorem maps_deriv_bounds (i : Fin 3) (x : ℝ) (hx : x ∈ I) :
    deriv (nonPolynomialMaps i) x ≠ 0 ∧ ‖deriv (nonPolynomialMaps i) x‖ ≤ 1 / 6 := by
  rw [maps_deriv_real i x hx]
  have he0 := Real.exp_pos (-x / 2)
  have he1 := Real.exp_le_one_iff.mpr (by linarith [hx.1] : -x / 2 ≤ 0)
  have hs0 := Real.sqrt_pos.mpr (by linarith [hx.1] : 0 < 1 + x)
  have hs1 : 1 ≤ Real.sqrt (1 + x) := by
    nlinarith [hx.1, Real.sq_sqrt (by linarith [hx.1] : 0 ≤ 1 + x)]
  rcases fin_three i with rfl | rfl | rfl <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · constructor
    · exact_mod_cast ne_of_gt (div_pos he0 (by norm_num : (0 : ℝ) < 8))
    · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
  · constructor
    · exact_mod_cast ne_of_gt (one_div_pos.mpr (mul_pos (by norm_num : (0 : ℝ) < 8) hs0))
    · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      apply (div_le_iff₀ (by positivity : 0 < 8 * Real.sqrt (1 + x))).mpr
      linarith
  · norm_num

/-- The non-polynomial maps lie in a common admissible class. -/
theorem nonPolynomialMaps_inClass : ∃ ε > 0, ∀ i, InClass ε (nonPolynomialMaps i) := by
  apply exists_inClass_forall
  intro i
  apply exists_inClass exampleDomain_open
    (by rintro _ ⟨x, hx, rfl⟩; exact exampleDomain_real hx)
    (maps_differentiableOn i) (maps_real i) (maps_mem_I i)
    (fun x hx => (maps_deriv_bounds i x hx).1)
  intro x hx
  exact (maps_deriv_bounds i x hx).2.trans_lt (by norm_num)

/-- An admissible radius can be chosen so that the complex derivative bound is below `1/5`. -/
theorem nonPolynomialMaps_exists_cmax_lt :
    ∃ ε > 0, ∃ Φ : IFS 3 ε, Φ.f = nonPolynomialMaps ∧ Φ.cmax < 1 / 5 := by
  obtain ⟨ε, hε, hf⟩ := nonPolynomialMaps_inClass
  let Φ : IFS 3 ε := ⟨nonPolynomialMaps, hε, hf⟩
  let V : Set ℂ := ⋂ i : Fin 3, nbhd (2 * ε) ∩
    (fun z => ‖deriv (nonPolynomialMaps i) z‖) ⁻¹' Iio (11 / 60)
  have hV : IsOpen V := isOpen_iInter_of_finite fun i =>
    (((hf i).differentiableOn.deriv (isOpen_nbhd _)).continuousOn.norm).isOpen_inter_preimage
      (isOpen_nbhd _) isOpen_Iio
  have hIV : ((↑) : ℝ → ℂ) '' I ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    apply mem_iInter.mpr
    intro i
    exact ⟨ofReal_mem_nbhd (by linarith) hx,
      (maps_deriv_bounds i x hx).2.trans_lt (by norm_num)⟩
  obtain ⟨δ, hδ, hδV⟩ := isCompact_image_I.exists_cthickening_subset_open hV hIV
  let ρ := min ε δ
  have hρ : 0 < ρ := lt_min hε hδ
  let Ψ := Φ.restrict hρ (min_le_left ε δ)
  refine ⟨ρ, hρ, Ψ, rfl, ?_⟩
  have hbound : Ψ.cmax ≤ 11 / 60 := by
    have : Nonempty (closure (nbhd ρ)) := ⟨⟨0, zero_mem_closure_nbhd hρ⟩⟩
    apply ciSup_le
    intro i
    apply ciSup_le
    intro z
    have hz := hδV (cthickening_mono (min_le_right ε δ) _
      (closure_thickening_subset_cthickening ρ _ z.2))
    exact (mem_iInter.mp hz i).2.le
  linarith

private theorem exp_second (z : ℂ) :
    deriv (deriv (nonPolynomialMaps 0)) z = -Complex.exp (-z / 2) / 16 := by
  have he : deriv (nonPolynomialMaps 0) = fun z => Complex.exp (-z / 2) / 8 :=
    funext fun z => (exp_hasDerivAt z).deriv
  rw [he]
  convert ((((hasDerivAt_id z).neg.div_const 2).cexp).div_const 8).deriv using 1 <;>
    simp only [Pi.neg_apply, id_eq]
  ring

private theorem root_second {z : ℂ} (hz : z ∈ exampleDomain) :
    deriv (deriv (nonPolynomialMaps 1)) z = -1 / (16 * Complex.sqrt (1 + z) ^ 3) := by
  have hn := sqrt_ne_zero hz
  have he : deriv (nonPolynomialMaps 1) =ᶠ[𝓝 z]
      (fun z => 1 / (8 * Complex.sqrt (1 + z))) := by
    filter_upwards [exampleDomain_open.mem_nhds hz] with w hw
    exact (root_hasDerivAt hw).deriv
  rw [he.deriv_eq]
  have hd := (hasDerivAt_const z (1 : ℂ)).fun_div ((sqrt_hasDerivAt hz).const_mul 8)
    (mul_ne_zero (by norm_num) hn)
  rw [hd.deriv]
  field_simp
  ring

/-- The pre-Schwarzian derivatives of the three maps on `I`. -/
theorem nonPolynomialMaps_nonlin (i : Fin 3) (x : ℝ) (hx : x ∈ I) :
    deriv (deriv (nonPolynomialMaps i)) x / deriv (nonPolynomialMaps i) x =
      (![(-1 / 2 : ℝ), -1 / (2 * (1 + x)), 0] i : ℂ) := by
  rcases fin_three i with rfl | rfl | rfl
  · rw [exp_second, (exp_hasDerivAt _).deriv]
    simp only [Matrix.cons_val_zero]
    push_cast
    field_simp [Complex.exp_ne_zero]
    ring
  · rw [root_second (exampleDomain_real hx), (root_hasDerivAt (exampleDomain_real hx)).deriv]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    push_cast
    have hn := sqrt_ne_zero (exampleDomain_real hx)
    have hs : Complex.sqrt (1 + (x : ℂ)) ^ 2 = 1 + x :=
      Complex.cpow_nat_inv_pow _ (by norm_num)
    have hx' : 1 + (x : ℂ) ≠ 0 := by
      have : (0 : ℝ) < 1 + x := by linarith [hx.1]
      exact_mod_cast this.ne'
    field_simp
    linear_combination 16 * hs
  · have he : deriv (nonPolynomialMaps 2) = fun _ => 1 / 6 :=
      funext fun z => (affine_hasDerivAt z).deriv
    rw [he, deriv_const]
    simp

/-- The uniform distortion bound used in the manuscript's criterion. -/
theorem nonPolynomialMaps_beta_le {ε : ℝ} (Φ : IFS 3 ε) (hf : Φ.f = nonPolynomialMaps) :
    Φ.beta ≤ 1 / 2 := by
  have : Nonempty I := ⟨⟨0, le_rfl, zero_le_one⟩⟩
  apply ciSup_le
  intro x
  apply ciSup_le
  intro i
  change ‖deriv (deriv (Φ.f i)) x / deriv (Φ.f i) x‖ ≤ _
  rw [hf, nonPolynomialMaps_nonlin i x x.2, Complex.norm_real]
  rcases fin_three i with rfl | rfl | rfl
  · norm_num
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [Real.norm_of_nonpos (by apply div_nonpos_of_nonpos_of_nonneg <;> linarith [x.2.1])]
    have hd : 0 < 2 * (1 + (x : ℝ)) := by linarith [x.2.1]
    rw [neg_div, neg_neg, div_le_iff₀ hd]
    linarith [x.2.1]
  · norm_num

/-- The manuscript's exact value `β = 1/2`. -/
theorem nonPolynomialMaps_beta_eq {ε : ℝ} (Φ : IFS 3 ε) (hf : Φ.f = nonPolynomialMaps) :
    Φ.beta = 1 / 2 := by
  apply le_antisymm (nonPolynomialMaps_beta_le Φ hf)
  have h := Φ.norm_nonlin_le_beta 0 (show (0 : ℝ) ∈ I from ⟨le_rfl, zero_le_one⟩)
  change ‖deriv (deriv (Φ.f 0)) (0 : ℝ) / deriv (Φ.f 0) (0 : ℝ)‖ ≤ Φ.beta at h
  rw [hf, nonPolynomialMaps_nonlin 0 0 ⟨le_rfl, zero_le_one⟩] at h
  norm_num at h ⊢
  exact h

/-- Distortions are separated at `x = 1`, with `α = 1/4`. -/
theorem nonPolynomialMaps_nonlin_sep {ε : ℝ} (Φ : IFS 3 ε)
    (hf : Φ.f = nonPolynomialMaps) (i j : Fin 3) (hij : i ≠ j) :
    (1 / 4 : ℝ) ≤ ‖Φ.nonlin i 1 - Φ.nonlin j 1‖ := by
  have he (k : Fin 3) : Φ.nonlin k 1 = (![(-1 / 2 : ℝ), -1 / 4, 0] k : ℂ) := by
    change deriv (deriv (Φ.f k)) 1 / deriv (Φ.f k) 1 = _
    rw [hf]
    convert nonPolynomialMaps_nonlin k 1 ⟨zero_le_one, le_rfl⟩ using 1
    norm_num
  rcases fin_three i with rfl | rfl | rfl <;>
    rcases fin_three j with rfl | rfl | rfl <;>
    first | exact absurd rfl hij | (rw [he, he]; norm_num)

/-- The non-polynomial example satisfies the SESC. -/
theorem nonPolynomial_sesc :
    ∃ ε > 0, ∃ Φ : IFS 3 ε, Φ.f = nonPolynomialMaps ∧ Φ.SESC := by
  obtain ⟨ε, hε, Φ, hf, hc⟩ := nonPolynomialMaps_exists_cmax_lt
  refine ⟨ε, hε, Φ, hf, ?_⟩
  have hsep : ∀ i j : Fin 3, i ≠ j →
      ∃ x ∈ I, (1 / 4 : ℝ) ≤ ‖Φ.nonlin i x - Φ.nonlin j x‖ := by
    intro i j hij
    exact ⟨1, ⟨zero_le_one, le_rfl⟩, by simpa using nonPolynomialMaps_nonlin_sep Φ hf i j hij⟩
  obtain ⟨hβ, h⟩ := Φ.proposition_1_8 (by norm_num) (by norm_num) hsep
  have hb := nonPolynomialMaps_beta_le Φ hf
  have hc0 := Φ.cmax_nonneg
  refine (h ?_).2
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- The fixed points stated in the example. -/
theorem nonPolynomialMaps_fixedPoints :
    nonPolynomialMaps 0 0 = 0 ∧ nonPolynomialMaps 1 0 = 0 ∧ nonPolynomialMaps 2 1 = 1 := by
  norm_num [nonPolynomialMaps, Complex.sqrt]

/-- The first two derivatives agree at their common fixed point. -/
theorem nonPolynomialMaps_deriv_zero :
    deriv (nonPolynomialMaps 0) 0 = 1 / 8 ∧ deriv (nonPolynomialMaps 1) 0 = 1 / 8 := by
  rw [(exp_hasDerivAt _).deriv, (root_hasDerivAt (by change -1 < (0 : ℂ).re; norm_num)).deriv]
  norm_num [Complex.sqrt]

/-- The two nonlinear maps also have the same pre-Schwarzian derivative at zero. -/
theorem nonPolynomialMaps_nonlin_zero :
    deriv (deriv (nonPolynomialMaps 0)) 0 / deriv (nonPolynomialMaps 0) 0 = -1 / 2 ∧
    deriv (deriv (nonPolynomialMaps 1)) 0 / deriv (nonPolynomialMaps 1) 0 = -1 / 2 := by
  have h0 := nonPolynomialMaps_nonlin 0 0 ⟨le_rfl, zero_le_one⟩
  have h1 := nonPolynomialMaps_nonlin 1 0 ⟨le_rfl, zero_le_one⟩
  norm_num at h0 h1 ⊢
  exact ⟨h0, h1⟩

/-- The maximum real derivative norm is exactly `1/6`, attained by the affine map. -/
theorem nonPolynomialMaps_max_deriv :
    (∀ i x, x ∈ I → ‖deriv (nonPolynomialMaps i) x‖ ≤ 1 / 6) ∧
    (∀ x : ℝ, ‖deriv (nonPolynomialMaps 2) x‖ = 1 / 6) := by
  refine ⟨fun i x hx => (maps_deriv_bounds i x hx).2, fun x => ?_⟩
  rw [(affine_hasDerivAt _).deriv]
  norm_num

end AnalyticESC
