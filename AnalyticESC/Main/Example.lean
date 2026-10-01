module

public import AnalyticESC.Main.Criterion

@[expose] public section

/-!
# The example of Section 1.2.2

The system `f₁(x) = x/8`, `f₂(x) = x/8 + x²/32`, `f₃(x) = x/16 + x²/32 + 29/32` lies in `𝔖_3` for
`ε = 1/100`, has `c_max < 1/5`, `β ≤ 1` and distortions `1/2`-apart at `0`, so Proposition 1.8
shows that it satisfies the SESC.
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-- The maps of the example in Section 1.2.2. -/
noncomputable def exampleMaps : Fin 3 → ℂ → ℂ :=
  ![fun z => z / 8, fun z => z / 8 + z ^ 2 / 32, fun z => z / 16 + z ^ 2 / 32 + 29 / 32]

/-! ### Points of `cl B_{1/100}` -/

/-- A point of `cl B_{1/100}` lies within `1/100` of a point of `I`. -/
private lemma example_exists_near {z : ℂ} (hz : z ∈ closure (nbhd (1 / 100))) :
    ∃ x ∈ I, ‖z - x‖ ≤ 1 / 100 := by
  have h := closure_thickening_subset_cthickening (1 / 100 : ℝ) (((↑) : ℝ → ℂ) '' I) hz
  rw [isCompact_image_I.cthickening_eq_biUnion_closedBall (by norm_num)] at h
  simp only [mem_iUnion, mem_closedBall, exists_prop] at h
  obtain ⟨_, ⟨x, hx, rfl⟩, hzx⟩ := h
  exact ⟨x, hx, by rwa [← dist_eq_norm]⟩

/-- A point within `1/100` of `I` has norm at most `101/100` and real part at least `-1/100`. -/
private lemma example_bounds_of_near {z : ℂ} {x : ℝ} (hx : x ∈ I) (hzx : ‖z - x‖ ≤ 1 / 100) :
    ‖z‖ ≤ 101 / 100 ∧ -(1 / 100) ≤ z.re := by
  have h1 := norm_sub_norm_le z x
  have h2 := Complex.abs_re_le_norm (z - x)
  rw [Complex.norm_real, Real.norm_of_nonneg hx.1] at h1
  rw [Complex.sub_re, Complex.ofReal_re] at h2
  constructor
  · linarith [hx.2]
  · linarith [neg_abs_le (z.re - x), hx.1]

private lemma example_bounds {z : ℂ} (hz : z ∈ closure (nbhd (1 / 100))) :
    ‖z‖ ≤ 101 / 100 ∧ -(1 / 100) ≤ z.re := by
  obtain ⟨x, hx, hzx⟩ := example_exists_near hz
  exact example_bounds_of_near hx hzx

/-- A map that is `1/5`-Lipschitz near `I` and sends `I` into `I` maps `cl B_{1/100}` into
`B_{1/100}`. -/
private lemma example_mapsTo {f : ℂ → ℂ} (hI : ∀ x ∈ I, ∃ y ∈ I, f x = y)
    (hf : ∀ z : ℂ, ∀ x ∈ I, ‖z - x‖ ≤ 1 / 100 → ‖f z - f x‖ ≤ 1 / 5 * ‖z - x‖) :
    MapsTo f (closure (nbhd (1 / 100))) (nbhd (1 / 100)) := by
  intro z hz
  obtain ⟨x, hx, hzx⟩ := example_exists_near hz
  obtain ⟨y, hy, hfy⟩ := hI x hx
  rw [nbhd, mem_thickening_iff]
  refine ⟨y, mem_image_of_mem _ hy, ?_⟩
  rw [dist_eq_norm, ← hfy]
  calc ‖f z - f x‖ ≤ 1 / 5 * ‖z - x‖ := hf z x hx hzx
    _ ≤ 1 / 5 * (1 / 100) := by gcongr
    _ < 1 / 100 := by norm_num

/-! ### The maps and their derivatives -/

private lemma exampleMaps_zero : exampleMaps 0 = fun z => z / 8 := rfl

private lemma exampleMaps_one : exampleMaps 1 = fun z => z / 8 + z ^ 2 / 32 := rfl

private lemma exampleMaps_two : exampleMaps 2 = fun z => z / 16 + z ^ 2 / 32 + 29 / 32 := rfl

private lemma hasDerivAt_exampleMaps_zero (z : ℂ) : HasDerivAt (exampleMaps 0) (1 / 8) z := by
  rw [exampleMaps_zero]
  exact hasDerivAt_id' z |>.div_const 8

private lemma hasDerivAt_exampleMaps_one (z : ℂ) :
    HasDerivAt (exampleMaps 1) (1 / 8 + z / 16) z := by
  rw [exampleMaps_one]
  have h := (hasDerivAt_id' z |>.div_const 8).add ((hasDerivAt_pow 2 z).div_const 32)
  convert h using 1
  push_cast
  ring

private lemma hasDerivAt_exampleMaps_two (z : ℂ) :
    HasDerivAt (exampleMaps 2) (1 / 16 + z / 16) z := by
  rw [exampleMaps_two]
  have h := ((hasDerivAt_id' z |>.div_const 16).add ((hasDerivAt_pow 2 z).div_const 32)).add_const
    (29 / 32 : ℂ)
  convert h using 1
  push_cast
  ring

private lemma deriv_exampleMaps_zero : deriv (exampleMaps 0) = fun _ => 1 / 8 :=
  funext fun z => (hasDerivAt_exampleMaps_zero z).deriv

private lemma deriv_exampleMaps_one : deriv (exampleMaps 1) = fun z => 1 / 8 + z / 16 :=
  funext fun z => (hasDerivAt_exampleMaps_one z).deriv

private lemma deriv_exampleMaps_two : deriv (exampleMaps 2) = fun z => 1 / 16 + z / 16 :=
  funext fun z => (hasDerivAt_exampleMaps_two z).deriv

private lemma deriv_deriv_exampleMaps_zero : deriv (deriv (exampleMaps 0)) = fun _ => 0 := by
  rw [deriv_exampleMaps_zero]
  funext z
  exact deriv_const z _

private lemma deriv_deriv_exampleMaps_one : deriv (deriv (exampleMaps 1)) = fun _ => 1 / 16 := by
  rw [deriv_exampleMaps_one]
  funext z
  exact ((hasDerivAt_id' z).div_const 16 |>.const_add (1 / 8)).deriv

private lemma deriv_deriv_exampleMaps_two : deriv (deriv (exampleMaps 2)) = fun _ => 1 / 16 := by
  rw [deriv_exampleMaps_two]
  funext z
  exact ((hasDerivAt_id' z).div_const 16 |>.const_add (1 / 16)).deriv

/-! ### Values at real points -/

private lemma exampleMaps_zero_ofReal (x : ℝ) : exampleMaps 0 x = ((x / 8 : ℝ) : ℂ) := by
  rw [exampleMaps_zero]
  push_cast
  rfl

private lemma exampleMaps_one_ofReal (x : ℝ) :
    exampleMaps 1 x = ((x / 8 + x ^ 2 / 32 : ℝ) : ℂ) := by
  rw [exampleMaps_one]
  push_cast
  rfl

private lemma exampleMaps_two_ofReal (x : ℝ) :
    exampleMaps 2 x = ((x / 16 + x ^ 2 / 32 + 29 / 32 : ℝ) : ℂ) := by
  rw [exampleMaps_two]
  push_cast
  rfl

/-! ### Norm estimates -/

private lemma example_norm_factor_le (c : ℂ) {z : ℂ} {x : ℝ} (hx : x ∈ I)
    (hzx : ‖z - x‖ ≤ 1 / 100) : ‖c + (z + x) / 32‖ ≤ ‖c‖ + 201 / 100 / 32 := by
  have hz := (example_bounds_of_near hx hzx).1
  have hx' : ‖(x : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hx.1]; exact hx.2
  calc ‖c + (z + x) / 32‖ ≤ ‖c‖ + ‖(z + x) / 32‖ := norm_add_le _ _
    _ = ‖c‖ + ‖z + x‖ / 32 := by rw [norm_div]; norm_num
    _ ≤ ‖c‖ + (‖z‖ + ‖(x : ℂ)‖) / 32 := by gcongr; exact norm_add_le _ _
    _ ≤ ‖c‖ + 201 / 100 / 32 := by linarith

private lemma example_norm_deriv_le (c : ℂ) {z : ℂ} (hz : z ∈ closure (nbhd (1 / 100))) :
    ‖c + z / 16‖ ≤ ‖c‖ + 101 / 100 / 16 := by
  have hz' := (example_bounds hz).1
  calc ‖c + z / 16‖ ≤ ‖c‖ + ‖z / 16‖ := norm_add_le _ _
    _ = ‖c‖ + ‖z‖ / 16 := by rw [norm_div]; norm_num
    _ ≤ ‖c‖ + 101 / 100 / 16 := by linarith

private lemma example_re_deriv_pos (c : ℝ) (hc : 1 / 1600 < c) {z : ℂ}
    (hz : z ∈ closure (nbhd (1 / 100))) : (c : ℂ) + z / 16 ≠ 0 := by
  have hz' := (example_bounds hz).2
  intro h
  have h' := congrArg Complex.re h
  rw [Complex.add_re, Complex.ofReal_re, Complex.div_ofNat_re, Complex.zero_re] at h'
  linarith

/-! ### The three maps lie in the class -/

private lemma example_inClass_zero : InClass (1 / 100) (exampleMaps 0) where
  differentiableOn z _ := (hasDerivAt_exampleMaps_zero z).differentiableAt.differentiableWithinAt
  im_eq_zero x _ := by rw [exampleMaps_zero_ofReal, Complex.ofReal_im]
  re_mem_I x hx := by
    rw [exampleMaps_zero_ofReal, Complex.ofReal_re]
    obtain ⟨h0, h1⟩ := hx
    constructor <;> linarith
  mapsTo := by
    refine example_mapsTo (fun x hx => ⟨x / 8, ?_, exampleMaps_zero_ofReal x⟩) fun z x _ _ => ?_
    · obtain ⟨h0, h1⟩ := hx
      constructor <;> linarith
    · rw [exampleMaps_zero]
      simp only
      rw [show z / 8 - (x : ℂ) / 8 = (z - x) * (1 / 8) by ring, norm_mul]
      norm_num
      linarith [norm_nonneg (z - x)]
  deriv_ne_zero z _ := by rw [deriv_exampleMaps_zero]; norm_num
  norm_deriv_lt_one z _ := by rw [deriv_exampleMaps_zero]; norm_num

private lemma example_inClass_one : InClass (1 / 100) (exampleMaps 1) where
  differentiableOn z _ := (hasDerivAt_exampleMaps_one z).differentiableAt.differentiableWithinAt
  im_eq_zero x _ := by rw [exampleMaps_one_ofReal, Complex.ofReal_im]
  re_mem_I x hx := by
    rw [exampleMaps_one_ofReal, Complex.ofReal_re]
    obtain ⟨h0, h1⟩ := hx
    constructor <;> nlinarith
  mapsTo := by
    refine example_mapsTo (fun x hx => ⟨x / 8 + x ^ 2 / 32, ?_, exampleMaps_one_ofReal x⟩)
      fun z x hx hzx => ?_
    · obtain ⟨h0, h1⟩ := hx
      constructor <;> nlinarith
    · rw [exampleMaps_one]
      simp only
      rw [show z / 8 + z ^ 2 / 32 - ((x : ℂ) / 8 + (x : ℂ) ^ 2 / 32) =
          (z - x) * (1 / 8 + (z + x) / 32) by ring, norm_mul, mul_comm]
      gcongr
      refine (example_norm_factor_le _ hx hzx).trans ?_
      norm_num
  deriv_ne_zero z hz := by
    rw [deriv_exampleMaps_one]
    have h := example_re_deriv_pos (1 / 8) (by norm_num) hz
    push_cast at h
    exact h
  norm_deriv_lt_one z hz := by
    rw [deriv_exampleMaps_one]
    refine (example_norm_deriv_le _ hz).trans_lt ?_
    norm_num

private lemma example_inClass_two : InClass (1 / 100) (exampleMaps 2) where
  differentiableOn z _ := (hasDerivAt_exampleMaps_two z).differentiableAt.differentiableWithinAt
  im_eq_zero x _ := by rw [exampleMaps_two_ofReal, Complex.ofReal_im]
  re_mem_I x hx := by
    rw [exampleMaps_two_ofReal, Complex.ofReal_re]
    obtain ⟨h0, h1⟩ := hx
    constructor <;> nlinarith
  mapsTo := by
    refine example_mapsTo
      (fun x hx => ⟨x / 16 + x ^ 2 / 32 + 29 / 32, ?_, exampleMaps_two_ofReal x⟩)
      fun z x hx hzx => ?_
    · obtain ⟨h0, h1⟩ := hx
      constructor <;> nlinarith
    · rw [exampleMaps_two]
      simp only
      rw [show z / 16 + z ^ 2 / 32 + 29 / 32 - ((x : ℂ) / 16 + (x : ℂ) ^ 2 / 32 + 29 / 32) =
          (z - x) * (1 / 16 + (z + x) / 32) by ring, norm_mul, mul_comm]
      gcongr
      refine (example_norm_factor_le _ hx hzx).trans ?_
      norm_num
  deriv_ne_zero z hz := by
    rw [deriv_exampleMaps_two]
    have h := example_re_deriv_pos (1 / 16) (by norm_num) hz
    push_cast at h
    exact h
  norm_deriv_lt_one z hz := by
    rw [deriv_exampleMaps_two]
    refine (example_norm_deriv_le _ hz).trans_lt ?_
    norm_num

theorem exampleMaps_inClass (i : Fin 3) : InClass (1 / 100) (exampleMaps i) := by
  fin_cases i
  · exact example_inClass_zero
  · exact example_inClass_one
  · exact example_inClass_two

/-- The example as an IFS in `𝔖_3`, with `ε = 1/100`. -/
noncomputable def exampleIFS : IFS 3 (1 / 100) where
  f := exampleMaps
  ε_pos := by norm_num
  inClass := exampleMaps_inClass

/-! ### The constants `c_max` and `β` -/

private lemma example_fin_three (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  revert i
  decide

private lemma example_norm_deriv_le_all (i : Fin 3) {z : ℂ} (hz : z ∈ closure (nbhd (1 / 100))) :
    ‖deriv (exampleMaps i) z‖ ≤ 19 / 100 := by
  obtain rfl | rfl | rfl := example_fin_three i
  · rw [deriv_exampleMaps_zero]
    norm_num
  · rw [deriv_exampleMaps_one]
    refine (example_norm_deriv_le _ hz).trans ?_
    norm_num
  · rw [deriv_exampleMaps_two]
    refine (example_norm_deriv_le _ hz).trans ?_
    norm_num

theorem exampleIFS_cmax_lt : exampleIFS.cmax < 1 / 5 := by
  have : Nonempty (closure (nbhd (1 / 100 : ℝ))) := ⟨⟨0, zero_mem_closure_nbhd (by norm_num)⟩⟩
  have h : exampleIFS.cmax ≤ 19 / 100 :=
    ciSup_le fun i => ciSup_le fun z => example_norm_deriv_le_all i z.2
  linarith

private lemma example_nonlin_zero (z : ℂ) : exampleIFS.nonlin 0 z = 0 := by
  change deriv (deriv (exampleMaps 0)) z / deriv (exampleMaps 0) z = 0
  rw [deriv_deriv_exampleMaps_zero, deriv_exampleMaps_zero, zero_div]

private lemma example_nonlin_one (z : ℂ) :
    exampleIFS.nonlin 1 z = 1 / 16 / (1 / 8 + z / 16) := by
  change deriv (deriv (exampleMaps 1)) z / deriv (exampleMaps 1) z = _
  rw [deriv_deriv_exampleMaps_one, deriv_exampleMaps_one]

private lemma example_nonlin_two (z : ℂ) :
    exampleIFS.nonlin 2 z = 1 / 16 / (1 / 16 + z / 16) := by
  change deriv (deriv (exampleMaps 2)) z / deriv (exampleMaps 2) z = _
  rw [deriv_deriv_exampleMaps_two, deriv_exampleMaps_two]

private lemma example_norm_nonlin_le (i : Fin 3) {x : ℝ} (hx : x ∈ I) :
    ‖exampleIFS.nonlin i x‖ ≤ 1 := by
  have h0 := hx.1
  obtain rfl | rfl | rfl := example_fin_three i
  · rw [example_nonlin_zero, norm_zero]
    exact zero_le_one
  · rw [example_nonlin_one, show (1 / 16 : ℂ) / (1 / 8 + (x : ℂ) / 16) =
        ((1 / 16 / (1 / 8 + x / 16) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), div_le_one (by positivity)]
    linarith
  · rw [example_nonlin_two, show (1 / 16 : ℂ) / (1 / 16 + (x : ℂ) / 16) =
        ((1 / 16 / (1 / 16 + x / 16) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), div_le_one (by positivity)]
    linarith

theorem exampleIFS_beta_le : exampleIFS.beta ≤ 1 := by
  have : Nonempty I := ⟨⟨0, le_rfl, zero_le_one⟩⟩
  exact ciSup_le fun x => ciSup_le fun i => example_norm_nonlin_le i x.2

/-! ### Separation of the distortions and the SESC -/

theorem exampleIFS_nonlin_sep (i j : Fin 3) (hij : i ≠ j) :
    (1 / 2 : ℝ) ≤ ‖exampleIFS.nonlin i 0 - exampleIFS.nonlin j 0‖ := by
  have h0 := example_nonlin_zero 0
  have h1 : exampleIFS.nonlin 1 0 = 1 / 2 := by rw [example_nonlin_one]; norm_num
  have h2 : exampleIFS.nonlin 2 0 = 1 := by rw [example_nonlin_two]; norm_num
  obtain rfl | rfl | rfl := example_fin_three i <;>
    obtain rfl | rfl | rfl := example_fin_three j <;>
    first
    | exact absurd rfl hij
    | (simp only [h0, h1, h2]; norm_num)

/-- The example satisfies the SESC. -/
theorem exampleIFS_sesc : exampleIFS.SESC := by
  have hsep : ∀ i j : Fin 3, i ≠ j →
      ∃ x ∈ I, (1 / 2 : ℝ) ≤ ‖exampleIFS.nonlin i x - exampleIFS.nonlin j x‖ :=
    fun i j hij => ⟨0, ⟨le_rfl, zero_le_one⟩, by
      rw [Complex.ofReal_zero]
      exact exampleIFS_nonlin_sep i j hij⟩
  obtain ⟨hβ, h⟩ := exampleIFS.proposition_1_8 (by norm_num) (by norm_num) hsep
  have hc := exampleIFS_cmax_lt
  have hc0 := exampleIFS.cmax_nonneg
  have hb := exampleIFS_beta_le
  refine (h ?_).2
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- The example lies in `𝔖_3` for some `ε > 0` and satisfies the SESC. -/
theorem example_sesc :
    ∃ ε > 0, ∃ Φ : IFS 3 ε, Φ.f = exampleMaps ∧ Φ.SESC :=
  ⟨1 / 100, by norm_num, exampleIFS, rfl, exampleIFS_sesc⟩

end AnalyticESC
