module

public import AnalyticESC.Basic

@[expose] public section

/-!
# Real-variable and identity-theorem lemmas

Lemma 3.1 (closeness of two functions gives closeness of their derivatives), its iterate, the
identity theorem on `B_ε` in the forms used in the paper, and the elementary bound (4.3).
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-! ## Lemma 3.1 and its iterate -/

/-- Taylor's theorem of order two with the Lagrange remainder, for a `𝒞²` map on an open set
containing the segment between `x` and `y`. -/
private theorem exists_taylor_two {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {x y : ℝ} (hxy : x ≠ y) (hsub : uIcc x y ⊆ U) :
    ∃ ξ ∈ uIoo x y, f y - f x - deriv f x * (y - x) = deriv (deriv f) ξ * (y - x) ^ 2 / 2 := by
  obtain ⟨ξ, hξ, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hxy
    ((hf.mono hsub).of_le (by norm_num))
  refine ⟨ξ, hξ, ?_⟩
  have hd : derivWithin f (uIcc x y) x = deriv f x := by
    have : DifferentiableAt ℝ f x :=
      (hf.contDiffAt (hU.mem_nhds (hsub left_mem_uIcc))).differentiableAt (by norm_num)
    exact this.derivWithin (uniqueDiffOn_uIcc hxy x left_mem_uIcc)
  simp [hd] at h
  rw [iteratedDeriv_succ, iteratedDeriv_one] at h
  rw [← h]
  ring

/-- Lemma 3.1 for `𝒞²` maps on a neighbourhood of `J = [a, b]`, with any common bound `Q` for the
second derivatives. -/
theorem abs_deriv_sub_le_of_abs_sub_le {f g : ℝ → ℝ} {a b η Q : ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hab : Icc a b ⊆ U) (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U) (hη : 0 < η)
    (hJ : 2 * Real.sqrt η < b - a) (hfQ : ∀ x ∈ Icc a b, |deriv (deriv f) x| ≤ Q)
    (hgQ : ∀ x ∈ Icc a b, |deriv (deriv g) x| ≤ Q) (hfg : ∀ x ∈ Icc a b, |f x - g x| ≤ η) :
    ∀ x ∈ Icc a b, |deriv f x - deriv g x| ≤ (2 + Q) * Real.sqrt η := by
  intro x hx
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  have hs2 : Real.sqrt η ^ 2 = η := Real.sq_sqrt hη.le
  -- One of `x ± √η` lies in `[a, b]`.
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ Icc a b, |y - x| = Real.sqrt η := by
    by_cases h : x + Real.sqrt η ≤ b
    · exact ⟨x + Real.sqrt η, ⟨by linarith [hx.1], h⟩, by simp [abs_of_pos hs]⟩
    · refine ⟨x - Real.sqrt η, ⟨by linarith, by linarith [hx.2]⟩, ?_⟩
      rw [show x - Real.sqrt η - x = -Real.sqrt η by ring, abs_neg, abs_of_pos hs]
  have hxy : x ≠ y := by
    rintro rfl
    rw [sub_self, abs_zero] at hyx
    exact hs.ne hyx
  have hsub : uIcc x y ⊆ Icc a b := uIcc_subset_Icc hx hy
  obtain ⟨ξ₁, hξ₁, h₁⟩ := exists_taylor_two hU hf hxy (hsub.trans hab)
  obtain ⟨ξ₂, hξ₂, h₂⟩ := exists_taylor_two hU hg hxy (hsub.trans hab)
  have hξ₁' : ξ₁ ∈ Icc a b := hsub (Ioo_subset_Icc_self hξ₁)
  have hξ₂' : ξ₂ ∈ Icc a b := hsub (Ioo_subset_Icc_self hξ₂)
  have hd2 : (y - x) ^ 2 = η := by rw [← sq_abs, hyx, hs2]
  have key : (deriv f x - deriv g x) * (y - x) = (f y - g y) - (f x - g x) -
      (deriv (deriv f) ξ₁ - deriv (deriv g) ξ₂) * (y - x) ^ 2 / 2 := by
    linear_combination h₂ - h₁
  have hb : |deriv (deriv f) ξ₁ - deriv (deriv g) ξ₂| ≤ 2 * Q := by
    have := abs_sub (deriv (deriv f) ξ₁) (deriv (deriv g) ξ₂)
    linarith [hfQ ξ₁ hξ₁', hgQ ξ₂ hξ₂']
  have hmain : |deriv f x - deriv g x| * Real.sqrt η ≤ (2 + Q) * Real.sqrt η * Real.sqrt η := by
    rw [← hyx, ← abs_mul, key, hd2, hyx, mul_assoc, ← sq, hs2]
    have e1 := abs_sub (f y - g y - (f x - g x))
      ((deriv (deriv f) ξ₁ - deriv (deriv g) ξ₂) * η / 2)
    have e2 := abs_sub (f y - g y) (f x - g x)
    have e3 : |(deriv (deriv f) ξ₁ - deriv (deriv g) ξ₂) * η / 2| ≤ Q * η := by
      rw [abs_div, abs_mul, abs_of_pos hη, abs_two]
      nlinarith
    linarith [hfg x hx, hfg y hy]
  exact le_of_mul_le_mul_right hmain hs

/-- The second derivative of a `𝒞²` map on an open set is bounded on a compact interval inside
it. -/
private theorem bddAbove_abs_deriv_deriv {f : ℝ → ℝ} {U : Set ℝ} {a b : ℝ} (hU : IsOpen U)
    (hab : Icc a b ⊆ U) (hf : ContDiffOn ℝ 2 f U) :
    BddAbove (range fun y : Icc a b => |deriv (deriv f) y|) := by
  have h1 : ContDiffOn ℝ 1 (deriv f) U := hf.deriv_of_isOpen hU (by norm_num)
  have h2 : ContinuousOn (deriv (deriv f)) U := h1.continuousOn_deriv_of_isOpen hU le_rfl
  rw [← image_eq_range (fun y => |deriv (deriv f) y|)]
  exact isCompact_Icc.bddAbove_image ((h2.mono hab).abs)

/-- Lemma 3.1: for real analytic `f`, `g` on `J = [a, b]` with `2√η < |J|` and
`Q = max(sup_J |f''|, sup_J |g''|)`, `sup_J |f - g| ≤ η` implies `sup_J |f' - g'| ≤ (2 + Q)√η`. -/
theorem lemma_3_1 {f g : ℝ → ℝ} {a b η : ℝ} (hf : AnalyticOnNhd ℝ f (Icc a b))
    (hg : AnalyticOnNhd ℝ g (Icc a b)) (hη : 0 < η) (hJ : 2 * Real.sqrt η < b - a)
    (hfg : ∀ x ∈ Icc a b, |f x - g x| ≤ η) :
    ∀ x ∈ Icc a b, |deriv f x - deriv g x| ≤
      (2 + max (⨆ y : Icc a b, |deriv (deriv f) y|) (⨆ y : Icc a b, |deriv (deriv g) y|)) *
        Real.sqrt η := by
  set U := {x | AnalyticAt ℝ f x} ∩ {x | AnalyticAt ℝ g x}
  have hU : IsOpen U := (isOpen_analyticAt ℝ f).inter (isOpen_analyticAt ℝ g)
  have hab : Icc a b ⊆ U := fun x hx => ⟨hf x hx, hg x hx⟩
  have hfU : ContDiffOn ℝ 2 f U :=
    AnalyticOnNhd.contDiffOn (fun x hx => hx.1) hU.uniqueDiffOn
  have hgU : ContDiffOn ℝ 2 g U :=
    AnalyticOnNhd.contDiffOn (fun x hx => hx.2) hU.uniqueDiffOn
  refine abs_deriv_sub_le_of_abs_sub_le hU hab hfU hgU hη hJ (fun x hx => ?_) (fun x hx => ?_)
    hfg
  · exact (le_ciSup (bddAbove_abs_deriv_deriv hU hab hfU) ⟨x, hx⟩).trans (le_max_left _ _)
  · exact (le_ciSup (bddAbove_abs_deriv_deriv hU hab hgU) ⟨x, hx⟩).trans (le_max_right _ _)

/-- The `j`-th derivative of a `𝒞ⁿ` map on an open set is `𝒞^m` there whenever `j + m ≤ n`. -/
private theorem contDiffOn_iteratedDeriv_of_isOpen {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    {n : ℕ} (hf : ContDiffOn ℝ n f U) {j m : ℕ} (hjm : j + m ≤ n) :
    ContDiffOn ℝ m (iteratedDeriv j f) U := by
  induction j generalizing m with
  | zero =>
    rw [iteratedDeriv_zero]
    exact hf.of_le (by exact_mod_cast (by omega : m ≤ n))
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact (ih (m := m + 1) (by omega)).deriv_of_isOpen hU (by push_cast; rfl)

/-- Lemma 3.1 iterated `k` times: closeness `η ≤ 1` of `f` and `g` gives closeness
`(2 + Q)² η^{2^{-k}}` of their `k`-th derivatives, given bounds `Q` on the derivatives of order
at most `k + 1`. -/
theorem abs_iteratedDeriv_sub_le {f g : ℝ → ℝ} {a b η Q : ℝ} {U : Set ℝ} (k : ℕ) (hU : IsOpen U)
    (hab : Icc a b ⊆ U) (hf : ContDiffOn ℝ (k + 1) f U) (hg : ContDiffOn ℝ (k + 1) g U)
    (hη : 0 < η) (hη1 : η ≤ 1) (hQ : 0 ≤ Q)
    (hfQ : ∀ j ≤ k + 1, ∀ x ∈ Icc a b, |iteratedDeriv j f x| ≤ Q)
    (hgQ : ∀ j ≤ k + 1, ∀ x ∈ Icc a b, |iteratedDeriv j g x| ≤ Q)
    (hJ : 2 * (2 + Q) * η ^ ((2 : ℝ)⁻¹ ^ k) < b - a) (hfg : ∀ x ∈ Icc a b, |f x - g x| ≤ η) :
    ∀ x ∈ Icc a b, |iteratedDeriv k f x - iteratedDeriv k g x| ≤ (2 + Q) ^ 2 * η ^ ((2 : ℝ)⁻¹ ^ k) :=
  by
  have hf' : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) f U := by exact_mod_cast hf
  have hg' : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) g U := by exact_mod_cast hg
  have h2Q : 1 ≤ (2 + Q) ^ 2 := by nlinarith
  -- The bound `(2 + Q)² η^{2^{-j}}` is preserved by one application of Lemma 3.1.
  suffices H : ∀ j ≤ k, ∀ x ∈ Icc a b,
      |iteratedDeriv j f x - iteratedDeriv j g x| ≤ (2 + Q) ^ 2 * η ^ ((2 : ℝ)⁻¹ ^ j) from
    H k le_rfl
  intro j
  induction j with
  | zero =>
    intro _ x hx
    simp only [iteratedDeriv_zero, pow_zero, Real.rpow_one]
    nlinarith [hfg x hx]
  | succ j ih =>
    intro hjk x hx
    have hpos : 0 < η ^ ((2 : ℝ)⁻¹ ^ j) := Real.rpow_pos_of_pos hη _
    have hM : 0 < (2 + Q) ^ 2 * η ^ ((2 : ℝ)⁻¹ ^ j) := by positivity
    have hsqrt : Real.sqrt ((2 + Q) ^ 2 * η ^ ((2 : ℝ)⁻¹ ^ j)) =
        (2 + Q) * η ^ ((2 : ℝ)⁻¹ ^ (j + 1)) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith), Real.sqrt_eq_rpow,
        ← Real.rpow_mul hη.le, pow_succ, one_div]
    have hexp : η ^ ((2 : ℝ)⁻¹ ^ (j + 1)) ≤ η ^ ((2 : ℝ)⁻¹ ^ k) :=
      Real.rpow_le_rpow_of_exponent_ge hη hη1
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) hjk)
    have hJ' : 2 * Real.sqrt ((2 + Q) ^ 2 * η ^ ((2 : ℝ)⁻¹ ^ j)) < b - a := by
      rw [hsqrt]
      nlinarith
    have hdd : ∀ φ : ℝ → ℝ, deriv (deriv (iteratedDeriv j φ)) = iteratedDeriv (j + 2) φ := by
      intro φ
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have key := abs_deriv_sub_le_of_abs_sub_le hU hab
      (contDiffOn_iteratedDeriv_of_isOpen hU hf' (j := j) (m := 2) (by omega))
      (contDiffOn_iteratedDeriv_of_isOpen hU hg' (j := j) (m := 2) (by omega)) hM hJ'
      (fun y hy => by rw [hdd]; exact hfQ (j + 2) (by omega) y hy)
      (fun y hy => by rw [hdd]; exact hgQ (j + 2) (by omega) y hy)
      (ih (by omega)) x hx
    rw [hsqrt, ← iteratedDeriv_succ, ← iteratedDeriv_succ] at key
    calc _ ≤ _ := key
      _ = _ := by ring

/-! ## The identity theorem on `B_ε` -/

/-- The inclusion `ℝ → ℂ` maps punctured neighbourhoods into punctured neighbourhoods. -/
private theorem tendsto_ofReal_nhdsNE (c : ℝ) :
    Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] c) (𝓝[≠] (c : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  simpa using hx

/-- The real points of a nondegenerate interval accumulate in `ℂ` at its midpoint. -/
private theorem frequently_ofReal_mem_Icc {a b : ℝ} (hab : a < b) :
    ∃ᶠ z : ℂ in 𝓝[≠] (((a + b) / 2 : ℝ) : ℂ), ∃ x ∈ Icc a b, z = (x : ℂ) := by
  have hc : Icc a b ∈ 𝓝 ((a + b) / 2) := Icc_mem_nhds (by linarith) (by linarith)
  have h1 : ∃ᶠ x in 𝓝[≠] ((a + b) / 2), x ∈ Icc a b :=
    (eventually_nhdsWithin_of_eventually_nhds hc).frequently
  exact (tendsto_ofReal_nhdsNE _).frequently (h1.mono fun x hx => ⟨x, hx, rfl⟩)

/-- Identity theorem: maps holomorphic on `B_ε` that agree on a nondegenerate interval of `I`
agree on `B_ε`. -/
theorem eqOn_nbhd_of_eqOn_Icc {ε : ℝ} (hε : 0 < ε) {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (nbhd ε)) (hh : DifferentiableOn ℂ h (nbhd ε)) {a b : ℝ}
    (hab : a < b) (hI : Icc a b ⊆ I) (heq : ∀ x ∈ Icc a b, g x = h x) : EqOn g h (nbhd ε) := by
  have hU := isOpen_nbhd ε
  have hc : (((a + b) / 2 : ℝ) : ℂ) ∈ nbhd ε :=
    ofReal_mem_nbhd hε (hI ⟨by linarith, by linarith⟩)
  refine (hg.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq (hh.analyticOnNhd hU)
    (isPreconnected_nbhd ε) hc ?_
  exact (frequently_ofReal_mem_Icc hab).mono fun z ⟨x, hx, hz⟩ => hz ▸ heq x hx

/-- Identity theorem: maps holomorphic on `B_ε` with all derivatives equal at a point of `I`
agree on `B_ε`. -/
theorem eqOn_nbhd_of_iteratedDeriv_eq {ε : ℝ} (hε : 0 < ε) {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (nbhd ε)) (hh : DifferentiableOn ℂ h (nbhd ε)) {x : ℝ} (hx : x ∈ I)
    (heq : ∀ k, iteratedDeriv k g x = iteratedDeriv k h x) : EqOn g h (nbhd ε) := by
  have hU := isOpen_nbhd ε
  have hball : ball (x : ℂ) ε ⊆ nbhd ε := ball_subset_nbhd hx
  -- Both maps equal their Taylor series at `x` on the disc of radius `ε`.
  have hloc : g =ᶠ[𝓝 (x : ℂ)] h := by
    filter_upwards [ball_mem_nhds (x : ℂ) hε] with z hz
    rw [← Complex.taylorSeries_eq_on_ball' hz (hg.mono hball),
      ← Complex.taylorSeries_eq_on_ball' hz (hh.mono hball)]
    simp_rw [heq]
  exact (hg.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hh.analyticOnNhd hU)
    (isPreconnected_nbhd ε) (ofReal_mem_nbhd hε hx) hloc

/-- A map holomorphic on `B_ε`, not identically zero on `I`, has finitely many zeros in `I`. -/
theorem finite_zeros {ε : ℝ} (hε : 0 < ε) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (nbhd ε))
    (hne : ∃ x ∈ I, g x ≠ 0) : {x : ℝ | x ∈ I ∧ g x = 0}.Finite := by
  by_contra hinf
  -- Infinitely many zeros in the compact `I` accumulate at some `c ∈ I`.
  obtain ⟨c, hcI, hacc⟩ :=
    Set.Infinite.exists_accPt_of_subset_isCompact hinf isCompact_Icc fun x hx => hx.1
  have hfreq : ∃ᶠ z in 𝓝[≠] (c : ℂ), g z = 0 := by
    rw [accPt_iff_frequently_nhdsNE] at hacc
    exact (tendsto_ofReal_nhdsNE c).frequently (hacc.mono fun x hx => hx.2)
  have hzero :=
    (hg.analyticOnNhd (isOpen_nbhd ε)).eqOn_zero_of_preconnected_of_frequently_eq_zero
      (isPreconnected_nbhd ε) (ofReal_mem_nbhd hε hcI) hfreq
  obtain ⟨x, hx, hgx⟩ := hne
  exact hgx (hzero (ofReal_mem_nbhd hε hx))

/-! ## The bound (4.3) -/

/-- The maximum of `|x|^p e^{-x²/σ}` over `x ∈ ℝ` is `(pσ/2)^{p/2} e^{-p/2}`. -/
private theorem rpow_abs_mul_exp_le {p σ : ℝ} (hp : 0 < p) (hσ : 0 < σ) (x : ℝ) :
    |x| ^ p * Real.exp (-x ^ 2 / σ) ≤ (p / 2 * σ) ^ (p / 2) * Real.exp (-(p / 2)) := by
  have hA : 0 < p / 2 := by positivity
  have hAσ : 0 < p / 2 * σ := by positivity
  set v := x ^ 2 / (p / 2 * σ) with hv_def
  have hv : 0 ≤ v := by positivity
  have h1 : v ≤ Real.exp (v - 1) := by linarith [Real.add_one_le_exp (v - 1)]
  have h2 : |x| ^ p = (p / 2 * σ) ^ (p / 2) * v ^ (p / 2) := by
    rw [← Real.mul_rpow hAσ.le hv, hv_def, mul_div_cancel₀ _ hAσ.ne',
      show p = 2 * (p / 2) by ring, Real.rpow_mul (abs_nonneg x)]
    norm_num [sq_abs]
  have h3 : v ^ (p / 2) ≤ Real.exp ((v - 1) * (p / 2)) := by
    rw [Real.exp_mul]
    exact Real.rpow_le_rpow hv h1 hA.le
  have h4 : (v - 1) * (p / 2) + -x ^ 2 / σ = -(p / 2) := by
    rw [hv_def]
    field_simp
    ring
  calc |x| ^ p * Real.exp (-x ^ 2 / σ)
      = (p / 2 * σ) ^ (p / 2) * (v ^ (p / 2) * Real.exp (-x ^ 2 / σ)) := by rw [h2]; ring
    _ ≤ (p / 2 * σ) ^ (p / 2) * (Real.exp ((v - 1) * (p / 2)) * Real.exp (-x ^ 2 / σ)) := by
      gcongr
    _ = (p / 2 * σ) ^ (p / 2) * Real.exp (-(p / 2)) := by rw [← Real.exp_add, h4]

/-- The elementary bound (4.3): for `c, p, ε > 0` and `q > -p/2`,
`sup_{x ∈ ℝ} c σ^q |x|^p e^{-x²/σ} ≤ ε` whenever
`0 < σ ≤ (2e/p)^{p/(2q+p)} (ε/c)^{1/(q+p/2)}`. -/
theorem gaussian_bound {c p ε q σ : ℝ} (hc : 0 < c) (hp : 0 < p) (hε : 0 < ε) (hq : -(p / 2) < q)
    (hσ : 0 < σ)
    (hσle : σ ≤ (2 * Real.exp 1 / p) ^ (p / (2 * q + p)) * (ε / c) ^ (1 / (q + p / 2)))
    (x : ℝ) : c * σ ^ q * |x| ^ p * Real.exp (-x ^ 2 / σ) ≤ ε := by
  have hA : 0 < p / 2 := by positivity
  have hr : 0 < q + p / 2 := by linarith
  have h2qp : 0 < 2 * q + p := by linarith
  -- Raise the hypothesis on `σ` to the power `q + p/2`.
  have hσr : σ ^ (q + p / 2) ≤ (2 * Real.exp 1 / p) ^ (p / 2) * (ε / c) := by
    have h := Real.rpow_le_rpow hσ.le hσle hr.le
    rwa [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul (by positivity),
      show p / (2 * q + p) * (q + p / 2) = p / 2 by field_simp,
      one_div_mul_cancel hr.ne', Real.rpow_one] at h
  have he : p / 2 * (2 * Real.exp 1 / p) = Real.exp 1 := by field_simp
  calc c * σ ^ q * |x| ^ p * Real.exp (-x ^ 2 / σ)
      = c * σ ^ q * (|x| ^ p * Real.exp (-x ^ 2 / σ)) := by ring
    _ ≤ c * σ ^ q * ((p / 2 * σ) ^ (p / 2) * Real.exp (-(p / 2))) :=
      mul_le_mul_of_nonneg_left (rpow_abs_mul_exp_le hp hσ x) (by positivity)
    _ = c * ((p / 2) ^ (p / 2) * Real.exp (-(p / 2))) * σ ^ (q + p / 2) := by
      rw [Real.mul_rpow hA.le hσ.le, Real.rpow_add hσ]
      ring
    _ ≤ c * ((p / 2) ^ (p / 2) * Real.exp (-(p / 2))) *
        ((2 * Real.exp 1 / p) ^ (p / 2) * (ε / c)) := by gcongr
    _ = c * (ε / c) * (Real.exp (-(p / 2)) * (p / 2 * (2 * Real.exp 1 / p)) ^ (p / 2)) := by
      rw [Real.mul_rpow hA.le (by positivity)]
      ring
    _ = ε := by
      rw [he, Real.exp_one_rpow, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      field_simp

end AnalyticESC
