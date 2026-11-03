module

public import AnalyticESC.Literature.Rapaport.Analytic.Main.ZeroEntropy

@[expose] public section

/-!
# The asymptotic inputs of the main argument

The statements "for `n` large enough" of the proof of Theorem 1.2 of A. Rapaport, *Dimension of
self-conformal measures associated to an exponentially separated analytic IFS on ℝ*,
arXiv:2412.16753v2, Section 4, along sequences of levels tending to infinity:

* `eventually_abs_ent_sub_le`: Young's identity (2.9) at the levels `j m → ∞`.
* `eventually_integral_ent_le`: the integrated Lemma 4.1.
* `eventually_measure_goodSet_ge`: the set `E` of good points (positive fibre entropy, small
  remainder) has measure `≥ 1 - δ`; Rapaport's `β(E) > 1 - δ`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Main.Eventually`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic.SectionFour

open MeasureTheory ProbabilityTheory Set Filter Topology FractalGeometry.SelfConformal
open FractalGeometry.Rapaport.Analytic
open AnalyticESC (I realComp RapaportHyp)
open scoped ENNReal

variable {N : ℕ} {φ : Fin N → ℝ → ℝ}

/-- Young's identity along levels `j m → ∞`: eventually `|H(θ, 𝒟_{j m}) - j m d log 2| ≤ δ j m`. -/
theorem eventually_abs_ent_sub_le {θ : Measure ℝ} [IsProbabilityMeasure θ] (hθ : θ Iᶜ = 0)
    {d : ℝ} (hd : FractalGeometry.IsExactDim θ d) {j : ℕ → ℕ} (hj : Tendsto j atTop atTop)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m in atTop, |ent θ (cellIdx (j m)) - j m * (d * Real.log 2)| ≤ δ * j m := by
  have h := (tendsto_ent_div_of_isExactDim hθ hd).comp hj
  have h2 := (Metric.tendsto_nhds.1 h) δ hδ
  filter_upwards [h2, hj.eventually_gt_atTop 0] with m hm hjm
  simp only [Function.comp_apply, Real.dist_eq] at hm
  have hjm' : (0 : ℝ) < j m := by exact_mod_cast hjm
  have : ent θ (cellIdx (j m)) - j m * (d * Real.log 2) =
      j m * (ent θ (cellIdx (j m)) / j m - d * Real.log 2) := by
    field_simp
  rw [this, abs_mul, abs_of_pos hjm', mul_comm δ]
  exact mul_le_mul_of_nonneg_left hm.le hjm'.le

/-- The integrated Lemma 4.1 of Rapaport: for levels `L m` with `2^{L m} ≤ e^{χ m}`,
eventually `∫ H((Π_m β_x).μ, 𝒟_{L m}) dμ(x) ≤ δ m`. -/
theorem eventually_integral_ent_le [NeZero N] (hφ : RapaportHyp φ) {p : Fin N → ℝ}
    (hp : AnalyticESC.IsProbVec p) {δ : ℝ} (hδ : 0 < δ) {L : ℕ → ℕ}
    (hL : ∀ m, (2 : ℝ) ^ L m ≤ Real.exp (lyapunov φ p hp * m)) :
    ∀ᶠ m : ℕ in atTop, ∫ x, ent (wordAct φ (selfConformal φ p hp) (fibre φ p hp x) m)
      (cellIdx (L m)) ∂selfConformal φ p hp ≤ δ * m := by
  set μ := selfConformal φ p hp with hμ
  set χ := lyapunov φ p hp with hχ
  have hμI : μ Iᶜ = 0 := selfConformal_compl_I hφ hp
  have hμprob : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hχ0 : 0 < χ := lyapunov_pos hφ hp
  set D := distConst φ with hD
  have hD0 : 0 < D := distConst_pos
  set δ₃ := δ / 4 with hδ₃
  have hδ₃0 : 0 < δ₃ := by positivity
  set ε₀ := δ / (2 * (χ + 2)) with hε₀
  have hε₀0 : 0 < ε₀ := by positivity
  -- the bad words have small `β`-mass
  have hbad := tendsto_bernoulli_not_goodDeriv hφ hp hδ₃0
  have hbad' := (Metric.tendsto_nhds.1 hbad) ε₀ hε₀0
  have hconst : ∀ᶠ m : ℕ in atTop, Real.log (4 * (D + 1)) + Real.log 2 ≤ δ / 4 * m := by
    have := tendsto_natCast_atTop_atTop (R := ℝ)
    filter_upwards [(this.const_mul_atTop (by positivity : (0 : ℝ) < δ / 4)).eventually_ge_atTop
      (Real.log (4 * (D + 1)) + Real.log 2)] with m hm
    exact hm
  filter_upwards [hbad', hconst, eventually_gt_atTop 0] with m hm hcm hm0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
  set R := Real.exp (-(m * (χ - δ₃))) with hR
  have hR0 : 0 ≤ R := (Real.exp_pos _).le
  set B : Set (ℕ → Fin N) := {η | |deriv (wordMap φ (pre m η)) 0| ≤ R} with hB
  have hBm : MeasurableSet B :=
    measurable_pre m (MeasurableSet.of_discrete
      (s := {w : Fin m → Fin N | |deriv (wordMap φ w) 0| ≤ R}))
  have hBc : (bernoulli p hp).real Bᶜ ≤ ε₀ := by
    refine le_trans (measureReal_mono fun η hη => ?_) hm.le
    simp only [hB, mem_compl_iff, mem_ofPred_eq, not_le] at hη
    simp only [mem_ofPred_eq]
    by_contra hlt
    push Not at hlt
    have hg := goodWord_of_abs_lt (χ := χ) hm0
      (deriv_realComp_ne_zero hφ (List.ofFn (pre m η)) zero_mem_I) hlt
    have := hg.2
    rw [hR] at hη
    rw [show (m : ℝ) * (χ - δ₃) = (m : ℝ) * (χ - δ₃) from rfl] at this
    linarith
  -- the pointwise bound
  have hpt : ∀ᵐ x ∂μ, ent (wordAct φ μ (fibre φ p hp x) m) (cellIdx (L m)) ≤
      Real.log (2 ^ L m * (2 * (D * R)) + 2) +
        (fibre φ p hp x).real Bᶜ * Real.log (2 ^ L m + 2) + Real.log 2 := by
    filter_upwards [ae_mem_image_of_fibre hφ hp] with x hx
    exact ent_wordAct_le_of_carried hφ hμI (fibre φ p hp x) x m (L m) hR0 (hx m)
  have hmB : Measurable fun x => (fibre φ p hp x).real Bᶜ :=
    ENNReal.measurable_toReal.comp ((graphMeasure φ p hp).condKernel.measurable_coe hBm.compl)
  have hintB : Integrable (fun x => (fibre φ p hp x).real Bᶜ) μ :=
    Integrable.of_mem_Icc 0 1 hmB.aemeasurable
      (Eventually.of_forall fun x => ⟨measureReal_nonneg, measureReal_le_one⟩)
  have hint2 : Integrable (fun x => Real.log (2 ^ L m * (2 * (D * R)) + 2) +
      (fibre φ p hp x).real Bᶜ * Real.log (2 ^ L m + 2) + Real.log 2) μ :=
    ((integrable_const _).add (hintB.mul_const _)).add (integrable_const _)
  have hmE : Measurable fun x => ent (wordAct φ μ (fibre φ p hp x) m) (cellIdx (L m)) :=
    measurable_ent_of_kernel (fun x => wordAct_compl_I hφ hμI _ m)
      (fun s _ => measurable_wordAct_fibre hp μ m s) (L m)
  have hintE : Integrable (fun x => ent (wordAct φ μ (fibre φ p hp x) m) (cellIdx (L m))) μ := by
    refine Integrable.of_mem_Icc 0 (Real.log (2 ^ L m + 2)) hmE.aemeasurable
      (Eventually.of_forall fun x => ?_)
    have := isProbabilityMeasure_wordAct (φ := φ) (θ := μ) (fibre φ p hp x) m
    exact ⟨ent_nonneg _, ent_cellIdx_le_of_compl_I (wordAct_compl_I hφ hμI _ m) _⟩
  refine (integral_mono_ae hintE hint2 hpt).trans ?_
  have hA1 : Integrable (fun x => (fibre φ p hp x).real Bᶜ * Real.log (2 ^ L m + 2)) μ :=
    hintB.mul_const _
  have hA2 : Integrable (fun x => Real.log (2 ^ L m * (2 * (D * R)) + 2) +
      (fibre φ p hp x).real Bᶜ * Real.log (2 ^ L m + 2)) μ := (integrable_const _).add hA1
  rw [integral_add hA2 (integrable_const _), integral_add (integrable_const _) hA1,
    integral_mul_const, integral_fibre_real hp hBm.compl]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  -- the three terms
  have h1 : Real.log (2 ^ L m * (2 * (D * R)) + 2) ≤ Real.log (4 * (D + 1)) + δ₃ * m := by
    have hLR : (2 : ℝ) ^ L m * R ≤ Real.exp (δ₃ * m) := by
      calc (2 : ℝ) ^ L m * R ≤ Real.exp (χ * m) * R := by gcongr; exact hL m
        _ = Real.exp (δ₃ * m) := by rw [hR, ← Real.exp_add]; congr 1; ring
    have hexp1 : 1 ≤ Real.exp (δ₃ * m) := Real.one_le_exp (by positivity)
    calc Real.log (2 ^ L m * (2 * (D * R)) + 2)
        ≤ Real.log (4 * (D + 1) * Real.exp (δ₃ * m)) := by
          refine Real.log_le_log (by positivity) ?_
          have : 2 ^ L m * (2 * (D * R)) = 2 * D * (2 ^ L m * R) := by ring
          rw [this]
          nlinarith
      _ = Real.log (4 * (D + 1)) + δ₃ * m := by
          rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  have h2 : (bernoulli p hp).real Bᶜ * Real.log (2 ^ L m + 2) ≤ δ / 2 * m := by
    have hlog : Real.log (2 ^ L m + 2) ≤ χ * m + 2 := by
      have h3 := log_two_pow_add_two_le (L m)
      have h4 : (L m : ℝ) * Real.log 2 ≤ χ * m := by
        have := Real.log_le_log (by positivity) (hL m)
        rwa [Real.log_pow, Real.log_exp] at this
      have h5 : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9
        linarith
      nlinarith
    have hlog0 : 0 ≤ Real.log (2 ^ L m + 2) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ 2 ^ L m := one_le_pow₀ (by norm_num)
      linarith)
    calc (bernoulli p hp).real Bᶜ * Real.log (2 ^ L m + 2) ≤ ε₀ * (χ * m + 2) :=
          mul_le_mul hBc hlog hlog0 hε₀0.le
      _ ≤ δ / 2 * m := by
          rw [hε₀, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
          nlinarith
  rw [hδ₃] at h1
  linarith

/-- Markov's inequality for the fibres: `μ{x : β_x(s) ≥ t} ≤ β(s) / t`. -/
theorem measure_fibre_ge_le [NeZero N] {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p)
    {s : Set (ℕ → Fin N)} (hs : MeasurableSet s) {t : ℝ} (ht : 0 < t) :
    (selfConformal φ p hp).real {x | t ≤ (fibre φ p hp x).real s} ≤
      (bernoulli p hp).real s / t := by
  have hm : Measurable fun x => (fibre φ p hp x).real s :=
    ENNReal.measurable_toReal.comp ((graphMeasure φ p hp).condKernel.measurable_coe hs)
  have h := mul_meas_ge_le_integral_of_nonneg (μ := selfConformal φ p hp)
    (Eventually.of_forall fun x => measureReal_nonneg (μ := fibre φ p hp x) (s := s))
    (Integrable.of_mem_Icc 0 1 hm.aemeasurable
      (Eventually.of_forall fun x => ⟨measureReal_nonneg, measureReal_le_one⟩)) t
  rw [integral_fibre_real hp hs] at h
  rw [le_div_iff₀ ht]
  linarith

/-- The cylinder entropy of the fibres is measurable. -/
theorem measurable_cylEntropy_fibre [NeZero N] {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p)
    (l : ℕ) : Measurable fun x => cylEntropy (fibre φ p hp x) l := by
  unfold cylEntropy
  refine Finset.measurable_sum _ fun u _ => ?_
  exact Real.continuous_negMulLog.measurable.comp (ENNReal.measurable_toReal.comp
    ((graphMeasure φ p hp).condKernel.measurable_coe (measurableSet_cylinder u)))

/-- The words of length `l > 0` that are not good have `β`-mass at most that of the words with
`|(1/l) log |φ_w'(0)| + χ| ≥ δ`. -/
theorem bernoulli_not_good_le (hφ : RapaportHyp φ) {p : Fin N → ℝ}
    (hp : AnalyticESC.IsProbVec p) {δ : ℝ} {l : ℕ} (hl : 0 < l) :
    (bernoulli p hp).real {η | ¬ GoodWord φ (lyapunov φ p hp) δ (pre l η)} ≤
      (bernoulli p hp).real
        {ω | δ ≤ |Real.log |deriv (wordMap φ (pre l ω)) 0| / l - -lyapunov φ p hp|} := by
  refine measureReal_mono fun η hη => ?_
  simp only [mem_ofPred_eq] at hη ⊢
  by_contra h
  push Not at h
  exact hη (goodWord_of_abs_lt hl (deriv_realComp_ne_zero hφ _ zero_mem_I) h)

/-- The good set `E` has measure `≥ 1 - δ` for `m` large: the fibres `β_x` have entropy `> Δ n`
on the first `n = n_m` letters and give mass `≤ 2δ` to the words that are not good, for `x` in a
set of `μ`-measure `≥ 1 - δ`. -/
theorem eventually_measure_goodSet_ge [NeZero N] (hφ : RapaportHyp φ) {p : Fin N → ℝ}
    (hp : AnalyticESC.IsProbVec p) {Δ' Δ : ℝ} (hΔ : Δ < Δ')
    (hfib : ∀ᵐ x ∂selfConformal φ p hp,
      Tendsto (fun l : ℕ => cylEntropy (fibre φ p hp x) l / l) atTop (𝓝 Δ'))
    {δ : ℝ} (hδ : 0 < δ) {n n' : ℕ → ℕ} (hn : Tendsto n atTop atTop)
    (hn' : Tendsto n' atTop atTop) :
    ∀ᶠ m in atTop, 1 - δ ≤ (selfConformal φ p hp).real
      {x | Δ * n m < ent (fibre φ p hp x) (pre (n m)) ∧
        (fibre φ p hp x).real {η | ¬ (GoodWord φ (lyapunov φ p hp) δ (pre (n m) η) ∧
          GoodWord φ (lyapunov φ p hp) δ (pre (n' m) (shift^[n m] η)))} ≤ 2 * δ} := by
  set μ := selfConformal φ p hp with hμ
  set β := bernoulli p hp with hβ
  set χ := lyapunov φ p hp with hχ
  have hμprob : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  set B₁ : ℕ → Set (ℕ → Fin N) := fun l => {η | ¬ GoodWord φ χ δ (pre l η)} with hB₁
  have hB₁m : ∀ l, MeasurableSet (B₁ l) := fun l =>
    measurable_pre l (MeasurableSet.of_discrete
      (s := {w : Fin l → Fin N | ¬ GoodWord φ χ δ w}))
  set B₂ : ℕ → Set (ℕ → Fin N) := fun m => shift^[n m] ⁻¹' B₁ (n' m) with hB₂
  have hB₂m : ∀ m, MeasurableSet (B₂ m) := fun m =>
    (measurable_shift.iterate (n m)) (hB₁m (n' m))
  have hB₂eq : ∀ m, β.real (B₂ m) = β.real (B₁ (n' m)) := fun m => by
    simp only [measureReal_def, hB₂]
    rw [((measurePreserving_shift hp).iterate (n m)).measure_preimage
      (hB₁m (n' m)).nullMeasurableSet]
  -- the three bad sets
  set A₁ : ℕ → Set ℝ := fun m => {x | ent (fibre φ p hp x) (pre (n m)) ≤ Δ * n m} with hA₁
  set A₂ : ℕ → Set ℝ := fun m => {x | δ ≤ (fibre φ p hp x).real (B₁ (n m))} with hA₂
  set A₃ : ℕ → Set ℝ := fun m => {x | δ ≤ (fibre φ p hp x).real (B₂ m)} with hA₃
  have hmeasEnt : ∀ l, Measurable fun x => ent (fibre φ p hp x) (pre l) := fun l => by
    simp_rw [← cylEntropy_eq_ent]
    exact measurable_cylEntropy_fibre hp l
  have hA₁m : ∀ m, MeasurableSet (A₁ m) := fun m =>
    measurableSet_le (hmeasEnt (n m)) measurable_const
  have hA₂m : ∀ m, MeasurableSet (A₂ m) := fun m =>
    measurableSet_le measurable_const (ENNReal.measurable_toReal.comp
      ((graphMeasure φ p hp).condKernel.measurable_coe (hB₁m (n m))))
  have hA₃m : ∀ m, MeasurableSet (A₃ m) := fun m =>
    measurableSet_le measurable_const (ENNReal.measurable_toReal.comp
      ((graphMeasure φ p hp).condKernel.measurable_coe (hB₂m m)))
  -- the limits
  have hδ3 : 0 < δ / 3 := by positivity
  have hlim₁ : ∀ᶠ m in atTop, μ.real (A₁ m) ≤ δ / 3 := by
    have hF : ∀ l, Measurable fun x => cylEntropy (fibre φ p hp x) l / l := fun l =>
      (measurable_cylEntropy_fibre hp l).div_const _
    have h := tendsto_measure_dev_of_ae hF hfib (sub_pos.2 hΔ)
    have h2 := (Metric.tendsto_nhds.1 (h.comp hn)) (δ / 3) hδ3
    filter_upwards [h2, hn.eventually_gt_atTop 0] with m hm hnm
    simp only [Function.comp_apply, Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
      at hm
    refine le_trans (measureReal_mono fun x hx => ?_) hm.le
    simp only [hA₁, mem_ofPred_eq] at hx ⊢
    have hn0 : (0 : ℝ) < n m := by exact_mod_cast hnm
    rw [← cylEntropy_eq_ent] at hx
    have : cylEntropy (fibre φ p hp x) (n m) / n m ≤ Δ := by
      rw [div_le_iff₀ hn0]
      linarith
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  have hβlim : ∀ {j : ℕ → ℕ}, Tendsto j atTop atTop →
      ∀ᶠ m in atTop, β.real (B₁ (j m)) ≤ δ * (δ / 3) := by
    intro j hj
    have h := (Metric.tendsto_nhds.1 ((tendsto_bernoulli_not_goodDeriv hφ hp hδ).comp hj))
      (δ * (δ / 3)) (by positivity)
    filter_upwards [h, hj.eventually_gt_atTop 0] with m hm hjm
    simp only [Function.comp_apply, Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
      at hm
    exact (bernoulli_not_good_le hφ hp hjm).trans hm.le
  have hlim₂ : ∀ᶠ m in atTop, μ.real (A₂ m) ≤ δ / 3 := by
    filter_upwards [hβlim hn] with m hm
    refine (measure_fibre_ge_le hp (hB₁m (n m)) hδ).trans ?_
    rw [div_le_iff₀ hδ]
    linarith
  have hlim₃ : ∀ᶠ m in atTop, μ.real (A₃ m) ≤ δ / 3 := by
    filter_upwards [hβlim hn'] with m hm
    refine (measure_fibre_ge_le hp (hB₂m m) hδ).trans ?_
    rw [hB₂eq, div_le_iff₀ hδ]
    linarith
  filter_upwards [hlim₁, hlim₂, hlim₃] with m h₁ h₂ h₃
  have hsub : (A₁ m ∪ A₂ m ∪ A₃ m)ᶜ ⊆
      {x | Δ * n m < ent (fibre φ p hp x) (pre (n m)) ∧
        (fibre φ p hp x).real {η | ¬ (GoodWord φ χ δ (pre (n m) η) ∧
          GoodWord φ χ δ (pre (n' m) (shift^[n m] η)))} ≤ 2 * δ} := by
    intro x hx
    simp only [hA₁, hA₂, hA₃, mem_compl_iff, mem_union, mem_ofPred_eq, not_or, not_le] at hx
    obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
    refine ⟨hx1, ?_⟩
    have hsub' : {η | ¬ (GoodWord φ χ δ (pre (n m) η) ∧
        GoodWord φ χ δ (pre (n' m) (shift^[n m] η)))} ⊆ B₁ (n m) ∪ B₂ m := by
      intro η hη
      simp only [mem_ofPred_eq, not_and_or] at hη
      rcases hη with h | h
      · exact Or.inl h
      · exact Or.inr h
    calc _ ≤ (fibre φ p hp x).real (B₁ (n m) ∪ B₂ m) := measureReal_mono hsub'
      _ ≤ (fibre φ p hp x).real (B₁ (n m)) + (fibre φ p hp x).real (B₂ m) :=
          measureReal_union_le _ _
      _ ≤ 2 * δ := by linarith
  have hAm : MeasurableSet (A₁ m ∪ A₂ m ∪ A₃ m) := ((hA₁m m).union (hA₂m m)).union (hA₃m m)
  calc 1 - δ ≤ 1 - (μ.real (A₁ m) + μ.real (A₂ m) + μ.real (A₃ m)) := by linarith
    _ ≤ 1 - μ.real (A₁ m ∪ A₂ m ∪ A₃ m) := by
        have := measureReal_union_le (μ := μ) (A₁ m ∪ A₂ m) (A₃ m)
        have := measureReal_union_le (μ := μ) (A₁ m) (A₂ m)
        linarith
    _ = μ.real (A₁ m ∪ A₂ m ∪ A₃ m)ᶜ := by rw [measureReal_compl hAm, probReal_univ]
    _ ≤ _ := measureReal_mono hsub

end FractalGeometry.Rapaport.Analytic.SectionFour
