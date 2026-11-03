module

public import AnalyticESC.Literature.Rapaport.Analytic.Main.PieceBounds

@[expose] public section

/-!
# Lemma 4.1 of Rapaport: the fibres act with zero entropy at the scale `e^{-χ m}`

Lemma 4.1 of A. Rapaport, *Dimension of self-conformal measures associated to an exponentially
separated analytic IFS on ℝ*, arXiv:2412.16753v2: for `β`-a.e. `ω`,
`(1/m) H((Π_m β_ω).μ, 𝒟_{χ m}) → 0`. The proof of Theorem 1.2 only uses its integrated form,
which is proved here: `(1/m) ∫ H((Π_m β_x).μ, 𝒟_{L_m}) dμ(x) → 0` for levels `L_m` with
`2^{L_m} ≤ e^{χ m}`. The pointwise bound is Rapaport's: the words `w` with
`|φ_w'(0)| ≤ e^{-m(χ-δ)}` map `μ` into an interval of length `O(e^{-m(χ-δ)})` around `x`, and the
remaining words have small mass by the Lyapunov limit (2.6). Integrating the bound needs (2.6)
only for `β`, not on the fibres.

## Main declarations

* `tendsto_measure_dev_of_ae`: almost sure convergence implies convergence in measure.
* `tendsto_bernoulli_not_goodDeriv`: the words with `|(1/m) log |φ_w'(0)| + χ| ≥ δ` have
  `β`-mass `→ 0`.
* `integral_fibre_real`: `∫ β_x(s) dμ(x) = β(s)`.
* `ae_mem_image_of_fibre`: for `μ`-a.e. `x`, every cylinder `[w]` of positive `β_x`-mass has
  `x ∈ φ_w(I)`.
* `ent_wordAct_le_of_carried`: the pointwise bound of Lemma 4.1.
* `eventually_integral_ent_le`: the integrated Lemma 4.1.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Main.ZeroEntropy`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic.SectionFour

open MeasureTheory ProbabilityTheory Set Filter Topology FractalGeometry.SelfConformal
open FractalGeometry.Rapaport.Analytic
open AnalyticESC (I realComp RapaportHyp)
open scoped ENNReal

variable {N : ℕ} {φ : Fin N → ℝ → ℝ}

/-! ### Convergence in measure -/

/-- Almost sure convergence of measurable functions implies convergence in measure. -/
theorem tendsto_measure_dev_of_ae {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsFiniteMeasure ν] {f : ℕ → α → ℝ} (hf : ∀ m, Measurable (f m)) {c : ℝ}
    (hlim : ∀ᵐ ω ∂ν, Tendsto (fun m => f m ω) atTop (𝓝 c)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun m => ν.real {ω | ε ≤ |f m ω - c|}) atTop (𝓝 0) := by
  have h := tendstoInMeasure_of_tendsto_ae (g := fun _ => c)
    (fun m => (hf m).aestronglyMeasurable) hlim
  rw [tendstoInMeasure_iff_dist] at h
  have h2 := h ε hε
  simp only [Real.dist_eq] at h2
  have h3 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h2
  simp only [ENNReal.toReal_zero] at h3
  exact h3

/-- The normalised logarithmic derivative `(1/m) log |φ_{ω|_m}'(0)|` is measurable in `ω`. -/
theorem measurable_logDeriv_pre (m : ℕ) :
    Measurable fun ω : ℕ → Fin N => Real.log |deriv (wordMap φ (pre m ω)) 0| / m :=
  (measurable_of_countable (fun w : Fin m → Fin N =>
    Real.log |deriv (wordMap φ w) 0| / m)).comp (measurable_pre m)

/-- Rapaport's (2.6) in measure: `β{ω : |(1/m) log |φ_{ω|_m}'(0)| + χ| ≥ δ} → 0`. -/
theorem tendsto_bernoulli_not_goodDeriv (hφ : RapaportHyp φ) {p : Fin N → ℝ}
    (hp : AnalyticESC.IsProbVec p) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun m => (bernoulli p hp).real
      {ω | δ ≤ |Real.log |deriv (wordMap φ (pre m ω)) 0| / m - -lyapunov φ p hp|})
      atTop (𝓝 0) :=
  tendsto_measure_dev_of_ae measurable_logDeriv_pre
    (ae_tendsto_log_abs_deriv_realComp hφ hp) hδ

/-- A word with `|(1/m) log |φ_w'(0)| + χ| < δ`, `m > 0`, is good. -/
theorem goodWord_of_abs_lt {χ δ : ℝ} {m : ℕ} (hm : 0 < m) {w : Fin m → Fin N}
    (hw0 : deriv (wordMap φ w) 0 ≠ 0)
    (h : |Real.log |deriv (wordMap φ w) 0| / m - -χ| < δ) : GoodWord φ χ δ w := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hpos : 0 < |deriv (wordMap φ w) 0| := abs_pos.2 hw0
  rw [abs_lt, sub_neg_eq_add] at h
  obtain ⟨h1, h2⟩ := h
  have e1 : -(m * (χ + δ)) < Real.log |deriv (wordMap φ w) 0| := by
    have := (lt_div_iff₀ hm').1 (by linarith : -δ - χ < Real.log |deriv (wordMap φ w) 0| / m)
    linarith
  have e2 : Real.log |deriv (wordMap φ w) 0| < -(m * (χ - δ)) := by
    have := (div_lt_iff₀ hm').1 (by linarith : Real.log |deriv (wordMap φ w) 0| / m < δ - χ)
    linarith
  constructor
  · rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.2 e1.le
  · rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.2 e2.le

/-! ### The fibres -/

/-- `∫ β_x(s) dμ(x) = β(s)` for measurable `s`. -/
theorem integral_fibre_real [NeZero N] {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p)
    {s : Set (ℕ → Fin N)} (hs : MeasurableSet s) :
    ∫ x, (fibre φ p hp x).real s ∂selfConformal φ p hp = (bernoulli p hp).real s := by
  have hm : Measurable fun x => fibre φ p hp x s :=
    (graphMeasure φ p hp).condKernel.measurable_coe hs
  simp only [measureReal_def]
  rw [integral_toReal hm.aemeasurable (Eventually.of_forall fun x => measure_lt_top _ _),
    bernoulli_eq_lintegral_fibre φ hp hs]

/-- For `μ`-a.e. `x`, every cylinder `[w]` of positive `β_x`-mass has `x ∈ φ_w(I)`. -/
theorem ae_mem_image_of_fibre [NeZero N] (hφ : RapaportHyp φ) {p : Fin N → ℝ}
    (hp : AnalyticESC.IsProbVec p) :
    ∀ᵐ x ∂selfConformal φ p hp, ∀ (m : ℕ) (w : Fin m → Fin N),
      fibre φ p hp x (cylinder w) ≠ 0 → x ∈ wordMap φ w '' I := by
  filter_upwards [ae_exists_mem_cylinder_coding_eq φ hp] with x hx m w hw
  obtain ⟨η, hη, rfl⟩ := hx m w (pos_iff_ne_zero.2 hw)
  exact ⟨_, coding_mem hφ _, (coding_eq_of_mem_cylinder hφ hη).symm⟩

/-! ### The pointwise bound -/

/-- The pointwise bound of Lemma 4.1: if `ξ` is carried by cylinders `[w]` with `x ∈ φ_w(I)`,
and `B` is the set of `η` with `|φ_{η|_m}'(0)| ≤ R`, then
`H((Π_m ξ).μ, 𝒟_L) ≤ log (2^L 2 C R + 2) + ξ(Bᶜ) log (2^L + 2) + log 2`. -/
theorem ent_wordAct_le_of_carried (hφ : RapaportHyp φ) {θ : Measure ℝ} [IsProbabilityMeasure θ]
    (hθ : θ Iᶜ = 0) (ξ : Measure (ℕ → Fin N)) [IsProbabilityMeasure ξ] (x : ℝ) (m L : ℕ)
    {R : ℝ} (hR : 0 ≤ R)
    (hE1 : ∀ w : Fin m → Fin N, ξ (cylinder w) ≠ 0 → x ∈ wordMap φ w '' I) :
    ent (wordAct φ θ ξ m) (cellIdx L) ≤
      Real.log (2 ^ L * (2 * (distConst φ * R)) + 2) +
        ξ.real {η | |deriv (wordMap φ (pre m η)) 0| ≤ R}ᶜ * Real.log (2 ^ L + 2) +
        Real.log 2 := by
  classical
  set B : Set (ℕ → Fin N) := {η | |deriv (wordMap φ (pre m η)) 0| ≤ R} with hB_def
  have hBm : MeasurableSet B :=
    measurable_pre m (MeasurableSet.of_discrete
      (s := {w : Fin m → Fin N | |deriv (wordMap φ w) 0| ≤ R}))
  have hWprob := isProbabilityMeasure_wordAct (φ := φ) (θ := θ) ξ m
  set wt : Fin 2 → ℝ := ![ξ.real B, ξ.real Bᶜ] with hwt
  set θs : Fin 2 → Measure ℝ := ![wordAct φ θ ξ[|B] m, wordAct φ θ ξ[|Bᶜ] m] with hθs
  have hwt0 : ∀ i, 0 ≤ wt i := by
    intro i
    fin_cases i <;> simp [hwt, measureReal_nonneg]
  have hwt1 : ∑ i, wt i = 1 := by
    simp [hwt, Fin.sum_univ_two, measureReal_add_measureReal_compl hBm, probReal_univ]
  have hθsprob : ∀ i, wt i ≠ 0 → IsProbabilityMeasure (θs i) := by
    intro i hi
    fin_cases i
    · have : ξ B ≠ 0 := fun h => hi (by simp [hwt, measureReal_def, h])
      have := cond_isProbabilityMeasure (μ := ξ) this
      exact isProbabilityMeasure_wordAct (θ := θ) _ _
    · have : ξ Bᶜ ≠ 0 := fun h => hi (by simp [hwt, measureReal_def, h])
      have := cond_isProbabilityMeasure (μ := ξ) this
      exact isProbabilityMeasure_wordAct (θ := θ) _ _
  have hmix : wordAct φ θ ξ m = ∑ i, ENNReal.ofReal (wt i) • θs i := by
    have hdec : ξ = ξ B • ξ[|B] + ξ Bᶜ • ξ[|Bᶜ] := by
      ext t ht
      simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [mul_comm (ξ B), mul_comm (ξ Bᶜ), cond_add_cond_compl_eq hBm]
    conv_lhs => rw [hdec]
    rw [wordAct_add, wordAct_smul, wordAct_smul, Fin.sum_univ_two]
    simp [hwt, hθs, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hconv := ent_le_sum_ent_add_of_ne_zero hwt0 hwt1 hθsprob hmix (measurable_cellIdx L)
    (finiteLabels_cellIdx (wordAct_compl_I hφ hθ ξ m) L)
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at hconv
  have hH : Real.negMulLog (wt 0) + Real.negMulLog (wt 1) ≤ Real.log 2 := by
    have := sum_negMulLog_le_log_card hwt0 hwt1
    rw [Fin.sum_univ_two] at this
    simpa using this
  -- the first piece is carried by an interval of length `2 C R` around `x`
  have hfirst : wt 0 * ent (θs 0) (cellIdx L) ≤
      Real.log (2 ^ L * (2 * (distConst φ * R)) + 2) := by
    by_cases h0 : wt 0 = 0
    · rw [h0, zero_mul]
      refine Real.log_nonneg ?_
      have : 0 ≤ 2 ^ L * (2 * (distConst φ * R)) := by
        have := distConst_pos (φ := φ)
        positivity
      linarith
    have hprob := hθsprob 0 h0
    have hcarr : ∀ᵐ y ∂(θs 0), y ∈ Icc (x - distConst φ * R) (x + distConst φ * R) := by
      rw [ae_iff]
      simp only [hθs, Matrix.cons_val_zero]
      rw [wordAct_apply]
      refine Finset.sum_eq_zero fun w _ => ?_
      by_cases hw : ξ[|B] (cylinder w) = 0
      · rw [hw, zero_mul]
      · rw [cond_apply hBm] at hw
        have hne : ξ (B ∩ cylinder w) ≠ 0 := fun h => hw (by rw [h, mul_zero])
        obtain ⟨η, hηB, hηw⟩ := nonempty_of_measure_ne_zero hne
        have hpre : pre m η = w := funext fun k => hηw k
        have hwR : |deriv (wordMap φ w) 0| ≤ R := by
          have := hηB
          simp only [hB_def, mem_ofPred_eq, hpre] at this
          exact this
        have hξw : ξ (cylinder w) ≠ 0 := fun h =>
          hne (measure_mono_null Set.inter_subset_right h)
        obtain ⟨y₀, hy₀, hxy⟩ := hE1 w hξw
        have hmap : θ.map (wordMap φ w)
            {y | y ∉ Icc (x - distConst φ * R) (x + distConst φ * R)} = 0 := by
          rw [show {y | y ∉ Icc (x - distConst φ * R) (x + distConst φ * R)} =
            (Icc (x - distConst φ * R) (x + distConst φ * R))ᶜ from rfl,
            Measure.map_apply_of_aemeasurable (aemeasurable_wordMap hφ hθ w)
            (measurableSet_Icc.compl)]
          refine measure_mono_null (fun y hy => ?_) hθ
          intro hyI
          apply hy
          have h1 := abs_realComp_sub_le_distConst hφ (List.ofFn w) hyI hy₀ zero_mem_I
          rw [← wordMap_def] at h1
          have h2 : |y - y₀| ≤ 1 := abs_sub_le_one_of_mem_I hyI hy₀
          have h3 : distConst φ * |deriv (wordMap φ w) 0| * |y - y₀| ≤ distConst φ * R := by
            have := distConst_pos (φ := φ)
            calc distConst φ * |deriv (wordMap φ w) 0| * |y - y₀|
                ≤ distConst φ * R * 1 := by gcongr
              _ = distConst φ * R := mul_one _
          rw [hxy] at h1
          have h4 := h1.trans h3
          rw [abs_le] at h4
          constructor <;> linarith [h4.1, h4.2]
        rw [hmap, mul_zero]
    have hb := ent_cellIdx_comp_le_log (θ := θs 0) (F := id) measurable_id
      (a := x - distConst φ * R) (b := x + distConst φ * R)
      (by have := distConst_pos (φ := φ); nlinarith) L hcarr
    simp only [Function.comp_id] at hb
    have hw01 : wt 0 ≤ 1 := by simp [hwt, measureReal_le_one]
    have hent0 : 0 ≤ ent (θs 0) (cellIdx L) := ent_nonneg _
    calc wt 0 * ent (θs 0) (cellIdx L) ≤ 1 * ent (θs 0) (cellIdx L) :=
          mul_le_mul_of_nonneg_right hw01 hent0
      _ ≤ _ := by
          rw [one_mul]
          refine hb.trans_eq ?_
          congr 2
          ring
  have hsecond : wt 1 * ent (θs 1) (cellIdx L) ≤ ξ.real Bᶜ * Real.log (2 ^ L + 2) := by
    by_cases h1 : wt 1 = 0
    · rw [h1, zero_mul]
      exact mul_nonneg measureReal_nonneg (Real.log_nonneg (by
        have : (1 : ℝ) ≤ 2 ^ L := one_le_pow₀ (by norm_num)
        linarith))
    have hprob := hθsprob 1 h1
    have hb := ent_cellIdx_le_of_compl_I (θ := θs 1)
      (by simp only [hθs]; exact wordAct_compl_I hφ hθ _ _) L
    exact mul_le_mul_of_nonneg_left hb (hwt0 1)
  linarith

end FractalGeometry.Rapaport.Analytic.SectionFour
