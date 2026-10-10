module

public import AnalyticESC.Dimension.NaturalMeasure

@[expose] public section

/-!
# The `L^q` dimension of the natural measure of the polynomial example

`L^q` dimensions of the polynomial example in Section 1.2.2: for `q > 1`, the `L^q` spectrum
`τ_μ(q) = liminf_{r → 0} log(∑_{k ∈ ℤ} μ([kr, (k+1)r))^q) / log r` and the `L^q` dimension
`D_μ(q) = τ_μ(q)/(q - 1)` of the natural measure `μ` of the example satisfy
`D_μ(q) ≤ q (s(Φ) - 1/3) / (q - 1)`, which is smaller than `s(Φ)` for `q > 3 s(Φ)`. The sum
contains the term `μ([0,r))^q ≥ μ(B(0,r/2))^q`, and `μ(B(0,r))` has local dimension `s(Φ) - 1/3`
at `0` (`example_localDim`). The bound is deduced by contradiction through the ball-mass
estimate of Shmerkin's Lemma 1.7, proved here in the form needed at `0`.
-/

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory

/-- The `L^q` sum `∑_{k ∈ ℤ} μ([kr, (k+1)r))^q` of `μ` at scale `r`. -/
noncomputable def lqSum (μ : Measure ℝ) (q r : ℝ) : ℝ :=
  ∑' k : ℤ, μ.real (Ico (k * r) ((k + 1) * r)) ^ q

/-- The quotient `log(∑_{k ∈ ℤ} μ([kr, (k+1)r))^q) / log r`, whose limit inferior as `r → 0` is the
`L^q` spectrum. -/
noncomputable def lqRatio (μ : Measure ℝ) (q r : ℝ) : ℝ := Real.log (lqSum μ q r) / Real.log r

/-- The `L^q` dimension `D_μ(q) = τ_μ(q)/(q - 1)` of Section 1.2.2, where
`τ_μ(q) = liminf_{r → 0} log(∑_{k ∈ ℤ} μ([kr, (k+1)r))^q) / log r` is the `L^q` spectrum. -/
noncomputable def lqDim (μ : Measure ℝ) (q : ℝ) : ℝ := liminf (lqRatio μ q) (𝓝[>] 0) / (q - 1)

/-! ### `L^q` sums of a probability measure on `ℝ` -/

/-- The intervals `[kr, (k+1)r)`, `k ∈ ℤ`, partition `ℝ`, so their masses sum to `1`. -/
private theorem lq_hasSum (μ : Measure ℝ) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) :
    HasSum (fun k : ℤ => μ.real (Ico (k * r) ((k + 1) * r))) 1 := by
  have hU : ⋃ k : ℤ, Ico (k * r) ((k + 1) * r) = univ := by
    simpa [zsmul_eq_mul] using iUnion_Ico_zsmul hr
  have hD : Pairwise (Function.onFun Disjoint fun k : ℤ => Ico (k * r) ((k + 1) * r)) := by
    simpa [zsmul_eq_mul] using pairwise_disjoint_Ico_zsmul r
  have h := measure_iUnion (μ := μ) hD fun _ => measurableSet_Ico
  rw [hU, measure_univ] at h
  have hne : ∑' k : ℤ, μ (Ico (k * r) ((k + 1) * r)) ≠ ⊤ := by
    rw [← h]
    exact ENNReal.one_ne_top
  have hS := ENNReal.hasSum_toReal hne
  rw [← ENNReal.tsum_toReal_eq fun _ => measure_ne_top _ _, ← h, ENNReal.toReal_one] at hS
  exact hS

/-- For `q ≥ 1`, the `L^q` sum converges and lies in `[0, 1]`. -/
private theorem lq_summable_and_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ] {q r : ℝ}
    (hq : 1 ≤ q) (hr : 0 < r) :
    Summable (fun k : ℤ => μ.real (Ico (k * r) ((k + 1) * r)) ^ q) ∧ 0 ≤ lqSum μ q r ∧
      lqSum μ q r ≤ 1 := by
  have hS := lq_hasSum μ hr
  have hle : ∀ k : ℤ, μ.real (Ico (k * r) ((k + 1) * r)) ^ q ≤
      μ.real (Ico (k * r) ((k + 1) * r)) :=
    fun _ => Real.rpow_le_self_of_le_one measureReal_nonneg measureReal_le_one hq
  have hsum : Summable fun k : ℤ => μ.real (Ico (k * r) ((k + 1) * r)) ^ q :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hle hS.summable
  refine ⟨hsum, tsum_nonneg fun _ => by positivity, ?_⟩
  calc lqSum μ q r ≤ ∑' k : ℤ, μ.real (Ico (k * r) ((k + 1) * r)) :=
        hsum.tsum_le_tsum hle hS.summable
    _ = 1 := hS.tsum_eq

/-- For `q ≥ 1` and `0 < r < 1`, the quotient `log(∑_k μ([kr, (k+1)r))^q) / log r` is
nonnegative. -/
private theorem lqRatio_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] {q r : ℝ} (hq : 1 ≤ q)
    (hr0 : 0 < r) (hr1 : r < 1) : 0 ≤ lqRatio μ q r := by
  obtain ⟨-, h0, h1⟩ := lq_summable_and_bounds μ hq hr0
  exact div_nonneg_of_nonpos (Real.log_nonpos h0 h1) (Real.log_neg hr0 hr1).le

/-- If `μ` vanishes on `(-∞, 0)`, the term `μ([0,r))^q ≥ μ(B(0,r/2))^q` of the `L^q` sum gives
`log(∑_k μ([kr, (k+1)r))^q) / log r ≤ q log μ(B(0,r/2)) / log r` for `0 < r < 1`. -/
private theorem lqRatio_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : μ (Iio 0) = 0)
    {q r : ℝ} (hq : 1 ≤ q) (hr0 : 0 < r) (hr1 : r < 1)
    (hm : 0 < μ.real (closedBall 0 (r / 2))) :
    lqRatio μ q r ≤ q * Real.log (μ.real (closedBall 0 (r / 2))) / Real.log r := by
  obtain ⟨hsum, -, -⟩ := lq_summable_and_bounds μ hq hr0
  set m := μ.real (closedBall 0 (r / 2)) with hm_def
  have hsub : closedBall (0 : ℝ) (r / 2) ⊆ Iio 0 ∪ Ico 0 r := by
    intro x hx
    rw [mem_closedBall, Real.dist_eq, sub_zero, abs_le] at hx
    by_cases hx0 : x < 0
    · exact Or.inl hx0
    · exact Or.inr ⟨not_lt.1 hx0, by linarith⟩
  have hmI : m ≤ μ.real (Ico 0 r) :=
    calc m ≤ μ.real (Iio 0 ∪ Ico 0 r) := measureReal_mono hsub
      _ ≤ μ.real (Iio 0) + μ.real (Ico 0 r) := measureReal_union_le _ _
      _ = μ.real (Ico 0 r) := by rw [measureReal_def, h0, ENNReal.toReal_zero, zero_add]
  have hterm : μ.real (Ico 0 r) ^ q ≤ lqSum μ q r := by
    have h := hsum.le_tsum 0 fun _ _ => by positivity
    rw [Int.cast_zero, zero_mul, zero_add, one_mul] at h
    exact h
  have hpos : 0 < m ^ q := Real.rpow_pos_of_pos hm q
  have hmq : m ^ q ≤ lqSum μ q r := (Real.rpow_le_rpow hm.le hmI (by linarith)).trans hterm
  have hlog : q * Real.log m ≤ Real.log (lqSum μ q r) := by
    rw [← Real.log_rpow hm]
    exact Real.log_le_log hpos hmq
  exact div_le_div_of_nonpos_of_le (Real.log_neg hr0 hr1).le hlog

/-- A probability measure on `ℝ` vanishing on `(-∞, 0)`, charging every ball `B(0,r)` and with
local dimension `d` at `0` has `L^q` spectrum at most `q d` for `q > 1`; the quotient whose limit
inferior is the `L^q` spectrum is bounded below and does not tend to `∞`. -/
private theorem lq_liminf_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : μ (Iio 0) = 0)
    (hpos : ∀ r > 0, 0 < μ.real (closedBall 0 r)) {d : ℝ}
    (hlim : Tendsto (fun r => Real.log (μ.real (closedBall 0 r)) / Real.log r) (𝓝[>] 0) (𝓝 d))
    {q : ℝ} (hq : 1 < q) :
    IsBoundedUnder (· ≥ ·) (𝓝[>] 0) (lqRatio μ q) ∧
      IsCoboundedUnder (· ≥ ·) (𝓝[>] 0) (lqRatio μ q) ∧
      liminf (lqRatio μ q) (𝓝[>] 0) ≤ q * d := by
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 1 := Ioo_mem_nhdsGT one_pos
  set g : ℝ → ℝ := fun r => q * Real.log (μ.real (closedBall 0 (r / 2))) / Real.log r with hg_def
  have hg : Tendsto g (𝓝[>] 0) (𝓝 (q * d)) := by
    have h2 : Tendsto (fun r : ℝ => r / 2) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact ((continuous_id.div_const 2).tendsto' 0 0 (by simp)).mono_left
          nhdsWithin_le_nhds
      · exact eventually_mem_nhdsWithin.mono fun r hr => half_pos hr
    have hA := hlim.comp h2
    have hB : Tendsto (fun r => Real.log (r / 2) / Real.log r) (𝓝[>] 0) (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
        ((tendsto_const_nhds (x := Real.log 2)).div_atBot Real.tendsto_log_nhdsGT_zero)
      rw [sub_zero] at h
      refine h.congr' (hev.mono fun r hr => ?_)
      have hl : Real.log r ≠ 0 := (Real.log_neg hr.1 hr.2).ne
      show 1 - Real.log 2 / Real.log r = Real.log (r / 2) / Real.log r
      rw [Real.log_div hr.1.ne' two_ne_zero, sub_div, div_self hl]
    have h := (hA.mul hB).const_mul q
    rw [mul_one] at h
    refine h.congr' (hev.mono fun r hr => ?_)
    have hl : Real.log (r / 2) ≠ 0 := (Real.log_neg (half_pos hr.1) (by linarith [hr.2])).ne
    simp only [Function.comp_apply, hg_def]
    field_simp
  have hle : ∀ᶠ r in 𝓝[>] (0 : ℝ), lqRatio μ q r ≤ g r :=
    hev.mono fun r hr => lqRatio_le μ h0 hq.le hr.1 hr.2 (hpos _ (half_pos hr.1))
  have hbdd : IsBoundedUnder (· ≥ ·) (𝓝[>] 0) (lqRatio μ q) :=
    isBoundedUnder_of_eventually_ge (hev.mono fun r hr => lqRatio_nonneg μ hq.le hr.1 hr.2)
  have hg1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), g r ≤ q * d + 1 :=
    (hg.eventually (gt_mem_nhds (lt_add_one (q * d)))).mono fun _ h => h.le
  refine ⟨hbdd, isCoboundedUnder_ge_of_eventually_le _ (x := q * d + 1) ?_, ?_⟩
  · filter_upwards [hle, hg1] with r h1 h2
    exact h1.trans h2
  · rw [← hg.liminf_eq]
    exact liminf_le_liminf hle hbdd (isCoboundedUnder_ge_of_eventually_le _ hg1)

/-- The ball-mass estimate in Shmerkin's Lemma 1.7, specialised to the point `0` of a
measure supported on `[0,∞)`. At scale `r`, one grid interval covers `B(0,r/2)` up to a null
set. This is proved here, not assumed. See P. Shmerkin, Ann. of Math. 189 (2019), 319–391,
Lemma 1.7, DOI 10.4007/annals.2019.189.2.1. -/
theorem shmerkin_ball_bound_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h0 : μ (Iio 0) = 0) (hpos : ∀ r > 0, 0 < μ.real (closedBall 0 r))
    {q s : ℝ} (hq : 1 < q)
    (hbdd : IsBoundedUnder (· ≥ ·) (𝓝[>] 0) (lqRatio μ q)) (hs : s < lqDim μ q) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), μ.real (closedBall 0 (r / 2)) ≤ r ^ ((1 - 1 / q) * s) := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have ht : (q - 1) * s < liminf (lqRatio μ q) (𝓝[>] 0) := by
    have := (lt_div_iff₀ (sub_pos.2 hq)).1 hs
    linarith
  filter_upwards [eventually_lt_of_lt_liminf ht hbdd, (show Ioo (0 : ℝ) 1 ∈ 𝓝[>] 0 from Ioo_mem_nhdsGT one_pos)]
    with r hr hrI
  have hm := hpos (r / 2) (half_pos hrI.1)
  have hl := Real.log_neg hrI.1 hrI.2
  have he := (lt_div_iff_of_neg hl).1 (hr.trans_le (lqRatio_le μ h0 hq.le hrI.1 hrI.2 hm))
  apply (Real.log_le_log_iff hm (Real.rpow_pos_of_pos hrI.1 _)).1
  rw [Real.log_rpow hrI.1]
  have halg : q * ((1 - 1 / q) * s * Real.log r) = (q - 1) * s * Real.log r := by
    field_simp
  nlinarith

/-- A local dimension is at least a ball-mass exponent; replacing `r` by `r/2` does not
change the logarithmic limit. -/
private theorem localDim_ge_of_ball_bound (μ : Measure ℝ)
    (hpos : ∀ r > 0, 0 < μ.real (closedBall 0 r)) {d a : ℝ}
    (hlim : Tendsto (fun r => Real.log (μ.real (closedBall 0 r)) / Real.log r) (𝓝[>] 0) (𝓝 d))
    (hball : ∀ᶠ r in 𝓝[>] (0 : ℝ), μ.real (closedBall 0 (r / 2)) ≤ r ^ a) : a ≤ d := by
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 1 := Ioo_mem_nhdsGT one_pos
  have h2 : Tendsto (fun r : ℝ => r / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_id.div_const 2).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    · exact eventually_mem_nhdsWithin.mono fun r hr => half_pos hr
  have hlog : Tendsto (fun r => Real.log (r / 2) / Real.log r) (𝓝[>] 0) (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := Real.log 2)).div_atBot Real.tendsto_log_nhdsGT_zero)
    rw [sub_zero] at h
    refine h.congr' (hev.mono fun r hr => ?_)
    change 1 - Real.log 2 / Real.log r = Real.log (r / 2) / Real.log r
    rw [Real.log_div hr.1.ne' two_ne_zero, sub_div, div_self (Real.log_neg hr.1 hr.2).ne]
  have ht : Tendsto (fun r => Real.log (μ.real (closedBall 0 (r / 2))) / Real.log r)
      (𝓝[>] 0) (𝓝 d) := by
    have h := (hlim.comp h2).mul hlog
    rw [mul_one] at h
    refine h.congr' (hev.mono fun r hr => ?_)
    have hl : Real.log (r / 2) ≠ 0 := (Real.log_neg (half_pos hr.1) (by linarith [hr.2])).ne
    dsimp only [Function.comp_apply]
    field_simp
  apply ge_of_tendsto ht
  filter_upwards [hev, hball] with r hr hb
  have he := Real.log_le_log (hpos _ (half_pos hr.1)) hb
  rw [Real.log_rpow hr.1] at he
  exact (le_div_iff_of_neg (Real.log_neg hr.1 hr.2)).2 he

/-- The contradiction used in Section 1.2.2: a larger `L^q` dimension would, by the
ball-mass estimate of Lemma 1.7, force a larger local dimension at `0`. -/
theorem lqDim_le_of_localDim (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h0 : μ (Iio 0) = 0) (hpos : ∀ r > 0, 0 < μ.real (closedBall 0 r)) {d : ℝ}
    (hlim : Tendsto (fun r => Real.log (μ.real (closedBall 0 r)) / Real.log r) (𝓝[>] 0) (𝓝 d))
    {q : ℝ} (hq : 1 < q) (hbdd : IsBoundedUnder (· ≥ ·) (𝓝[>] 0) (lqRatio μ q)) :
    lqDim μ q ≤ q / (q - 1) * d := by
  by_contra! h
  obtain ⟨s, hs, hsD⟩ := exists_between h
  have hd := localDim_ge_of_ball_bound μ hpos hlim (shmerkin_ball_bound_zero μ h0 hpos hq hbdd hsD)
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have he : q * ((1 - 1 / q) * s) = (q - 1) * s := by field_simp
  have hs' : q * d < s * (q - 1) := by
    rw [div_mul_eq_mul_div] at hs
    exact (div_lt_iff₀ (sub_pos.2 hq)).1 hs
  nlinarith [mul_le_mul_of_nonneg_left hd hq0.le]

/-! ### The natural measure of the example near `0` -/

/-- If the first `m` letters of `ω` are `0`, then `π(ω) ≤ 8^{-m}`, as `f_0(z) = z/8`. -/
private theorem lq_natProj_le {m : ℕ} {ω : ℕ → Fin 3} (h : ∀ i < m, ω i = 0) :
    exampleIFS.natProj ω ≤ (1 / 8 : ℝ) ^ m := by
  have hy := exampleIFS.attractor_subset_I ⟨fun j => ω (j + m), rfl⟩
  have hl : (List.ofFn fun j : Fin m => ω j) = List.replicate m 0 :=
    List.ext_getElem (by simp) fun n h1 _ => by
      simp only [List.getElem_ofFn, List.getElem_replicate]
      exact h n (by simpa using h1)
  have hc : ∀ (n : ℕ) (z : ℂ), exampleIFS.comp (List.replicate n 0) z = z / 8 ^ n := by
    intro n
    induction n with
    | zero => intro z; simp [IFS.comp_nil]
    | succ n ih =>
      intro z
      rw [List.replicate_succ, IFS.comp_cons, Function.comp_apply, ih]
      show z / 8 ^ n / 8 = z / 8 ^ (n + 1)
      ring
  rw [exampleIFS.natProj_eq_comp_prefix ω m, hl, hc]
  set y := exampleIFS.natProj fun j => ω (j + m)
  have hy' : ((y : ℂ) / 8 ^ m) = ((y / 8 ^ m : ℝ) : ℂ) := by push_cast; ring
  rw [hy', Complex.ofReal_re, one_div_pow]
  exact div_le_div_of_nonneg_right hy.2 (by positivity)

/-- The natural measure of a Gibbs measure charges every ball `B(0,r)`, `r > 0`: it contains the
image of the cylinder `[0^m]` for `8^{-m} ≤ r`. -/
private theorem lq_measureReal_closedBall_pos {φ : (ℕ → Fin 3) → ℝ} {ν : Measure (ℕ → Fin 3)}
    [IsProbabilityMeasure ν] (hG : IsGibbsMeasure φ ν) {r : ℝ} (hr : 0 < r) :
    0 < (ν.map exampleIFS.natProj).real (closedBall 0 r) := by
  obtain ⟨c₁, hc₁, c₂, -, P, hG⟩ := hG
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 8 : ℝ) < 1)
  rw [map_measureReal_apply exampleIFS.measurable_natProj measurableSet_closedBall]
  refine (mul_pos hc₁ (Real.exp_pos _)).trans_le
    ((hG (fun _ => 0) m).1.trans (measureReal_mono fun y hy => ?_))
  have h0 := exampleIFS.attractor_subset_I ⟨y, rfl⟩
  rw [mem_preimage, mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg h0.1]
  exact (lq_natProj_le fun i hi => hy i hi).trans hm.le

/-- `L^q` dimensions of the polynomial example in Section 1.2.2, from Bowen's theorem:
for every Gibbs measure `ν` of the potential `s(Φ) log|f'_{ω₀}(π(σω))|` and every `q > 1`,
the natural measure `μ = ν ∘ π⁻¹` has `D_μ(q) ≤ q (s(Φ) - 1/3) / (q - 1)`, which is smaller than `s(Φ)` for `q > 3 s(Φ)`. The `L^q` sums
converge, and the quotient whose limit inferior is `τ_μ(q)` is bounded below and does not tend to
`∞`, so the limit inferior is not a junk value. -/
theorem example_lq_of_bowen (hB : BowenGibbsStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (fun n : ℕ => Real.log (exampleIFS.pressureSum t n) / n) atTop (𝓝 0) ↔
        t = s) ∧
      ∀ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν →
        IsGibbsMeasure (exampleIFS.potential s) ν → ∀ q > 1,
        (∀ r > 0, Summable fun k : ℤ =>
          (ν.map exampleIFS.natProj).real (Ico (k * r) ((k + 1) * r)) ^ q) ∧
        IsBoundedUnder (· ≥ ·) (𝓝[>] 0) (lqRatio (ν.map exampleIFS.natProj) q) ∧
        IsCoboundedUnder (· ≥ ·) (𝓝[>] 0) (lqRatio (ν.map exampleIFS.natProj) q) ∧
        lqDim (ν.map exampleIFS.natProj) q ≤ q / (q - 1) * (s - 1 / 3) ∧
        (3 * s < q → lqDim (ν.map exampleIFS.natProj) q < s) := by
  obtain ⟨s, hs, -, hloc⟩ := example_localDim_of_bowen hB
  refine ⟨s, hs, fun ν hν hG q hq => ?_⟩
  have := hν
  have hE : exampleIFS.natProj ⁻¹' Iio 0 = ∅ := eq_empty_iff_forall_notMem.2 fun ω hω =>
    not_lt.2 (exampleIFS.attractor_subset_I ⟨ω, rfl⟩).1 hω
  have h0 : (ν.map exampleIFS.natProj) (Iio 0) = 0 := by
    rw [Measure.map_apply exampleIFS.measurable_natProj measurableSet_Iio, hE, measure_empty]
  obtain ⟨hbdd, hcob, -⟩ := lq_liminf_le _ h0
    (fun _ hr => lq_measureReal_closedBall_pos hG hr) (hloc ν hν hG) hq
  have hq1 : 0 < q - 1 := sub_pos.2 hq
  have hdim := lqDim_le_of_localDim _ h0
    (fun _ hr => lq_measureReal_closedBall_pos hG hr) (hloc ν hν hG) hq hbdd
  refine ⟨fun r hr => (lq_summable_and_bounds _ hq.le hr).1, hbdd, hcob, hdim,
    fun h3 => hdim.trans_lt ?_⟩
  rw [div_mul_eq_mul_div, div_lt_iff₀ hq1]
  linarith

end AnalyticESC
