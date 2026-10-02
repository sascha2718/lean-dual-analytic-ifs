module

public import AnalyticESC.Dimension.Pressure

@[expose] public section

/-!
# The natural measure

From Bowen's theorem (`BowenGibbsStatement`), the potential `s log|f'_{ω₀}(π(σω))|` has a Gibbs
measure `ν`. When `s = s(Φ)`, `ν` has the Gibbs property `ν[w] ≍ ‖f_w'‖^s` of `IFS.IsGibbs`, so the
results of `Main.LocalDimension` apply to the natural measure `ν ∘ π⁻¹`.
-/

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-! ### Cylinders -/

/-- The prefix map `ω ↦ ω₁ ⋯ ωₙ` is measurable (as in `Main.LocalDimension`). -/
private theorem nm_measurable_prefix (n : ℕ) :
    Measurable fun (ω : ℕ → Fin N) (k : Fin n) => ω k :=
  Measurable.of_eval fun k => measurable_pi_apply (k : ℕ)

/-- The cylinder of a word of length `n` is the preimage of the word under the prefix map. -/
private theorem nm_wordCylinder_ofFn {n : ℕ} (v : Fin n → Fin N) :
    wordCylinder (List.ofFn v) = (fun (ω : ℕ → Fin N) (k : Fin n) => ω k) ⁻¹' {v} := by
  ext ω
  simp only [wordCylinder, mem_ofPred_eq, mem_preimage, mem_singleton_iff, funext_iff]
  constructor
  · intro h k
    simpa using h ⟨k, by simp⟩
  · intro h k
    simpa using h ⟨k, by simpa using k.2⟩

/-- The cylinders of the words of length `n` have total measure `1`. -/
private theorem nm_sum_measureReal_wordCylinder (ν : Measure (ℕ → Fin N))
    [IsProbabilityMeasure ν] (n : ℕ) :
    ∑ v : Fin n → Fin N, ν.real (wordCylinder (List.ofFn v)) = 1 := by
  have h := sum_measureReal_singleton (μ := ν.map fun (ω : ℕ → Fin N) (k : Fin n) => ω k)
    (Finset.univ : Finset (Fin n → Fin N))
  rw [Finset.coe_univ, map_measureReal_apply (nm_measurable_prefix n) MeasurableSet.univ,
    preimage_univ, probReal_univ] at h
  rw [← h]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [nm_wordCylinder_ofFn, map_measureReal_apply (nm_measurable_prefix n)
    (MeasurableSet.of_discrete)]

/-- The cylinder `[w]` is the set of sequences that agree with `w` in the first `|w|` places. -/
private theorem nm_wordCylinder_eq (hN : 0 < N) (w : List (Fin N)) :
    wordCylinder w = {y | ∀ i < w.length, y i = w.getD i ⟨0, hN⟩} := by
  ext y
  simp only [wordCylinder, mem_ofPred_eq]
  constructor
  · intro h i hi
    rw [h ⟨i, hi⟩, List.getD_eq_getElem _ _ hi]
    rfl
  · intro h k
    rw [h k k.2, List.getD_eq_getElem _ _ k.2]
    rfl

private theorem nm_ofFn_getD (hN : 0 < N) (w : List (Fin N)) :
    (List.ofFn fun j : Fin w.length => w.getD j ⟨0, hN⟩) = w :=
  List.ext_getElem (by simp) fun l h1 h2 => by
    simp only [List.getElem_ofFn]
    exact List.getD_eq_getElem _ _ h2

/-! ### Distortion -/

private theorem nm_supDeriv_pos (hN : 0 < N) (w : List (Fin N)) : 0 < Φ.supDeriv w :=
  (pow_pos (Φ.cmin_pos hN) _).trans_le (Φ.cmin_pow_le_supDeriv w)

include Φ in
private theorem nm_mem_closure {x : ℝ} (hx : x ∈ I) : (x : ℂ) ∈ closure (nbhd ε) :=
  subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)

/-- `|log A - log B| ≤ |A - B| / c` for `A, B ≥ c > 0`. -/
private theorem nm_abs_log_sub_log_le {A B c : ℝ} (hc : 0 < c) (hA : c ≤ A) (hB : c ≤ B) :
    |Real.log A - Real.log B| ≤ |A - B| / c := by
  have key : ∀ {X Y : ℝ}, c ≤ X → c ≤ Y → Real.log X - Real.log Y ≤ |X - Y| / c := by
    intro X Y hX hY
    have hX0 := hc.trans_le hX
    have hY0 := hc.trans_le hY
    rw [← Real.log_div hX0.ne' hY0.ne']
    calc Real.log (X / Y) ≤ X / Y - 1 := Real.log_le_sub_one_of_pos (div_pos hX0 hY0)
      _ = (X - Y) / Y := by field_simp
      _ ≤ |X - Y| / Y := div_le_div_of_nonneg_right (le_abs_self _) hY0.le
      _ ≤ |X - Y| / c := div_le_div_of_nonneg_left (abs_nonneg _) hc hY
  rw [abs_le]
  constructor
  · have := key hB hA
    rw [abs_sub_comm] at this
    linarith
  · exact key hA hB

/-- `log |f_i'|` is Lipschitz on `I`, uniformly in `i`: `|f_i''| ≤ M` on `B_ε` and
`|f_i'| ≥ c_min`. -/
private theorem nm_exists_lip (hN : 0 < N) :
    ∃ L, 0 ≤ L ∧ ∀ i, ∀ a ∈ I, ∀ b ∈ I,
      |Real.log ‖deriv (Φ.f i) a‖ - Real.log ‖deriv (Φ.f i) b‖| ≤ L * |a - b| := by
  obtain ⟨M, hM0, hM⟩ := Φ.exists_nonlin_bound
  have hcmin := Φ.cmin_pos hN
  refine ⟨M / Φ.cmin, div_nonneg hM0 hcmin.le, fun i a ha b hb => ?_⟩
  have hd2 : ∀ z ∈ nbhd ε, ‖deriv (deriv (Φ.f i)) z‖ ≤ M := by
    intro z hz
    have hz' := subset_closure hz
    have h1 : deriv (deriv (Φ.f i)) z = Φ.nonlin i z * deriv (Φ.f i) z := by
      rw [nonlin, div_mul_cancel₀ _ ((Φ.inClass i).deriv_ne_zero z hz')]
    rw [h1, norm_mul]
    calc ‖Φ.nonlin i z‖ * ‖deriv (Φ.f i) z‖ ≤ M * 1 :=
          mul_le_mul (hM i z hz') ((Φ.inClass i).norm_deriv_lt_one z hz').le (norm_nonneg _)
            hM0
      _ = M := mul_one M
  have hdiff : ∀ z ∈ nbhd ε, DifferentiableAt ℂ (deriv (Φ.f i)) z := fun z hz =>
    ((Φ.differentiableOn_f i).deriv (isOpen_nbhd _) z (nbhd_subset_two hz)).differentiableAt
      ((isOpen_nbhd _).mem_nhds (nbhd_subset_two hz))
  have hmvt := (convex_nbhd ε).norm_image_sub_le_of_norm_deriv_le hdiff hd2
    (ofReal_mem_nbhd Φ.ε_pos hb) (ofReal_mem_nbhd Φ.ε_pos ha)
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hmvt
  refine (nm_abs_log_sub_log_le hcmin (Φ.cmin_le_norm_deriv i (Φ.nm_mem_closure ha))
    (Φ.cmin_le_norm_deriv i (Φ.nm_mem_closure hb))).trans ?_
  calc |‖deriv (Φ.f i) a‖ - ‖deriv (Φ.f i) b‖| / Φ.cmin ≤ M * |a - b| / Φ.cmin :=
        div_le_div_of_nonneg_right ((abs_norm_sub_norm_le _ _).trans hmvt) hcmin.le
    _ = M / Φ.cmin * |a - b| := by ring

/-- The two points `f_v(y), f_v(y')` for `y, y' ∈ I` are at distance at most `c_max^{|v|}`. -/
private theorem nm_abs_re_comp_sub_le (v : List (Fin N)) {y y' : ℝ} (hy : y ∈ I) (hy' : y' ∈ I) :
    |(Φ.comp v y).re - (Φ.comp v y').re| ≤ Φ.cmax ^ v.length := by
  have h := Φ.norm_comp_sub_le v (ofReal_mem_nbhd Φ.ε_pos hy) (ofReal_mem_nbhd Φ.ε_pos hy')
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  have hyy : |y - y'| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hy.1, hy.2, hy'.1, hy'.2]
  calc |(Φ.comp v y).re - (Φ.comp v y').re| = |(Φ.comp v y - Φ.comp v y').re| := by
        rw [Complex.sub_re]
    _ ≤ ‖Φ.comp v y - Φ.comp v y'‖ := Complex.abs_re_le_norm _
    _ ≤ Φ.cmax ^ v.length * |y - y'| := h
    _ ≤ Φ.cmax ^ v.length * 1 := mul_le_mul_of_nonneg_left hyy (pow_nonneg Φ.cmax_nonneg _)
    _ = Φ.cmax ^ v.length := mul_one _

/-- Bounded distortion along a word:
`|log |f_w'(y)| - log |f_w'(y')|| ≤ L ∑_{k < |w|} c_max^k` for `y, y' ∈ I`. -/
private theorem nm_log_deriv_comp_sub_le {L : ℝ}
    (hL : ∀ i, ∀ a ∈ I, ∀ b ∈ I,
      |Real.log ‖deriv (Φ.f i) a‖ - Real.log ‖deriv (Φ.f i) b‖| ≤ L * |a - b|)
    (hL0 : 0 ≤ L) (w : List (Fin N)) {y y' : ℝ} (hy : y ∈ I) (hy' : y' ∈ I) :
    |Real.log ‖deriv (Φ.comp w) y‖ - Real.log ‖deriv (Φ.comp w) y'‖| ≤
      L * ∑ k ∈ Finset.range w.length, Φ.cmax ^ k := by
  induction w with
  | nil => simp
  | cons i v ih =>
    have hz := Φ.nm_mem_closure hy
    have hz' := Φ.nm_mem_closure hy'
    have hne : ∀ {x : ℝ}, x ∈ I → ‖deriv (Φ.comp v) x‖ ≠ 0 := fun hx =>
      norm_ne_zero_iff.2 (Φ.deriv_comp_ne_zero v (Φ.nm_mem_closure hx))
    have hne' : ∀ {x : ℝ}, x ∈ I → ‖deriv (Φ.f i) ((Φ.comp v x).re : ℂ)‖ ≠ 0 := fun hx =>
      norm_ne_zero_iff.2 ((Φ.inClass i).deriv_ne_zero _
        (Φ.nm_mem_closure (Φ.re_comp_mem_I v hx)))
    rw [Φ.deriv_comp_cons i v hz, Φ.deriv_comp_cons i v hz', norm_mul, norm_mul,
      Φ.comp_ofReal v hy, Φ.comp_ofReal v hy', Real.log_mul (hne' hy) (hne hy),
      Real.log_mul (hne' hy') (hne hy'), List.length_cons, Finset.sum_range_succ]
    have h1 := hL i _ (Φ.re_comp_mem_I v hy) _ (Φ.re_comp_mem_I v hy')
    have h2 := Φ.nm_abs_re_comp_sub_le v hy hy'
    calc |Real.log ‖deriv (Φ.f i) ((Φ.comp v y).re : ℂ)‖ + Real.log ‖deriv (Φ.comp v) y‖ -
          (Real.log ‖deriv (Φ.f i) ((Φ.comp v y').re : ℂ)‖ +
            Real.log ‖deriv (Φ.comp v) y'‖)|
        ≤ |Real.log ‖deriv (Φ.f i) ((Φ.comp v y).re : ℂ)‖ -
            Real.log ‖deriv (Φ.f i) ((Φ.comp v y').re : ℂ)‖| +
          |Real.log ‖deriv (Φ.comp v) y‖ - Real.log ‖deriv (Φ.comp v) y'‖| := by
          rw [add_sub_add_comm]
          exact abs_add_le _ _
      _ ≤ L * Φ.cmax ^ v.length + L * ∑ k ∈ Finset.range v.length, Φ.cmax ^ k :=
          add_le_add (h1.trans (mul_le_mul_of_nonneg_left h2 hL0)) ih
      _ = L * (∑ k ∈ Finset.range v.length, Φ.cmax ^ k + Φ.cmax ^ v.length) := by ring

/-- Bounded distortion: `log ‖f_w'‖` and `log |f_w'(y)|` differ by at most a constant, for all
finite words `w` and `y ∈ I`. -/
private theorem nm_exists_distortion (hN : 0 < N) :
    ∃ Δ, 0 ≤ Δ ∧ ∀ (w : List (Fin N)) {y : ℝ}, y ∈ I →
      |Real.log (Φ.supDeriv w) - Real.log ‖deriv (Φ.comp w) y‖| ≤ Δ := by
  obtain ⟨L, hL0, hL⟩ := Φ.nm_exists_lip hN
  have hc1 : 0 < 1 - Φ.cmax := sub_pos.2 Φ.cmax_lt_one
  refine ⟨L / (1 - Φ.cmax), div_nonneg hL0 hc1.le, fun w y hy => ?_⟩
  have hpos : ∀ {x : ℝ}, x ∈ I → 0 < ‖deriv (Φ.comp w) x‖ := fun hx =>
    norm_pos_iff.2 (Φ.deriv_comp_ne_zero w (Φ.nm_mem_closure hx))
  have hgeom : ∑ k ∈ Finset.range w.length, Φ.cmax ^ k ≤ 1 / (1 - Φ.cmax) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := w.length) Φ.cmax_nonneg Φ.cmax_lt_one
    rwa [← Finset.range_eq_Ico, pow_zero] at this
  have hdist : ∀ {x : ℝ}, x ∈ I →
      Real.log ‖deriv (Φ.comp w) x‖ ≤ Real.log ‖deriv (Φ.comp w) y‖ + L / (1 - Φ.cmax) := by
    intro x hx
    have h := (le_abs_self _).trans (Φ.nm_log_deriv_comp_sub_le hL hL0 w hx hy)
    have h' : L * ∑ k ∈ Finset.range w.length, Φ.cmax ^ k ≤ L / (1 - Φ.cmax) := by
      calc L * ∑ k ∈ Finset.range w.length, Φ.cmax ^ k ≤ L * (1 / (1 - Φ.cmax)) :=
            mul_le_mul_of_nonneg_left hgeom hL0
        _ = L / (1 - Φ.cmax) := by ring
    linarith
  have hle : Φ.supDeriv w ≤ Real.exp (L / (1 - Φ.cmax)) * ‖deriv (Φ.comp w) y‖ := by
    have : Nonempty I := ⟨⟨0, le_rfl, zero_le_one⟩⟩
    refine ciSup_le fun x => ?_
    calc ‖deriv (Φ.comp w) ((x : ℝ) : ℂ)‖ = Real.exp (Real.log ‖deriv (Φ.comp w) ((x : ℝ) : ℂ)‖) :=
          (Real.exp_log (hpos x.2)).symm
      _ ≤ Real.exp (Real.log ‖deriv (Φ.comp w) y‖ + L / (1 - Φ.cmax)) :=
          Real.exp_le_exp.2 (hdist x.2)
      _ = Real.exp (L / (1 - Φ.cmax)) * ‖deriv (Φ.comp w) y‖ := by
          rw [Real.exp_add, Real.exp_log (hpos hy), mul_comm]
  have h1 : Real.log ‖deriv (Φ.comp w) y‖ ≤ Real.log (Φ.supDeriv w) :=
    Real.log_le_log (hpos hy) (Φ.norm_deriv_le_supDeriv w hy)
  have h2 : Real.log (Φ.supDeriv w) ≤ L / (1 - Φ.cmax) + Real.log ‖deriv (Φ.comp w) y‖ := by
    have := Real.log_le_log (Φ.nm_supDeriv_pos hN w) hle
    rwa [Real.log_mul (Real.exp_pos _).ne' (hpos hy).ne', Real.log_exp] at this
  rw [abs_le]
  constructor <;> linarith

/-! ### The natural projection and Birkhoff sums -/

/-- `f_{ω₁ ⋯ ω_k}(π(σ^k ω)) = π(ω)`, as complex numbers. -/
private theorem nm_comp_natProj (ω : ℕ → Fin N) (k : ℕ) :
    Φ.comp (List.ofFn fun j : Fin k => ω j) (Φ.natProj fun j => ω (j + k)) = Φ.natProj ω := by
  rw [Φ.comp_ofReal _ (Φ.attractor_subset_I ⟨_, rfl⟩), ← Φ.natProj_eq_comp_prefix]

/-- The Birkhoff sum of the potential: `∑_{k<m} φ_s(σ^k x) = s log |f_w'(π(σ^m x))|` with
`w = x₀ ⋯ x_{m-1}`. -/
private theorem nm_birkhoff (s : ℝ) (m : ℕ) (x : ℕ → Fin N) :
    ∑ k ∈ Finset.range m, Φ.potential s (fun i => x (i + k)) =
      s * Real.log ‖deriv (Φ.comp (List.ofFn fun j : Fin m => x j))
        (Φ.natProj fun i => x (i + m))‖ := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    have h1 : ∑ k ∈ Finset.range m, Φ.potential s (fun i => x (i + (k + 1))) =
        ∑ k ∈ Finset.range m, Φ.potential s (fun i => x (i + k + 1)) :=
      Finset.sum_congr rfl fun k _ => rfl
    have he : (fun i => x (i + (m + 1))) = fun i => x (i + m + 1) := rfl
    have hπ : Φ.natProj (fun i => x (i + m + 1)) ∈ I := Φ.attractor_subset_I ⟨_, rfl⟩
    have hz := Φ.nm_mem_closure hπ
    set v := List.ofFn fun j : Fin m => x (j + 1) with hv
    have hlist : (List.ofFn fun j : Fin (m + 1) => x j) = x 0 :: v := by
      rw [List.ofFn_succ]
      simp [hv]
    have hc : Φ.comp v (Φ.natProj fun i => x (i + m + 1)) = Φ.natProj fun i => x (i + 1) :=
      Φ.nm_comp_natProj (fun i => x (i + 1)) m
    have hpot : Φ.potential s (fun i => x (i + 0)) =
        s * Real.log ‖deriv (Φ.f (x 0)) (Φ.natProj fun i => x (i + 1))‖ := rfl
    rw [Finset.sum_range_succ', h1, ih (fun j => x (j + 1)), he, hlist,
      Φ.deriv_comp_cons _ _ hz, hc, hpot, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 ((Φ.inClass _).deriv_ne_zero _
        (Φ.nm_mem_closure (Φ.attractor_subset_I ⟨_, rfl⟩))))
        (norm_ne_zero_iff.2 (Φ.deriv_comp_ne_zero _ hz))]
    ring

/-- Bowen's theorem gives a Gibbs measure for the potential `s log|f'_{ω₀}(π(σω))|`. -/
theorem exists_isGibbsMeasure (hB : BowenGibbsStatement) (hN : 0 < N) (s : ℝ) :
    ∃ ν : Measure (ℕ → Fin N), IsProbabilityMeasure ν ∧ IsGibbsMeasure (Φ.potential s) ν := by
  obtain ⟨L, hL0, hL⟩ := Φ.nm_exists_lip hN
  have hcmin := Φ.cmin_pos hN
  have hcmax : 0 < Φ.cmax := hcmin.trans_le (Φ.cmin_le_cmax hN)
  have hlog : Real.log Φ.cmin ≤ Real.log Φ.cmax := Real.log_le_log hcmin (Φ.cmin_le_cmax hN)
  have hK : 0 ≤ L / Φ.cmax + (Real.log Φ.cmax - Real.log Φ.cmin) :=
    add_nonneg (div_nonneg hL0 hcmax.le) (sub_nonneg.2 hlog)
  set b := |s| * (L / Φ.cmax + (Real.log Φ.cmax - Real.log Φ.cmin)) + 1 with hb_def
  have hb : 0 < b := add_pos_of_nonneg_of_pos (mul_nonneg (abs_nonneg s) hK) one_pos
  refine hB hN (Φ.potential s) hb hcmax Φ.cmax_lt_one fun k x y hxy => ?_
  simp only [potential]
  rw [← mul_sub, abs_mul]
  have hx := Φ.attractor_subset_I ⟨fun i => x (i + 1), rfl⟩
  have hy := Φ.attractor_subset_I ⟨fun i => y (i + 1), rfl⟩
  rcases k with _ | k
  · -- no common prefix: `log |f_i'|` takes values in `[log c_min, log c_max]`
    have hbd : ∀ (i : Fin N) {t : ℝ}, t ∈ I → Real.log Φ.cmin ≤ Real.log ‖deriv (Φ.f i) t‖ ∧
        Real.log ‖deriv (Φ.f i) t‖ ≤ Real.log Φ.cmax := fun i t ht =>
      ⟨Real.log_le_log hcmin (Φ.cmin_le_norm_deriv i (Φ.nm_mem_closure ht)),
        Real.log_le_log (hcmin.trans_le (Φ.cmin_le_norm_deriv i (Φ.nm_mem_closure ht)))
          (Φ.norm_deriv_le_cmax i (Φ.nm_mem_closure ht))⟩
    obtain ⟨h1, h2⟩ := hbd (x 0) hx
    obtain ⟨h3, h4⟩ := hbd (y 0) hy
    have hd : |Real.log ‖deriv (Φ.f (x 0)) (Φ.natProj fun i => x (i + 1))‖ -
        Real.log ‖deriv (Φ.f (y 0)) (Φ.natProj fun i => y (i + 1))‖| ≤
        L / Φ.cmax + (Real.log Φ.cmax - Real.log Φ.cmin) := by
      have : 0 ≤ L / Φ.cmax := div_nonneg hL0 hcmax.le
      rw [abs_le]
      constructor <;> linarith
    rw [pow_zero, mul_one]
    have := mul_le_mul_of_nonneg_left hd (abs_nonneg s)
    linarith
  · -- a common prefix of length `k + 1`: the two points lie in `f_u(I)`, `|u| = k`
    have h0 : x 0 = y 0 := hxy 0 (Nat.succ_pos k)
    have hu : (List.ofFn fun j : Fin k => x (j + 1)) = List.ofFn fun j : Fin k => y (j + 1) := by
      congr 1
      funext j
      exact hxy _ (by omega)
    have hcx := Φ.nm_comp_natProj (fun i => x (i + 1)) k
    have hcy := Φ.nm_comp_natProj (fun i => y (i + 1)) k
    have hdist : |Φ.natProj (fun i => x (i + 1)) - Φ.natProj (fun i => y (i + 1))| ≤
        Φ.cmax ^ k := by
      have h := Φ.nm_abs_re_comp_sub_le (List.ofFn fun j : Fin k => x (j + 1))
        (Φ.attractor_subset_I ⟨fun j => x (j + k + 1), rfl⟩)
        (Φ.attractor_subset_I ⟨fun j => y (j + k + 1), rfl⟩)
      rw [List.length_ofFn] at h
      have e1 : (Φ.comp (List.ofFn fun j : Fin k => x (j + 1))
          (Φ.natProj fun j => x (j + k + 1))).re = Φ.natProj fun i => x (i + 1) := by
        rw [show (Φ.comp (List.ofFn fun j : Fin k => x (j + 1))
          (Φ.natProj fun j => x (j + k + 1))) = Φ.natProj fun i => x (i + 1) from hcx,
          Complex.ofReal_re]
      have e2 : (Φ.comp (List.ofFn fun j : Fin k => x (j + 1))
          (Φ.natProj fun j => y (j + k + 1))).re = Φ.natProj fun i => y (i + 1) := by
        rw [hu, show (Φ.comp (List.ofFn fun j : Fin k => y (j + 1))
          (Φ.natProj fun j => y (j + k + 1))) = Φ.natProj fun i => y (i + 1) from hcy,
          Complex.ofReal_re]
      rwa [e1, e2] at h
    have hd := (hL (x 0) _ hx _ hy).trans (mul_le_mul_of_nonneg_left hdist hL0)
    rw [← h0]
    have hb' : |s| * (L / Φ.cmax) ≤ b := by
      have : 0 ≤ |s| * (Real.log Φ.cmax - Real.log Φ.cmin) :=
        mul_nonneg (abs_nonneg s) (sub_nonneg.2 hlog)
      rw [hb_def]
      nlinarith [abs_nonneg s]
    calc |s| * |Real.log ‖deriv (Φ.f (x 0)) (Φ.natProj fun i => x (i + 1))‖ -
          Real.log ‖deriv (Φ.f (x 0)) (Φ.natProj fun i => y (i + 1))‖|
        ≤ |s| * (L * Φ.cmax ^ k) := mul_le_mul_of_nonneg_left hd (abs_nonneg s)
      _ = |s| * (L / Φ.cmax) * Φ.cmax ^ (k + 1) := by
          rw [pow_succ]
          field_simp
      _ ≤ b * Φ.cmax ^ (k + 1) := mul_le_mul_of_nonneg_right hb' (pow_nonneg hcmax.le _)

/-- A Gibbs measure of the potential `s log|f'_{ω₀}(π(σω))|`, for the zero `s` of the pressure, has
the Gibbs property `C⁻¹ ‖f_w'‖^s ≤ ν[w] ≤ C ‖f_w'‖^s`. -/
theorem isGibbs_of_isGibbsMeasure (hN : 0 < N) {s : ℝ}
    (hs : Tendsto (fun n : ℕ => Real.log (Φ.pressureSum s n) / n) atTop (𝓝 0))
    {ν : Measure (ℕ → Fin N)} [IsProbabilityMeasure ν] (hν : IsGibbsMeasure (Φ.potential s) ν) :
    Φ.IsGibbs s ν := by
  obtain ⟨c₁, hc₁, c₂, hc₂, P, hG⟩ := hν
  obtain ⟨Δ, hΔ0, hΔ⟩ := Φ.nm_exists_distortion hN
  set A := |s| * Δ with hA_def
  set K₁ := c₁ * Real.exp (-A) with hK₁_def
  set K₂ := c₂ * Real.exp A with hK₂_def
  have hK₁ : 0 < K₁ := mul_pos hc₁ (Real.exp_pos _)
  have hK₂ : 0 < K₂ := mul_pos hc₂ (Real.exp_pos _)
  -- `ν[w] ≍ exp(-P|w|) ‖f_w'‖^s`
  have key : ∀ w : List (Fin N),
      K₁ * Real.exp (-P * w.length) * Φ.supDeriv w ^ s ≤ ν.real (wordCylinder w) ∧
        ν.real (wordCylinder w) ≤ K₂ * Real.exp (-P * w.length) * Φ.supDeriv w ^ s := by
    intro w
    set x : ℕ → Fin N := fun i => w.getD i ⟨0, hN⟩ with hx_def
    obtain ⟨h1, h2⟩ := hG x w.length
    rw [← nm_wordCylinder_eq hN w, Φ.nm_birkhoff, nm_ofFn_getD hN w] at h1 h2
    have hπ : Φ.natProj (fun i => x (i + w.length)) ∈ I := Φ.attractor_subset_I ⟨_, rfl⟩
    have hd : |s * Real.log (Φ.supDeriv w) -
        s * Real.log ‖deriv (Φ.comp w) (Φ.natProj fun i => x (i + w.length))‖| ≤ A := by
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hΔ w hπ) (abs_nonneg s)
    rw [abs_le] at hd
    have hrpow : Φ.supDeriv w ^ s = Real.exp (s * Real.log (Φ.supDeriv w)) := by
      rw [Real.rpow_def_of_pos (Φ.nm_supDeriv_pos hN w), mul_comm]
    have e : ∀ c B : ℝ, c * Real.exp B * Real.exp (-P * w.length) * Φ.supDeriv w ^ s =
        c * Real.exp (-P * w.length + (s * Real.log (Φ.supDeriv w) + B)) := by
      intro c B
      rw [hrpow, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    constructor
    · rw [hK₁_def, e]
      refine le_trans ?_ h1
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hc₁.le
    · rw [hK₂_def, e]
      refine h2.trans ?_
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hc₂.le
  -- summing over the words of length `m`: `exp(-Pm) ∑_{|w| = m} ‖f_w'‖^s ≍ 1`
  have hps : ∀ m, 0 < Φ.pressureSum s m := fun m =>
    Finset.sum_pos (fun _ _ => Real.rpow_pos_of_pos (Φ.nm_supDeriv_pos hN _) s)
      ⟨fun _ => ⟨0, hN⟩, Finset.mem_univ _⟩
  have hsum : ∀ m : ℕ, K₁ * Real.exp (-P * m) * Φ.pressureSum s m ≤ 1 ∧
      1 ≤ K₂ * Real.exp (-P * m) * Φ.pressureSum s m := by
    intro m
    have h1 := nm_sum_measureReal_wordCylinder ν m
    constructor
    · rw [← h1, pressureSum, Finset.mul_sum]
      refine Finset.sum_le_sum fun v _ => ?_
      have := (key (List.ofFn v)).1
      rwa [List.length_ofFn] at this
    · rw [← h1, pressureSum, Finset.mul_sum]
      refine Finset.sum_le_sum fun v _ => ?_
      have := (key (List.ofFn v)).2
      rwa [List.length_ofFn] at this
  have hlog : ∀ m : ℕ, -Real.log K₂ ≤ Real.log (Φ.pressureSum s m) - P * m ∧
      Real.log (Φ.pressureSum s m) - P * m ≤ -Real.log K₁ := by
    intro m
    obtain ⟨h1, h2⟩ := hsum m
    have hpos : ∀ K : ℝ, 0 < K → 0 < K * Real.exp (-P * m) * Φ.pressureSum s m := fun K hK =>
      mul_pos (mul_pos hK (Real.exp_pos _)) (hps m)
    have hl : ∀ K : ℝ, 0 < K → Real.log (K * Real.exp (-P * m) * Φ.pressureSum s m) =
        Real.log K + -P * m + Real.log (Φ.pressureSum s m) := fun K hK => by
      rw [Real.log_mul (mul_pos hK (Real.exp_pos _)).ne' (hps m).ne',
        Real.log_mul hK.ne' (Real.exp_pos _).ne', Real.log_exp]
    have l1 := Real.log_le_log (hpos K₁ hK₁) h1
    have l2 := Real.log_le_log one_pos h2
    rw [hl K₁ hK₁, Real.log_one] at l1
    rw [hl K₂ hK₂, Real.log_one] at l2
    constructor <;> linarith
  -- hence `(1/m) log ∑_{|w| = m} ‖f_w'‖^s → P`, so `P = 0`
  have hlim : Tendsto (fun n : ℕ => Real.log (Φ.pressureSum s n) / n) atTop (𝓝 P) := by
    have hc : ∀ c : ℝ, Tendsto (fun n : ℕ => P + c / n) atTop (𝓝 P) := fun c => by
      simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat c)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hc (-Real.log K₂)) (hc (-Real.log K₁))
      ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [add_div' _ _ _ hn'.ne', div_le_div_iff_of_pos_right hn']
      linarith [(hlog n).1]
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [add_div' _ _ _ hn'.ne', div_le_div_iff_of_pos_right hn']
      linarith [(hlog n).2]
  have hP : P = 0 := tendsto_nhds_unique hlim hs
  -- the Gibbs property with `C = max(K₂, K₁⁻¹)`
  refine ⟨max K₂ K₁⁻¹, lt_max_of_lt_left hK₂, fun w => ?_⟩
  obtain ⟨h1, h2⟩ := key w
  rw [hP, neg_zero, zero_mul, Real.exp_zero, mul_one] at h1 h2
  have hw := Real.rpow_nonneg (Φ.nm_supDeriv_pos hN w).le s
  constructor
  · refine le_trans (mul_le_mul_of_nonneg_right ?_ hw) h1
    exact inv_le_of_inv_le₀ hK₁ (le_max_right _ _)
  · exact h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hw)

end IFS

/-- The remark at the end of Section 1.2.2, from Bowen's theorem: the pressure of the example has
a unique zero `s = s(Φ)`, the potential `s log|f'_{ω₀}(π(σω))|` has a Gibbs measure, and for every
such Gibbs measure `ν` the natural measure `ν ∘ π⁻¹` has local dimension `s(Φ) - 1/3` at `0`. -/
theorem example_localDim_of_bowen (hB : BowenGibbsStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (fun n : ℕ => Real.log (exampleIFS.pressureSum t n) / n) atTop (𝓝 0) ↔
        t = s) ∧
      (∃ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν ∧
        IsGibbsMeasure (exampleIFS.potential s) ν) ∧
      ∀ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν →
        IsGibbsMeasure (exampleIFS.potential s) ν →
        Tendsto (fun r => Real.log ((ν.map exampleIFS.natProj).real (closedBall 0 r)) / Real.log r)
          (𝓝[>] 0) (𝓝 (s - 1 / 3)) := by
  obtain ⟨s, -, hs⟩ := exampleIFS.exists_pressure_zero (by norm_num)
  refine ⟨s, hs, exampleIFS.exists_isGibbsMeasure hB (by norm_num) s, fun ν hν hG => ?_⟩
  exact (example_localDim (exampleIFS.isGibbs_of_isGibbsMeasure (by norm_num) ((hs s).2 rfl)
    hG)).2

end AnalyticESC
