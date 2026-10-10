module

public import AnalyticESC.Main.Example
public import AnalyticESC.Separation

@[expose] public section

/-!
# The local dimension of the natural measure of the polynomial example

The natural measure `μ = ν ∘ π⁻¹` of the polynomial example in Section 1.2.2, where
`ν` is the Gibbs measure of the potential `s(Φ) log|f'_{ω₁}(π(σω))|`, has local dimension
`s(Φ) - 1/3 < s(Φ)` at `0`.

The Gibbs measure is not constructed here. The results assume a probability measure `ν` on `Σ`
with the Gibbs property `C⁻¹ ‖f_w'‖^s ≤ ν[w] ≤ C ‖f_w'‖^s` for every finite word `w`, which Bowen's
theorem provides for `s = s(Φ)`. The Gibbs property determines `s`: the pressure
`P(t) = lim_n (1/n) log ∑_{w ∈ Σ_n} ‖f_w'‖^t` vanishes at `t = s` and at no other `t`.
-/

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory

/-- The cylinder `[w] = {ω ∈ Σ : ω₁ ⋯ ω_{|w|} = w}` of a finite word. -/
def wordCylinder {N : ℕ} (w : List (Fin N)) : Set (ℕ → Fin N) :=
  {ω | ∀ k : Fin w.length, ω k = w[k]}

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- `‖f_w'‖ = sup_{x ∈ [0,1]} |f_w'(x)|`. -/
noncomputable def supDeriv (w : List (Fin N)) : ℝ := ⨆ x : I, ‖deriv (Φ.comp w) x‖

/-- The sum `∑_{w ∈ Σ_n} ‖f_w'‖^t`, whose exponential growth rate is the pressure `P(t)`. -/
noncomputable def pressureSum (t : ℝ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → Fin N, Φ.supDeriv (List.ofFn w) ^ t

/-- `ν` has the Gibbs property for the potential `s log|f'|`: `ν[w]` is comparable to `‖f_w'‖^s`,
uniformly over finite words `w`. -/
def IsGibbs (s : ℝ) (ν : Measure (ℕ → Fin N)) : Prop :=
  ∃ C > 0, ∀ w : List (Fin N),
    C⁻¹ * Φ.supDeriv w ^ s ≤ ν.real (wordCylinder w) ∧
      ν.real (wordCylinder w) ≤ C * Φ.supDeriv w ^ s

/-- The prefix map `ω ↦ ω₁ ⋯ ωₙ` is measurable. -/
private theorem measurable_prefix (n : ℕ) : Measurable fun (ω : ℕ → Fin N) (k : Fin n) => ω k :=
  Measurable.of_eval fun k => measurable_pi_apply (k : ℕ)

/-- The natural projection is measurable, so `ν ∘ π⁻¹` is the image measure of `ν`. -/
theorem measurable_natProj : Measurable Φ.natProj :=
  measurable_of_tendsto_metrizable
    (f := fun n ω => (Φ.comp (List.ofFn fun k : Fin n => ω k) 0).re)
    (fun n => (measurable_of_finite fun v : Fin n → Fin N => (Φ.comp (List.ofFn v) 0).re).comp
      (measurable_prefix n))
    (tendsto_pi_nhds.2 Φ.tendsto_natProj)

/-- The cylinder of a word of length `n` is the preimage of the word under the prefix map. -/
private theorem wordCylinder_ofFn {n : ℕ} (v : Fin n → Fin N) :
    wordCylinder (List.ofFn v) = (fun (ω : ℕ → Fin N) (k : Fin n) => ω k) ⁻¹' {v} := by
  ext ω
  simp only [wordCylinder, mem_ofPred_eq, mem_preimage, mem_singleton_iff, funext_iff]
  constructor
  · intro h k
    simpa using h ⟨k, by simp⟩
  · intro h k
    simpa using h ⟨k, by simpa using k.2⟩

/-- The measure of the set of infinite words whose prefix of length `n` lies in `S` is the sum of
the measures of the cylinders of the words in `S`. -/
private theorem sum_measureReal_wordCylinder (ν : Measure (ℕ → Fin N)) [IsFiniteMeasure ν] (n : ℕ)
    (S : Finset (Fin n → Fin N)) :
    ∑ v ∈ S, ν.real (wordCylinder (List.ofFn v)) =
      ν.real ((fun (ω : ℕ → Fin N) (k : Fin n) => ω k) ⁻¹' ↑S) := by
  rw [← map_measureReal_apply (measurable_prefix n) (MeasurableSet.of_discrete),
    ← sum_measureReal_singleton]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [wordCylinder_ofFn, map_measureReal_apply (measurable_prefix n) (MeasurableSet.of_discrete)]

/-- The cylinders of the words of length `n` have total measure `1`. -/
private theorem sum_measureReal_wordCylinder_univ (ν : Measure (ℕ → Fin N))
    [IsProbabilityMeasure ν] (n : ℕ) :
    ∑ v : Fin n → Fin N, ν.real (wordCylinder (List.ofFn v)) = 1 := by
  rw [sum_measureReal_wordCylinder, Finset.coe_univ, preimage_univ, probReal_univ]

private theorem bddAbove_norm_deriv_comp (w : List (Fin N)) :
    BddAbove (range fun x : I => ‖deriv (Φ.comp w) ((x : ℝ) : ℂ)‖) :=
  ⟨Φ.cmax ^ w.length, by
    rintro _ ⟨x, rfl⟩
    exact Φ.norm_deriv_comp_le w (subset_closure (ofReal_mem_nbhd Φ.ε_pos x.2))⟩

/-- `|f_w'(x)| ≤ ‖f_w'‖` for `x ∈ [0,1]`. -/
theorem norm_deriv_le_supDeriv (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    ‖deriv (Φ.comp w) x‖ ≤ Φ.supDeriv w :=
  le_ciSup (f := fun x : I => ‖deriv (Φ.comp w) ((x : ℝ) : ℂ)‖) (Φ.bddAbove_norm_deriv_comp w)
    ⟨x, hx⟩

/-- `‖f_w'‖ ≤ c_max^{|w|}`. -/
theorem supDeriv_le (w : List (Fin N)) : Φ.supDeriv w ≤ Φ.cmax ^ w.length := by
  have : Nonempty I := ⟨⟨0, le_rfl, zero_le_one⟩⟩
  exact ciSup_le fun x => Φ.norm_deriv_comp_le w (subset_closure (ofReal_mem_nbhd Φ.ε_pos x.2))

/-- `c_min^{|w|} ≤ ‖f_w'‖`. -/
theorem cmin_pow_le_supDeriv (w : List (Fin N)) : Φ.cmin ^ w.length ≤ Φ.supDeriv w :=
  (Φ.cmin_pow_le_norm_deriv_comp w
    (subset_closure (ofReal_mem_nbhd Φ.ε_pos (left_mem_Icc.2 zero_le_one)))).trans
    (Φ.norm_deriv_le_supDeriv w (left_mem_Icc.2 zero_le_one))

/-- The Gibbs property determines the exponent: the pressure `P(t)` exists and vanishes exactly
for `t = s`, so `s = s(Φ)`. -/
theorem tendsto_pressure_iff_of_isGibbs (hN : 0 < N) {s : ℝ} {ν : Measure (ℕ → Fin N)}
    [IsProbabilityMeasure ν] (hν : Φ.IsGibbs s ν) (t : ℝ) :
    Tendsto (fun n : ℕ => Real.log (Φ.pressureSum t n) / n) atTop (𝓝 0) ↔ t = s := by
  obtain ⟨C, hC, hG⟩ := hν
  have hcmin := Φ.cmin_pos hN
  have hcmax : 0 < Φ.cmax := hcmin.trans_le (Φ.cmin_le_cmax hN)
  set L := Real.log Φ.cmax with hL_def
  have hL : L < 0 := Real.log_neg hcmax Φ.cmax_lt_one
  have hpos : ∀ w, 0 < Φ.supDeriv w := fun w =>
    (pow_pos hcmin _).trans_le (Φ.cmin_pow_le_supDeriv w)
  have hlog : ∀ n (v : Fin n → Fin N), Real.log (Φ.supDeriv (List.ofFn v)) ≤ n * L := by
    intro n v
    have h := Real.log_le_log (hpos _) (Φ.supDeriv_le (List.ofFn v))
    rwa [List.length_ofFn, Real.log_pow] at h
  have hne : ∀ n, (Finset.univ : Finset (Fin n → Fin N)).Nonempty := fun n =>
    ⟨fun _ => ⟨0, hN⟩, Finset.mem_univ _⟩
  have hP : ∀ t n, 0 < Φ.pressureSum t n := fun t n =>
    Finset.sum_pos (fun v _ => Real.rpow_pos_of_pos (hpos _) t) (hne n)
  -- the Gibbs property and `∑_w ν[w] = 1` give `C⁻¹ ≤ P_n(s) ≤ C`
  have hPs : ∀ n, Φ.pressureSum s n ≤ C ∧ C⁻¹ ≤ Φ.pressureSum s n := by
    intro n
    have h1 := sum_measureReal_wordCylinder_univ ν n
    have hle : C⁻¹ * Φ.pressureSum s n ≤ 1 := by
      rw [← h1, pressureSum, Finset.mul_sum]
      exact Finset.sum_le_sum fun v _ => (hG _).1
    have hge : 1 ≤ C * Φ.pressureSum s n := by
      rw [← h1, pressureSum, Finset.mul_sum]
      exact Finset.sum_le_sum fun v _ => (hG _).2
    constructor
    · rwa [inv_mul_le_iff₀ hC, mul_one] at hle
    · rwa [inv_le_iff_one_le_mul₀ hC, mul_comm]
  -- `‖f_w'‖^t = ‖f_w'‖^s ⋅ exp((t - s) log ‖f_w'‖)`
  have hterm : ∀ w, Φ.supDeriv w ^ t =
      Φ.supDeriv w ^ s * Real.exp (Real.log (Φ.supDeriv w) * (t - s)) := by
    intro w
    rw [← Real.rpow_def_of_pos (hpos w), ← Real.rpow_add (hpos w), add_sub_cancel]
  have hup : s ≤ t → ∀ n, Real.log (Φ.pressureSum t n) ≤ Real.log C + n * ((t - s) * L) := by
    intro hst n
    have h : Φ.pressureSum t n ≤ C * Real.exp (n * ((t - s) * L)) := by
      calc Φ.pressureSum t n
          ≤ Φ.pressureSum s n * Real.exp (n * ((t - s) * L)) := by
            rw [pressureSum, pressureSum, Finset.sum_mul]
            refine Finset.sum_le_sum fun v _ => ?_
            rw [hterm]
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
              (Real.rpow_nonneg (hpos _).le _)
            have := mul_le_mul_of_nonneg_right (hlog n v) (sub_nonneg.2 hst)
            linarith
        _ ≤ C * Real.exp (n * ((t - s) * L)) :=
            mul_le_mul_of_nonneg_right (hPs n).1 (Real.exp_pos _).le
    calc Real.log (Φ.pressureSum t n) ≤ Real.log (C * Real.exp (n * ((t - s) * L))) :=
          Real.log_le_log (hP t n) h
      _ = Real.log C + n * ((t - s) * L) := by
          rw [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hlow : t ≤ s → ∀ n, -Real.log C + n * ((t - s) * L) ≤ Real.log (Φ.pressureSum t n) := by
    intro hst n
    have h : C⁻¹ * Real.exp (n * ((t - s) * L)) ≤ Φ.pressureSum t n := by
      calc C⁻¹ * Real.exp (n * ((t - s) * L))
          ≤ Φ.pressureSum s n * Real.exp (n * ((t - s) * L)) :=
            mul_le_mul_of_nonneg_right (hPs n).2 (Real.exp_pos _).le
        _ ≤ Φ.pressureSum t n := by
            rw [pressureSum, pressureSum, Finset.sum_mul]
            refine Finset.sum_le_sum fun v _ => ?_
            rw [hterm]
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
              (Real.rpow_nonneg (hpos _).le _)
            have := mul_le_mul_of_nonpos_right (hlog n v) (sub_nonpos.2 hst)
            linarith
    calc -Real.log C + n * ((t - s) * L) = Real.log (C⁻¹ * Real.exp (n * ((t - s) * L))) := by
          rw [Real.log_mul (inv_ne_zero hC.ne') (Real.exp_pos _).ne', Real.log_exp,
            Real.log_inv]
      _ ≤ Real.log (Φ.pressureSum t n) :=
          Real.log_le_log (mul_pos (inv_pos.2 hC) (Real.exp_pos _)) h
  -- dividing by `n`
  have hdiv : ∀ {a b : ℝ} {n : ℕ}, 1 ≤ n → a ≤ b + n * ((t - s) * L) →
      a / n ≤ b / n + (t - s) * L := by
    intro a b n hn h
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_add' _ _ _ hn'.ne', div_le_div_iff_of_pos_right hn']
    linarith
  have hdiv' : ∀ {a b : ℝ} {n : ℕ}, 1 ≤ n → b + n * ((t - s) * L) ≤ a →
      b / n + (t - s) * L ≤ a / n := by
    intro a b n hn h
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_add' _ _ _ hn'.ne', div_le_div_iff_of_pos_right hn']
    linarith
  have hlim : ∀ b : ℝ, Tendsto (fun n : ℕ => b / n + (t - s) * L) atTop (𝓝 ((t - s) * L)) :=
    fun b => by simpa using (tendsto_const_div_atTop_nhds_zero_nat b).add_const ((t - s) * L)
  constructor
  · intro h
    by_contra hts
    rcases lt_or_gt_of_ne hts with hts | hts
    · have h1 : (t - s) * L ≤ 0 := le_of_tendsto_of_tendsto (hlim _) h
        (eventually_atTop.2 ⟨1, fun n hn => hdiv' hn (hlow hts.le n)⟩)
      nlinarith
    · have h1 : 0 ≤ (t - s) * L := le_of_tendsto_of_tendsto h (hlim _)
        (eventually_atTop.2 ⟨1, fun n hn => hdiv hn (hup hts.le n)⟩)
      nlinarith
  · rintro rfl
    rw [show (0 : ℝ) = (t - t) * L by ring]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim (-Real.log C)) (hlim (Real.log C))
      ?_ ?_
    · exact eventually_atTop.2 ⟨1, fun n hn => hdiv' hn (hlow le_rfl n)⟩
    · exact eventually_atTop.2 ⟨1, fun n hn => hdiv hn (hup le_rfl n)⟩

/-- `π(ω) = f_{ω₁ ⋯ ω_k}(π(σ^k ω))`, where `σ` is the left shift. -/
theorem natProj_eq_comp_prefix (ω : ℕ → Fin N) (k : ℕ) :
    Φ.natProj ω =
      (Φ.comp (List.ofFn fun j : Fin k => ω j) (Φ.natProj fun j => ω (j + k))).re := by
  set v : ℕ → Fin N := fun j => ω (j + k)
  set a := List.ofFn fun j : Fin k => ω j
  have hlist : ∀ n, (List.ofFn fun j : Fin (n + k) => ω j) =
      a ++ List.ofFn fun j : Fin n => v j := fun n =>
    List.ext_getElem (by simp [a, Nat.add_comm]) fun l h1 h2 => by
      rw [List.getElem_append]
      split_ifs with h
      · simp [a]
      · simp only [a, List.length_ofFn] at h
        simp only [List.getElem_ofFn, v, a, List.length_ofFn]
        congr
        omega
  have hπ : Φ.natProj v ∈ I := Φ.attractor_subset_I ⟨v, rfl⟩
  have hc : ContinuousAt (fun t : ℝ => (Φ.comp a t).re) (Φ.natProj v) :=
    Complex.continuous_re.continuousAt.comp ((Φ.differentiableAt_comp a
      (subset_closure (ofReal_mem_nbhd Φ.ε_pos hπ))).continuousAt.comp
      Complex.continuous_ofReal.continuousAt)
  refine tendsto_nhds_unique ((tendsto_add_atTop_iff_nat k).2 (Φ.tendsto_natProj ω)) ?_
  refine (hc.tendsto.comp (Φ.tendsto_natProj v)).congr fun n => ?_
  rw [Function.comp_apply, hlist n, Φ.comp_append, Function.comp_apply, ← Complex.ofReal_zero,
    ← Φ.comp_ofReal _ (left_mem_Icc.2 zero_le_one)]

end IFS

/-! ### The local dimension: an analytic lemma -/

/-- If `a ρ^n ≤ m(r) ≤ b ρ^n` whenever `λ^{n+2} < r ≤ λ^{n+1}`, then
`log m(r) / log r → log ρ / log λ` as `r → 0⁺`. -/
private theorem tendsto_log_div_log_of_bounds {m : ℝ → ℝ} {lam ρ a b : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (hρ : 0 < ρ) (ha : 0 < a) (hb : 0 < b)
    (h : ∀ (n : ℕ) (r : ℝ), lam ^ (n + 2) < r → r ≤ lam ^ (n + 1) →
      a * ρ ^ n ≤ m r ∧ m r ≤ b * ρ ^ n) :
    Tendsto (fun r => Real.log (m r) / Real.log r) (𝓝[>] 0)
      (𝓝 (Real.log ρ / Real.log lam)) := by
  set d := Real.log ρ / Real.log lam
  set K := |Real.log a| + |Real.log b| + 2 * |Real.log ρ|
  have hL : Real.log lam < 0 := Real.log_neg hlam0 hlam1
  have hbound : ∀ r, 0 < r → r < lam → |Real.log (m r) - d * Real.log r| ≤ K := by
    intro r hr0 hr
    obtain ⟨k, hk1, hk2⟩ :=
      exists_nat_pow_near_of_lt_one hr0 (hr.le.trans hlam1.le) hlam0 hlam1
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := by
      rcases k with _ | n
      · rw [zero_add, pow_one] at hk1
        linarith
      · exact ⟨n, rfl⟩
    obtain ⟨h1, h2⟩ := h n r hk1 hk2
    have hρn := pow_pos hρ n
    have hm : 0 < m r := (mul_pos ha hρn).trans_le h1
    have hl1 : Real.log a + n * Real.log ρ ≤ Real.log (m r) := by
      have := Real.log_le_log (mul_pos ha hρn) h1
      rwa [Real.log_mul ha.ne' hρn.ne', Real.log_pow] at this
    have hl2 : Real.log (m r) ≤ Real.log b + n * Real.log ρ := by
      have := Real.log_le_log hm h2
      rwa [Real.log_mul hb.ne' hρn.ne', Real.log_pow] at this
    have hr1 : (n + 2) * Real.log lam < Real.log r := by
      have := Real.log_lt_log (pow_pos hlam0 _) hk1
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    have hr2 : Real.log r ≤ (n + 1) * Real.log lam := by
      have := Real.log_le_log hr0 hk2
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    set t := Real.log r / Real.log lam
    have ht1 : n + 1 ≤ t := by
      rw [le_div_iff_of_neg hL]
      linarith
    have ht2 : t ≤ n + 2 := by
      rw [div_le_iff_of_neg hL]
      linarith
    have hdr : d * Real.log r = Real.log ρ * t := by
      simp only [d, t]
      ring
    rw [hdr, show Real.log (m r) - Real.log ρ * t =
      (Real.log (m r) - n * Real.log ρ) + (n - t) * Real.log ρ by ring]
    refine (abs_add_le _ _).trans ?_
    have hA : |Real.log (m r) - n * Real.log ρ| ≤ |Real.log a| + |Real.log b| := by
      rw [abs_le]
      constructor <;> linarith [neg_abs_le (Real.log a), le_abs_self (Real.log b),
        abs_nonneg (Real.log a), abs_nonneg (Real.log b)]
    have hB : |(n - t) * Real.log ρ| ≤ 2 * |Real.log ρ| := by
      rw [abs_mul]
      gcongr
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hK : Tendsto (fun r => K / |Real.log r|) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_abs_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hK
  filter_upwards [Ioo_mem_nhdsGT hlam0] with r hr
  have hlr : Real.log r ≠ 0 := (Real.log_neg hr.1 (hr.2.trans hlam1)).ne
  rw [Real.norm_eq_abs, show Real.log (m r) / Real.log r - d =
    (Real.log (m r) - d * Real.log r) / Real.log r by field_simp, abs_div]
  exact div_le_div_of_nonneg_right (hbound r hr.1 hr.2) (abs_nonneg _)

/-! ### The local dimension: the maps `f₁` and `f₂` of the example

The Lean letters `0, 1, 2` index the maps `f₁, f₂, f₃` of the paper. Words over the letters `0, 1`
are the words `w` with `i ≠ 2` for every letter `i` of `w`. -/

private theorem ld_fin_three (i : Fin 3) (hi : i ≠ 2) : i = 0 ∨ i = 1 := by
  revert i
  decide

/-- For the letters `i = 0, 1` and real `x`, `f_i(x)` is real with
`x/8 ≤ f_i(x) ≤ x/8 + x²/32`. -/
private theorem ld_f_ofReal (i : Fin 3) (hi : i ≠ 2) (x : ℝ) :
    ∃ y : ℝ, exampleIFS.f i x = y ∧ x / 8 ≤ y ∧ y ≤ x / 8 + x ^ 2 / 32 := by
  rcases ld_fin_three i hi with rfl | rfl
  · refine ⟨x / 8, ?_, le_rfl, by nlinarith⟩
    change (x : ℂ) / 8 = _
    push_cast
    ring
  · refine ⟨x / 8 + x ^ 2 / 32, ?_, by nlinarith, le_rfl⟩
    change (x : ℂ) / 8 + (x : ℂ) ^ 2 / 32 = _
    push_cast
    ring

private theorem ld_f_two_ofReal (x : ℝ) :
    exampleIFS.f 2 x = ((x / 16 + x ^ 2 / 32 + 29 / 32 : ℝ) : ℂ) := by
  change (x : ℂ) / 16 + (x : ℂ) ^ 2 / 32 + 29 / 32 = _
  push_cast
  ring

private theorem ld_f_zero (i : Fin 3) (hi : i ≠ 2) : exampleIFS.f i 0 = 0 := by
  rcases ld_fin_three i hi with rfl | rfl
  · change (0 : ℂ) / 8 = 0
    simp
  · change (0 : ℂ) / 8 + 0 ^ 2 / 32 = 0
    simp

private theorem ld_hasDerivAt_zero (z : ℂ) : HasDerivAt (exampleIFS.f 0) (1 / 8) z := by
  change HasDerivAt (fun z : ℂ => z / 8) _ z
  exact (hasDerivAt_id' z).div_const 8

private theorem ld_hasDerivAt_one (z : ℂ) : HasDerivAt (exampleIFS.f 1) (1 / 8 + z / 16) z := by
  change HasDerivAt (fun z : ℂ => z / 8 + z ^ 2 / 32) _ z
  have h := ((hasDerivAt_id' z).div_const 8).add ((hasDerivAt_pow 2 z).div_const 32)
  convert h using 1
  push_cast
  ring

private theorem ld_deriv_f_zero (i : Fin 3) (hi : i ≠ 2) : deriv (exampleIFS.f i) 0 = 1 / 8 := by
  rcases ld_fin_three i hi with rfl | rfl
  · exact (ld_hasDerivAt_zero 0).deriv
  · rw [(ld_hasDerivAt_one 0).deriv]
    norm_num

private theorem ld_norm_deriv_f_le (i : Fin 3) (hi : i ≠ 2) {x : ℝ} (hx : 0 ≤ x) :
    ‖deriv (exampleIFS.f i) x‖ ≤ 1 / 8 + x / 16 := by
  rcases ld_fin_three i hi with rfl | rfl
  · rw [(ld_hasDerivAt_zero _).deriv]
    norm_num
    positivity
  · rw [(ld_hasDerivAt_one _).deriv, show (1 / 8 : ℂ) + (x : ℂ) / 16 = ((1 / 8 + x / 16 : ℝ) : ℂ)
      by push_cast; ring, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-! ### The local dimension: compositions of `f₁` and `f₂` -/

private theorem ld_comp_zero {w : List (Fin 3)} (hw : ∀ i ∈ w, i ≠ 2) :
    exampleIFS.comp w 0 = 0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [IFS.comp_cons, Function.comp_apply, ih fun j hj => hw j (List.mem_cons_of_mem i hj),
      ld_f_zero i (hw i List.mem_cons_self)]

private theorem ld_deriv_comp_zero {w : List (Fin 3)} (hw : ∀ i ∈ w, i ≠ 2) :
    deriv (exampleIFS.comp w) 0 = (1 / 8 : ℂ) ^ w.length := by
  induction w with
  | nil => simp [deriv_id]
  | cons i w ih =>
    have hw' : ∀ j ∈ w, j ≠ 2 := fun j hj => hw j (List.mem_cons_of_mem i hj)
    rw [exampleIFS.deriv_comp_cons i w (zero_mem_closure_nbhd (by norm_num)), ld_comp_zero hw',
      ih hw', ld_deriv_f_zero i (hw i List.mem_cons_self), List.length_cons, pow_succ']

/-- `8^{-|w|} x ≤ f_w(x)` for words `w` over the letters `0, 1` and `x ∈ [0,1]`. -/
private theorem ld_le_re_comp {w : List (Fin 3)} (hw : ∀ i ∈ w, i ≠ 2) {x : ℝ} (hx : x ∈ I) :
    (1 / 8 : ℝ) ^ w.length * x ≤ (exampleIFS.comp w x).re := by
  induction w with
  | nil => simp
  | cons i w ih =>
    have hw' : ∀ j ∈ w, j ≠ 2 := fun j hj => hw j (List.mem_cons_of_mem i hj)
    have hy := exampleIFS.re_comp_mem_I w hx
    obtain ⟨y, hy', h1, -⟩ := ld_f_ofReal i (hw i List.mem_cons_self) _
    have := ih hw'
    rw [IFS.comp_cons, Function.comp_apply, exampleIFS.comp_ofReal w hx, hy', Complex.ofReal_re,
      List.length_cons, pow_succ]
    nlinarith

/-- `f_w(x) ≤ 8^{-|w|} x (1 + x)` for words `w` over the letters `0, 1` and `x ∈ [0,1]`. -/
private theorem ld_re_comp_le {w : List (Fin 3)} (hw : ∀ i ∈ w, i ≠ 2) {x : ℝ} (hx : x ∈ I) :
    (exampleIFS.comp w x).re ≤ (1 / 8 : ℝ) ^ w.length * (x * (1 + x)) := by
  induction w using List.reverseRecOn generalizing x with
  | nil =>
    simp only [IFS.comp_nil, id, Complex.ofReal_re, List.length_nil, pow_zero, one_mul]
    nlinarith [hx.1]
  | append_singleton u i ih =>
    have hu : ∀ j ∈ u, j ≠ 2 := fun j hj => hw j (List.mem_append_left _ hj)
    have hi : i ≠ 2 := hw i (List.mem_append_right _ (List.mem_singleton_self i))
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨y, hy, h1, h2⟩ := ld_f_ofReal i hi x
    have hy0 : 0 ≤ y := by linarith
    have hyI : y ∈ I := ⟨hy0, by nlinarith⟩
    have hc : exampleIFS.comp [i] = exampleIFS.f i := rfl
    rw [exampleIFS.comp_append, Function.comp_apply, hc, hy, List.length_append,
      List.length_singleton, pow_succ]
    have hyy : y * (1 + y) ≤ 1 / 8 * (x * (1 + x)) := by
      have h3 : y * (1 + y) ≤ (x / 8 + x ^ 2 / 32) * (1 + (x / 8 + x ^ 2 / 32)) :=
        mul_le_mul h2 (by linarith) (by linarith) (by positivity)
      have h4 : x ^ 2 ≤ x := by nlinarith
      have h5 : x ^ 3 ≤ x ^ 2 := by nlinarith
      have h6 : x ^ 4 ≤ x ^ 3 := by nlinarith
      nlinarith
    calc (exampleIFS.comp u y).re ≤ (1 / 8) ^ u.length * (y * (1 + y)) := ih hu hyI
      _ ≤ (1 / 8) ^ u.length * (1 / 8 * (x * (1 + x))) := by gcongr
      _ = (1 / 8) ^ u.length * (1 / 8) * (x * (1 + x)) := by ring

/-- `|f_w'(x)| ≤ 8^{-|w|} (1 + x)` for words `w` over the letters `0, 1` and `x ∈ [0,1]`. -/
private theorem ld_norm_deriv_comp_le {w : List (Fin 3)} (hw : ∀ i ∈ w, i ≠ 2) {x : ℝ}
    (hx : x ∈ I) : ‖deriv (exampleIFS.comp w) x‖ ≤ (1 / 8 : ℝ) ^ w.length * (1 + x) := by
  induction w using List.reverseRecOn generalizing x with
  | nil =>
    simp only [IFS.comp_nil, deriv_id, norm_one, List.length_nil, pow_zero, one_mul]
    linarith [hx.1]
  | append_singleton u i ih =>
    have hu : ∀ j ∈ u, j ≠ 2 := fun j hj => hw j (List.mem_append_left _ hj)
    have hi : i ≠ 2 := hw i (List.mem_append_right _ (List.mem_singleton_self i))
    have hz : (x : ℂ) ∈ closure (nbhd (1 / 100)) :=
      subset_closure (ofReal_mem_nbhd (by norm_num) hx)
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨y, hy, h1, h2⟩ := ld_f_ofReal i hi x
    have hy0 : 0 ≤ y := by linarith
    have hyI : y ∈ I := ⟨hy0, by nlinarith⟩
    have hc : exampleIFS.comp [i] = exampleIFS.f i := rfl
    rw [exampleIFS.deriv_comp_append u [i] hz, hc, hy, norm_mul, List.length_append,
      List.length_singleton, pow_succ]
    have h3 := ih hu hyI
    have h4 := ld_norm_deriv_f_le i hi hx0
    have hpow : (0 : ℝ) ≤ (1 / 8) ^ u.length := by positivity
    calc ‖deriv (exampleIFS.comp u) y‖ * ‖deriv (exampleIFS.f i) x‖
        ≤ ((1 / 8) ^ u.length * (1 + y)) * (1 / 8 + x / 16) :=
          mul_le_mul h3 h4 (norm_nonneg _) (by positivity)
      _ ≤ ((1 / 8) ^ u.length * (1 + (x / 8 + x ^ 2 / 32))) * (1 / 8 + x / 16) := by gcongr
      _ ≤ (1 / 8) ^ u.length * (1 / 8) * (1 + x) := by
          have h5 : (1 + (x / 8 + x ^ 2 / 32)) * (1 / 8 + x / 16) ≤ 1 / 8 * (1 + x) := by
            nlinarith
          calc ((1 / 8) ^ u.length * (1 + (x / 8 + x ^ 2 / 32))) * (1 / 8 + x / 16)
              = (1 / 8) ^ u.length * ((1 + (x / 8 + x ^ 2 / 32)) * (1 / 8 + x / 16)) := by ring
            _ ≤ (1 / 8) ^ u.length * (1 / 8 * (1 + x)) := by gcongr
            _ = _ := by ring

/-- `8^{-|w|} ≤ ‖f_w'‖ ≤ 2 ⋅ 8^{-|w|}` for words `w` over the letters `0, 1`. -/
private theorem ld_supDeriv_bounds {w : List (Fin 3)} (hw : ∀ i ∈ w, i ≠ 2) :
    (1 / 8 : ℝ) ^ w.length ≤ exampleIFS.supDeriv w ∧
      exampleIFS.supDeriv w ≤ 2 * (1 / 8 : ℝ) ^ w.length := by
  constructor
  · have h := exampleIFS.norm_deriv_le_supDeriv w (x := 0) (left_mem_Icc.2 zero_le_one)
    rwa [Complex.ofReal_zero, ld_deriv_comp_zero hw, norm_pow, norm_div, norm_one,
      Complex.norm_ofNat] at h
  · have : Nonempty I := ⟨⟨0, le_rfl, zero_le_one⟩⟩
    refine ciSup_le fun x => (ld_norm_deriv_comp_le hw x.2).trans ?_
    have hpow : (0 : ℝ) ≤ (1 / 8) ^ w.length := by positivity
    nlinarith [x.2.2]

/-- If `y ≤ x ≤ 2y`, then `x^s` is comparable to `y^s` for every real `s`. -/
private theorem ld_rpow_bounds {x y : ℝ} (s : ℝ) (hy : 0 < y) (h1 : y ≤ x) (h2 : x ≤ 2 * y) :
    min 1 (2 ^ s) * y ^ s ≤ x ^ s ∧ x ^ s ≤ max 1 (2 ^ s) * y ^ s := by
  have hx : 0 < x := hy.trans_le h1
  have h2y : (2 * y) ^ s = 2 ^ s * y ^ s := Real.mul_rpow (by norm_num) hy.le
  have hys := Real.rpow_nonneg hy.le s
  rcases le_total 0 s with hs | hs
  · have ha := Real.rpow_le_rpow hy.le h1 hs
    have hb := Real.rpow_le_rpow hx.le h2 hs
    rw [h2y] at hb
    constructor
    · calc min 1 (2 ^ s) * y ^ s ≤ 1 * y ^ s := mul_le_mul_of_nonneg_right (min_le_left _ _) hys
        _ ≤ x ^ s := by rw [one_mul]; exact ha
    · exact hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hys)
  · have ha := Real.rpow_le_rpow_of_nonpos hy h1 hs
    have hb := Real.rpow_le_rpow_of_nonpos hx h2 hs
    rw [h2y] at hb
    constructor
    · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hys).trans hb
    · calc x ^ s ≤ 1 * y ^ s := by rw [one_mul]; exact ha
        _ ≤ max 1 (2 ^ s) * y ^ s := mul_le_mul_of_nonneg_right (le_max_left _ _) hys

/-! ### The local dimension: cylinders of words over the letters `0, 1` -/

/-- The words of length `n` over the letters `0, 1`. -/
private def ldWords (n : ℕ) : Finset (Fin n → Fin 3) := Fintype.piFinset fun _ => {0, 1}

private theorem ld_mem_words {n : ℕ} {v : Fin n → Fin 3} : v ∈ ldWords n ↔ ∀ k, v k ≠ 2 := by
  rw [ldWords, Fintype.mem_piFinset]
  refine forall_congr' fun k => ?_
  generalize v k = i
  revert i
  decide

private theorem ld_card_words (n : ℕ) : (ldWords n).card = 2 ^ n := by
  rw [ldWords, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

private theorem ld_ofFn_ne_two {n : ℕ} {v : Fin n → Fin 3} (hv : v ∈ ldWords n) :
    ∀ i ∈ List.ofFn v, i ≠ 2 := by
  intro i hi
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hi
  exact ld_mem_words.1 hv k

/-- The Gibbs bounds summed over the words of length `n` over the letters `0, 1`. -/
private theorem ld_sum_bounds {s C : ℝ} {ν : Measure (ℕ → Fin 3)} (hC : 0 < C)
    (hG : ∀ w : List (Fin 3), C⁻¹ * exampleIFS.supDeriv w ^ s ≤ ν.real (wordCylinder w) ∧
      ν.real (wordCylinder w) ≤ C * exampleIFS.supDeriv w ^ s) (n : ℕ) :
    C⁻¹ * min 1 (2 ^ s) * (2 * (1 / 8 : ℝ) ^ s) ^ n ≤
        ∑ v ∈ ldWords n, ν.real (wordCylinder (List.ofFn v)) ∧
      ∑ v ∈ ldWords n, ν.real (wordCylinder (List.ofFn v)) ≤
        C * max 1 (2 ^ s) * (2 * (1 / 8 : ℝ) ^ s) ^ n := by
  have hterm : ∀ v ∈ ldWords n,
      C⁻¹ * min 1 (2 ^ s) * ((1 / 8 : ℝ) ^ s) ^ n ≤ ν.real (wordCylinder (List.ofFn v)) ∧
        ν.real (wordCylinder (List.ofFn v)) ≤ C * max 1 (2 ^ s) * ((1 / 8 : ℝ) ^ s) ^ n := by
    intro v hv
    obtain ⟨h1, h2⟩ := ld_supDeriv_bounds (ld_ofFn_ne_two hv)
    rw [List.length_ofFn] at h1 h2
    obtain ⟨h3, h4⟩ := ld_rpow_bounds s (pow_pos (by norm_num) n) h1 h2
    rw [← Real.rpow_pow_comm (by norm_num)] at h3 h4
    obtain ⟨h5, h6⟩ := hG (List.ofFn v)
    constructor
    · calc C⁻¹ * min 1 (2 ^ s) * ((1 / 8 : ℝ) ^ s) ^ n
          = C⁻¹ * (min 1 (2 ^ s) * ((1 / 8 : ℝ) ^ s) ^ n) := by ring
        _ ≤ C⁻¹ * exampleIFS.supDeriv (List.ofFn v) ^ s :=
            mul_le_mul_of_nonneg_left h3 (inv_pos.2 hC).le
        _ ≤ _ := h5
    · calc ν.real (wordCylinder (List.ofFn v)) ≤ C * exampleIFS.supDeriv (List.ofFn v) ^ s := h6
        _ ≤ C * (max 1 (2 ^ s) * ((1 / 8 : ℝ) ^ s) ^ n) := mul_le_mul_of_nonneg_left h4 hC.le
        _ = _ := by ring
  have hs1 := Finset.sum_le_sum fun v hv => (hterm v hv).1
  have hs2 := Finset.sum_le_sum fun v hv => (hterm v hv).2
  rw [Finset.sum_const, ld_card_words, nsmul_eq_mul] at hs1 hs2
  push_cast at hs1 hs2
  constructor
  · calc C⁻¹ * min 1 (2 ^ s) * (2 * (1 / 8 : ℝ) ^ s) ^ n
        = (2 : ℝ) ^ n * (C⁻¹ * min 1 (2 ^ s) * ((1 / 8 : ℝ) ^ s) ^ n) := by rw [mul_pow]; ring
      _ ≤ _ := hs1
  · calc _ ≤ (2 : ℝ) ^ n * (C * max 1 (2 ^ s) * ((1 / 8 : ℝ) ^ s) ^ n) := hs2
      _ = C * max 1 (2 ^ s) * (2 * (1 / 8 : ℝ) ^ s) ^ n := by rw [mul_pow]; ring

/-! ### The local dimension: the natural projection near `0` -/

/-- If the first `n` letters of `ω` are `0` or `1`, then `π(ω) ≤ 2 ⋅ 8^{-n}`. -/
private theorem ld_natProj_le {n : ℕ} {ω : ℕ → Fin 3} (h : (fun k : Fin n => ω k) ∈ ldWords n) :
    exampleIFS.natProj ω ≤ 2 * (1 / 8 : ℝ) ^ n := by
  have hy := exampleIFS.attractor_subset_I ⟨fun j => ω (j + n), rfl⟩
  rw [exampleIFS.natProj_eq_comp_prefix ω n]
  refine (ld_re_comp_le (ld_ofFn_ne_two h) hy).trans ?_
  rw [List.length_ofFn]
  have hpow : (0 : ℝ) ≤ (1 / 8) ^ n := by positivity
  have : exampleIFS.natProj (fun j => ω (j + n)) * (1 + exampleIFS.natProj (fun j => ω (j + n)))
      ≤ 2 := by nlinarith [hy.1, hy.2]
  nlinarith

/-- If the letter of `ω` in position `k` (from `0`) is the first letter `2`, then
`π(ω) ≥ (29/32) 8^{-k}`. -/
private theorem ld_le_natProj {k : ℕ} {ω : ℕ → Fin 3} (hk : ω k = 2) (h : ∀ j < k, ω j ≠ 2) :
    29 / 32 * (1 / 8 : ℝ) ^ k ≤ exampleIFS.natProj ω := by
  have hw : ∀ i ∈ List.ofFn (fun j : Fin k => ω j), i ≠ 2 := by
    intro i hi
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hi
    exact h j j.2
  set σ : ℕ → Fin 3 := fun j => ω (j + k) with hσ
  have hy := exampleIFS.attractor_subset_I ⟨σ, rfl⟩
  have hz := exampleIFS.attractor_subset_I ⟨fun j => σ (j + 1), rfl⟩
  have h29 : 29 / 32 ≤ exampleIFS.natProj σ := by
    rw [exampleIFS.natProj_eq_comp_prefix σ 1]
    have hl : (List.ofFn fun j : Fin 1 => σ j) = [2] := by simp [σ, hk]
    rw [hl, IFS.comp_cons, IFS.comp_nil, Function.comp_apply, id, ld_f_two_ofReal,
      Complex.ofReal_re]
    nlinarith [hz.1]
  rw [exampleIFS.natProj_eq_comp_prefix ω k]
  refine le_trans ?_ (ld_le_re_comp hw hy)
  rw [List.length_ofFn]
  have hpow : (0 : ℝ) ≤ (1 / 8) ^ k := by positivity
  nlinarith

/-- The natural measure of the polynomial example in Section 1.2.2: a measure `ν` with the Gibbs
property for the potential `s log|f'|` fixes `s = s(Φ)` as the unique zero of the pressure,
and the natural measure `μ = ν ∘ π⁻¹` has local dimension `s(Φ) - 1/3` at `0`. -/
theorem example_localDim {s : ℝ} {ν : Measure (ℕ → Fin 3)} [IsProbabilityMeasure ν]
    (hν : exampleIFS.IsGibbs s ν) :
    (∀ t, Tendsto (fun n : ℕ => Real.log (exampleIFS.pressureSum t n) / n) atTop (𝓝 0) ↔
      t = s) ∧
    Tendsto (fun r => Real.log ((ν.map exampleIFS.natProj).real (closedBall 0 r)) / Real.log r)
      (𝓝[>] 0) (𝓝 (s - 1 / 3)) := by
  refine ⟨exampleIFS.tendsto_pressure_iff_of_isGibbs (by norm_num) hν, ?_⟩
  obtain ⟨C, hC, hG⟩ := hν
  set ρ : ℝ := 2 * (1 / 8 : ℝ) ^ s with hρ_def
  have hρ : 0 < ρ := mul_pos two_pos (Real.rpow_pos_of_pos (by norm_num) s)
  have hmin : 0 < min 1 ((2 : ℝ) ^ s) := lt_min one_pos (Real.rpow_pos_of_pos two_pos s)
  have hmax : 0 < max 1 ((2 : ℝ) ^ s) := lt_max_of_lt_left one_pos
  -- `μ(B(0,r)) = ν(π⁻¹ B(0,r))`
  have hμ : ∀ r, (ν.map exampleIFS.natProj).real (closedBall 0 r) =
      ν.real (exampleIFS.natProj ⁻¹' closedBall 0 r) := fun r =>
    map_measureReal_apply exampleIFS.measurable_natProj measurableSet_closedBall
  -- the cylinders of the words of length `n` over `0, 1` lie in `π⁻¹ B(0, 2 ⋅ 8^{-n})`
  have hlow : ∀ n, C⁻¹ * min 1 (2 ^ s) * ρ ^ n ≤
      ν.real (exampleIFS.natProj ⁻¹' closedBall 0 (2 * (1 / 8 : ℝ) ^ n)) := by
    intro n
    refine (ld_sum_bounds hC hG n).1.trans ?_
    rw [IFS.sum_measureReal_wordCylinder]
    refine measureReal_mono fun ω hω => ?_
    have h0 := exampleIFS.attractor_subset_I ⟨ω, rfl⟩
    rw [mem_preimage, mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg h0.1]
    exact ld_natProj_le hω
  -- for `r < (29/32) 8^{-n}`, `π⁻¹ B(0,r)` lies in the cylinders of the words of length `n + 1`
  -- over `0, 1`
  have hup : ∀ n r, r < 29 / 32 * (1 / 8 : ℝ) ^ n →
      ν.real (exampleIFS.natProj ⁻¹' closedBall 0 r) ≤ C * max 1 (2 ^ s) * ρ ^ (n + 1) := by
    intro n r hr
    refine le_trans ?_ (ld_sum_bounds hC hG (n + 1)).2
    rw [IFS.sum_measureReal_wordCylinder]
    refine measureReal_mono fun ω hω => ?_
    rw [mem_preimage, mem_closedBall, Real.dist_eq, sub_zero] at hω
    have hle : exampleIFS.natProj ω ≤ r := (le_abs_self _).trans hω
    have key : ∀ k, k ≤ n → ω k ≠ 2 := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk h2
        have h1 := ld_le_natProj h2 fun j hj => ih j hj (hj.trans_le hk).le
        have h3 : (1 / 8 : ℝ) ^ n ≤ (1 / 8) ^ k :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
        linarith
    rw [mem_preimage, Finset.mem_coe, ld_mem_words]
    exact fun k => key k (Nat.lt_succ_iff.1 k.2)
  have hd : s - 1 / 3 = Real.log ρ / Real.log (1 / 8) := by
    have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have h8 : Real.log (1 / 8) = -(3 * Real.log 2) := by
      rw [one_div, Real.log_inv, show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast
      ring
    rw [hρ_def, Real.log_mul two_ne_zero (Real.rpow_pos_of_pos (by norm_num) s).ne',
      Real.log_rpow (by norm_num), h8]
    field_simp
    ring
  rw [hd]
  refine tendsto_log_div_log_of_bounds
    (m := fun r => (ν.map exampleIFS.natProj).real (closedBall 0 r)) (by norm_num) (by norm_num)
    hρ (mul_pos (mul_pos (inv_pos.2 hC) hmin) (pow_pos hρ 3)) (mul_pos (mul_pos hC hmax) hρ) ?_
  intro n r hr1 hr2
  have hpow : (0 : ℝ) < (1 / 8) ^ n := by positivity
  have hpow1 : (1 / 8 : ℝ) ^ (n + 1) = (1 / 8) ^ n * (1 / 8) := pow_succ _ _
  have hpow2 : (1 / 8 : ℝ) ^ (n + 2) = (1 / 8) ^ n * (1 / 8) ^ 2 := pow_add _ _ _
  have hpow3 : (1 / 8 : ℝ) ^ (n + 3) = (1 / 8) ^ n * (1 / 8) ^ 3 := pow_add _ _ _
  rw [hμ]
  constructor
  · have hr : 2 * (1 / 8 : ℝ) ^ (n + 3) ≤ r := by
      rw [hpow3]
      rw [hpow2] at hr1
      nlinarith
    calc C⁻¹ * min 1 (2 ^ s) * ρ ^ 3 * ρ ^ n = C⁻¹ * min 1 (2 ^ s) * ρ ^ (n + 3) := by ring
      _ ≤ _ := hlow (n + 3)
      _ ≤ _ := measureReal_mono (preimage_mono (closedBall_subset_closedBall hr))
  · have hr : r < 29 / 32 * (1 / 8 : ℝ) ^ n := by
      rw [hpow1] at hr2
      nlinarith
    calc _ ≤ C * max 1 (2 ^ s) * ρ ^ (n + 1) := hup n r hr
      _ = C * max 1 (2 ^ s) * ρ * ρ ^ n := by ring

/-- The local dimension of the natural measure of the example at `0` is smaller than `s(Φ)`. -/
theorem example_localDim_lt {s : ℝ} {ν : Measure (ℕ → Fin 3)} [IsProbabilityMeasure ν]
    (hν : exampleIFS.IsGibbs s ν) :
    ∃ d < s, Tendsto
      (fun r => Real.log ((ν.map exampleIFS.natProj).real (closedBall 0 r)) / Real.log r)
      (𝓝[>] 0) (𝓝 d) :=
  ⟨s - 1 / 3, by linarith, (example_localDim hν).2⟩

end AnalyticESC
