module

public import AnalyticESC.Literature.Rapaport.Attractor.Basic

@[expose] public section

/-!
# Gibbs weights from Bowen's theorem

For a system `φ` satisfying `AnalyticESC.RapaportHyp φ` and the zero `s` of the pressure, Bowen's
theorem (R. Bowen, *Equilibrium states and the ergodic theory of Anosov diffeomorphisms*, Lecture
Notes in Mathematics 470, Springer, 1975, Theorem 1.4, taken as the hypothesis
`AnalyticESC.BowenGibbsStatement`) applied to the potential `ψ_s(ω) = s log |φ'_{ω₀}(Π(σω))|`
gives a probability measure `ν` on `(Fin N)^ℕ` with `ν[u] ≍ ‖φ_u'‖_I^s`. This is the measure `ν`
of the proof of Corollary 1.3 of A. Rapaport, *Dimension of self-conformal measures associated to
an exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2. The pressure hypothesis forces
the constant `P` of the Gibbs bounds to vanish. The argument follows
`AnalyticESC.IFS.isGibbs_of_isGibbsMeasure` of `AnalyticESC.Dimension.NaturalMeasure`.

Main declarations:

* `potential`: `s` times the toolkit's `lyapunovCocycle`, with its Birkhoff sums
  (`birkhoff_potential`) and exponentially decaying variations (`potential_variation`, via
  `abs_coding_sub_le_of_agree`);
* `sum_measureReal_cylinder`, `ext0`, `setOf_eq_cylinder`, `word_ext0`: cylinders;
* `exists_gibbs_weights`: `C⁻¹ ‖φ_u'‖^s ≤ ν[u] ≤ C ‖φ_u'‖^s`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Attractor.Gibbs`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Attractor

open Set Filter Topology MeasureTheory AnalyticESC FractalGeometry.SelfConformal

variable {N : ℕ} {φ : Fin N → ℝ → ℝ}

/-- The potential `ψ_s(ω) = s log |φ'_{ω₀}(Π(σω))|` on `(Fin N)^ℕ`, `s` times the Lyapunov
cocycle of the toolkit. -/
noncomputable def potential (φ : Fin N → ℝ → ℝ) (s : ℝ) (ω : ℕ → Fin N) : ℝ :=
  s * lyapunovCocycle φ ω

/-- The Birkhoff sums of the potential:
`∑_{k < m} ψ_s(σ^k x) = s log |φ_{x|_m}'(Π(σ^m x))|`. -/
theorem birkhoff_potential (hφ : RapaportHyp φ) (s : ℝ) (m : ℕ) (x : ℕ → Fin N) :
    ∑ k ∈ Finset.range m, potential φ s (fun i => x (i + k)) =
      s * Real.log |deriv (realComp φ (word x m)) (coding φ (shift^[m] x))| := by
  have h : ∀ k, (fun i => x (i + k)) = shift^[k] x := fun k =>
    funext fun i => (shift_iterate_apply k x i).symm
  simp only [potential, h, ← Finset.mul_sum]
  rw [← birkhoffSum_lyapunovCocycle hφ m x, birkhoffSum]

/-- Sequences that agree in the first `k` places have codings at distance at most
`c_max^k`. -/
theorem abs_coding_sub_le_of_agree (hφ : RapaportHyp φ) {k : ℕ} {ω η : ℕ → Fin N}
    (h : ∀ i < k, ω i = η i) : |coding φ ω - coding φ η| ≤ cmax φ ^ k := by
  have hw : word ω k = word η k := by
    simp only [word]
    congr 1
    funext j
    exact h j j.2
  rw [coding_eq_realComp hφ ω k, coding_eq_realComp hφ η k, hw]
  simpa using abs_realComp_sub_le_pow hφ (word η k) (coding_mem hφ _) (coding_mem hφ _)

/-- The potential has exponentially decaying variations: there are `b > 0` and `0 < α < 1` with
`|ψ_s(x) - ψ_s(y)| ≤ b α^k` whenever `x` and `y` agree in the first `k` places. -/
theorem potential_variation (hφ : RapaportHyp φ) (hN : 0 < N) (s : ℝ) :
    ∃ b α : ℝ, 0 < b ∧ 0 < α ∧ α < 1 ∧ ∀ (k : ℕ) (x y : ℕ → Fin N), (∀ i < k, x i = y i) →
      |potential φ s x - potential φ s y| ≤ b * α ^ k := by
  have hc1 := cmax_pos hφ hN
  have hlog : Real.log (cmin φ) ≤ Real.log (cmax φ) :=
    Real.log_le_log (cmin_pos hφ hN) (cmin_le_cmax hφ)
  have hK : 0 ≤ logLip φ / cmax φ + (Real.log (cmax φ) - Real.log (cmin φ)) :=
    add_nonneg (div_nonneg logLip_nonneg hc1.le) (sub_nonneg.2 hlog)
  set b := |s| * (logLip φ / cmax φ + (Real.log (cmax φ) - Real.log (cmin φ))) + 1 with hb_def
  have hb : 0 < b := add_pos_of_nonneg_of_pos (mul_nonneg (abs_nonneg s) hK) one_pos
  refine ⟨b, cmax φ, hb, hc1, cmax_lt_one hφ, fun k x y hxy => ?_⟩
  simp only [potential, lyapunovCocycle]
  rw [← mul_sub, abs_mul]
  have hx := coding_mem hφ (shift x)
  have hy := coding_mem hφ (shift y)
  rcases k with _ | k
  · -- no common prefix: `log |φ_i'|` takes values in `[log c_min, log c_max]`
    obtain ⟨h1, h2⟩ := log_abs_deriv_mem hφ (x 0) hx
    obtain ⟨h3, h4⟩ := log_abs_deriv_mem hφ (y 0) hy
    have hd : |Real.log |deriv (φ (x 0)) (coding φ (shift x))| -
        Real.log (|deriv (φ (y 0)) (coding φ (shift y))|)| ≤
        logLip φ / cmax φ + (Real.log (cmax φ) - Real.log (cmin φ)) := by
      have : 0 ≤ logLip φ / cmax φ := div_nonneg logLip_nonneg hc1.le
      rw [abs_le]
      constructor <;> linarith
    rw [pow_zero, mul_one]
    have := mul_le_mul_of_nonneg_left hd (abs_nonneg s)
    linarith
  · -- a common prefix of length `k + 1`
    have h0 : x 0 = y 0 := hxy 0 (Nat.succ_pos k)
    have hdist : |coding φ (shift x) - coding φ (shift y)| ≤ cmax φ ^ k :=
      abs_coding_sub_le_of_agree hφ fun i hi => hxy _ (by omega)
    have hd := (abs_log_abs_deriv_sub_le hφ (x 0) hx hy).trans
      (mul_le_mul_of_nonneg_left hdist logLip_nonneg)
    rw [← h0]
    have hb' : |s| * (logLip φ / cmax φ) ≤ b := by
      have : 0 ≤ |s| * (Real.log (cmax φ) - Real.log (cmin φ)) :=
        mul_nonneg (abs_nonneg s) (sub_nonneg.2 hlog)
      rw [hb_def]
      nlinarith [abs_nonneg s]
    calc |s| * |Real.log |deriv (φ (x 0)) (coding φ (shift x))| -
          Real.log (|deriv (φ (x 0)) (coding φ (shift y))|)|
        ≤ |s| * (logLip φ * cmax φ ^ k) := mul_le_mul_of_nonneg_left hd (abs_nonneg s)
      _ = |s| * (logLip φ / cmax φ) * cmax φ ^ (k + 1) := by
          rw [pow_succ]
          field_simp
      _ ≤ b * cmax φ ^ (k + 1) := mul_le_mul_of_nonneg_right hb' (pow_nonneg hc1.le _)

/-- The cylinders of length `n` have total mass `1`. -/
theorem sum_measureReal_cylinder (ν : Measure (ℕ → Fin N)) [IsProbabilityMeasure ν] (n : ℕ) :
    ∑ u : Fin n → Fin N, ν.real (cylinder u) = 1 := by
  have hmeas : Measurable fun (ω : ℕ → Fin N) (k : Fin n) => ω k :=
    measurable_pi_iff.2 fun k => measurable_pi_apply _
  have h := sum_measureReal_singleton (μ := ν.map fun (ω : ℕ → Fin N) (k : Fin n) => ω k)
    (Finset.univ : Finset (Fin n → Fin N))
  rw [Finset.coe_univ, map_measureReal_apply hmeas MeasurableSet.univ, preimage_univ,
    probReal_univ] at h
  rw [← h]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_measureReal_apply hmeas (MeasurableSet.of_discrete)]
  congr 1
  ext ω
  simp [SelfConformal.cylinder, funext_iff]

/-- The sequence extending a finite word by the letter `0`. -/
def ext0 (hN : 0 < N) {n : ℕ} (u : Fin n → Fin N) : ℕ → Fin N :=
  fun i => if h : i < n then u ⟨i, h⟩ else ⟨0, hN⟩

/-- The cylinder of `x|_n` for the extension `x` of `u` is `[u]`. -/
theorem setOf_eq_cylinder (hN : 0 < N) {n : ℕ} (u : Fin n → Fin N) :
    {y : ℕ → Fin N | ∀ i < n, y i = ext0 hN u i} = cylinder u := by
  ext y
  simp only [mem_ofPred_eq, SelfConformal.cylinder, ext0]
  constructor
  · intro h k
    simpa [k.2] using h k k.2
  · intro h i hi
    simpa [hi] using h ⟨i, hi⟩

/-- The prefix of length `n` of the extension of `u` is `u`. -/
theorem word_ext0 (hN : 0 < N) {n : ℕ} (u : Fin n → Fin N) : word (ext0 hN u) n = List.ofFn u := by
  simp only [word, ext0]
  congr 1
  funext k
  simp [k.2]

/-- Bowen's theorem gives a probability measure `ν` on `(Fin N)^ℕ` with
`C⁻¹ ‖φ_u'‖_I^s ≤ ν[u] ≤ C ‖φ_u'‖_I^s` for every word `u`, when `s` is a zero of the pressure. -/
theorem exists_gibbs_weights (hB : BowenGibbsStatement) (hφ : RapaportHyp φ) (hN : 0 < N)
    {s : ℝ} (hs : Tendsto (fun n : ℕ => Real.log (∑ u : Fin n → Fin N,
      supDeriv φ (List.ofFn u) ^ s) / n) atTop (𝓝 0)) :
    ∃ ν : Measure (ℕ → Fin N), IsProbabilityMeasure ν ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (n : ℕ) (u : Fin n → Fin N), C⁻¹ * supDeriv φ (List.ofFn u) ^ s ≤ ν.real (cylinder u) ∧
        ν.real (cylinder u) ≤ C * supDeriv φ (List.ofFn u) ^ s := by
  obtain ⟨b, α, hb, hα, hα1, hvar⟩ := potential_variation hφ hN s
  obtain ⟨ν, hν, c₁, hc₁, c₂, hc₂, P, hG⟩ := hB hN (potential φ s) hb hα hα1 hvar
  refine ⟨ν, hν, ?_⟩
  have hSpos : ∀ l : List (Fin N), 0 < supDeriv φ l := supDeriv_pos hφ
  set A := |s| * Real.log (distConst φ) with hA_def
  set K₁ := c₁ * Real.exp (-A) with hK₁_def
  set K₂ := c₂ * Real.exp A with hK₂_def
  have hK₁ : 0 < K₁ := mul_pos hc₁ (Real.exp_pos _)
  have hK₂ : 0 < K₂ := mul_pos hc₂ (Real.exp_pos _)
  -- `ν[u] ≍ exp(-P|u|) ‖φ_u'‖^s`
  have key : ∀ (n : ℕ) (u : Fin n → Fin N),
      K₁ * Real.exp (-P * n) * supDeriv φ (List.ofFn u) ^ s ≤ ν.real (cylinder u) ∧
        ν.real (cylinder u) ≤ K₂ * Real.exp (-P * n) * supDeriv φ (List.ofFn u) ^ s := by
    intro n u
    obtain ⟨h1, h2⟩ := hG (ext0 hN u) n
    rw [setOf_eq_cylinder hN u, birkhoff_potential hφ, word_ext0 hN u] at h1 h2
    have hπ : coding φ (shift^[n] (ext0 hN u)) ∈ I := coding_mem hφ _
    have hd : |s * Real.log (supDeriv φ (List.ofFn u)) -
        s * Real.log (|deriv (realComp φ (List.ofFn u)) (coding φ (shift^[n] (ext0 hN u)))|)|
          ≤ A := by
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_log_supDeriv_sub_le hφ _ hπ) (abs_nonneg s)
    rw [abs_le] at hd
    have hrpow : supDeriv φ (List.ofFn u) ^ s =
        Real.exp (s * Real.log (supDeriv φ (List.ofFn u))) := by
      rw [Real.rpow_def_of_pos (hSpos _), mul_comm]
    have e : ∀ c B : ℝ, c * Real.exp B * Real.exp (-P * n) * supDeriv φ (List.ofFn u) ^ s =
        c * Real.exp (-P * n + (s * Real.log (supDeriv φ (List.ofFn u)) + B)) := by
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
  -- summing over the words of length `n`: `exp(-Pn) ∑_{|u| = n} ‖φ_u'‖^s ≍ 1`
  set Z : ℕ → ℝ := fun n => ∑ u : Fin n → Fin N, supDeriv φ (List.ofFn u) ^ s with hZ_def
  have hZ : ∀ n, 0 < Z n := fun n =>
    Finset.sum_pos (fun _ _ => Real.rpow_pos_of_pos (hSpos _) s)
      ⟨fun _ => ⟨0, hN⟩, Finset.mem_univ _⟩
  have hsum : ∀ n : ℕ, K₁ * Real.exp (-P * n) * Z n ≤ 1 ∧ 1 ≤ K₂ * Real.exp (-P * n) * Z n := by
    intro n
    have h1 := sum_measureReal_cylinder ν n
    constructor
    · rw [← h1, hZ_def, Finset.mul_sum]
      exact Finset.sum_le_sum fun v _ => (key n v).1
    · rw [← h1, hZ_def, Finset.mul_sum]
      exact Finset.sum_le_sum fun v _ => (key n v).2
  have hlog : ∀ n : ℕ, -Real.log K₂ ≤ Real.log (Z n) - P * n ∧
      Real.log (Z n) - P * n ≤ -Real.log K₁ := by
    intro n
    obtain ⟨h1, h2⟩ := hsum n
    have hpos : ∀ K : ℝ, 0 < K → 0 < K * Real.exp (-P * n) * Z n := fun K hK =>
      mul_pos (mul_pos hK (Real.exp_pos _)) (hZ n)
    have hl : ∀ K : ℝ, 0 < K → Real.log (K * Real.exp (-P * n) * Z n) =
        Real.log K + -P * n + Real.log (Z n) := fun K hK => by
      rw [Real.log_mul (mul_pos hK (Real.exp_pos _)).ne' (hZ n).ne',
        Real.log_mul hK.ne' (Real.exp_pos _).ne', Real.log_exp]
    have l1 := Real.log_le_log (hpos K₁ hK₁) h1
    have l2 := Real.log_le_log one_pos h2
    rw [hl K₁ hK₁, Real.log_one] at l1
    rw [hl K₂ hK₂, Real.log_one] at l2
    constructor <;> linarith
  -- hence `(1/n) log ∑_{|u| = n} ‖φ_u'‖^s → P`, so `P = 0`
  have hlim : Tendsto (fun n : ℕ => Real.log (Z n) / n) atTop (𝓝 P) := by
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
  -- the Gibbs property with `C = max(1, K₂, K₁⁻¹)`
  refine ⟨max 1 (max K₂ K₁⁻¹), le_max_left _ _, fun n u => ?_⟩
  obtain ⟨h1, h2⟩ := key n u
  rw [hP, neg_zero, zero_mul, Real.exp_zero, mul_one] at h1 h2
  have hw := Real.rpow_nonneg (hSpos (List.ofFn u)).le s
  constructor
  · refine le_trans (mul_le_mul_of_nonneg_right ?_ hw) h1
    exact inv_le_of_inv_le₀ hK₁ ((le_max_right _ _).trans (le_max_right _ _))
  · exact h2.trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hw)

end FractalGeometry.Rapaport.Attractor
