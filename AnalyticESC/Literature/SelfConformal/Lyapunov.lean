module

public import AnalyticESC.Literature.SelfConformal.Distortion
public import AnalyticESC.Literature.Ergodic.Birkhoff

@[expose] public section

/-!
# The Lyapunov exponent

The Lyapunov exponent `χ = -∑_i p_i ∫ log |φ_i'| dμ` (in nats) of a self-conformal measure and the
almost sure limit (2.6) of A. Rapaport, *Dimension of self-conformal measures associated to an
exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2:
`(1/n) log |φ_{ω|_n}'(0)| → -χ` for `β`-a.e. `ω`. The proof applies Birkhoff's ergodic theorem
(G. D. Birkhoff, PNAS 17 (1931); `FractalGeometry.Ergodic.birkhoff_ergodic`) to the one-sided
Bernoulli shift and the function `ω ↦ log |φ_{ω_0}'(Π(σ ω))|`, and compares with the
derivative at `0` by bounded distortion.

## Main declarations

* `lyapunov`: the Lyapunov exponent `χ` of `(φ, p)`, in nats.
* `integrable_log_abs_deriv`, `integral_log_abs_deriv_le`, `log_cmin_le_integral_log_abs_deriv`.
* `lyapunov_pos`, `neg_log_cmax_le_lyapunov`, `lyapunov_le_neg_log_cmin`.
* `integral_step`, `integral_lyapunovCocycle`: `∫ log |φ_{ω_0}'(Π(σ ω))| dβ(ω) = -χ`.
* `birkhoffSum_lyapunovCocycle`: the Birkhoff sums are `log |φ_{ω|_n}'(Π(σ^n ω))|`.
* `ae_tendsto_log_abs_deriv_realComp`: the limit (2.6).

Copied from the library `FractalGeometry` (module `FractalGeometry.SelfConformal.Lyapunov`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.SelfConformal

open MeasureTheory ProbabilityTheory Set Filter Topology
open AnalyticESC (I realComp RapaportHyp IsProbVec)

variable {N : ℕ} {φ : Fin N → ℝ → ℝ} {p : Fin N → ℝ}

/-- The Lyapunov exponent `χ = -∑_i p_i ∫ log |φ_i'| dμ` (nats) of the self-conformal measure. -/
noncomputable def lyapunov (φ : Fin N → ℝ → ℝ) (p : Fin N → ℝ) (hp : IsProbVec p) : ℝ :=
  -∑ i, p i * ∫ y, Real.log |deriv (φ i) y| ∂selfConformal φ p hp

/-- `0 < c_max`. -/
theorem cmax_pos (hφ : RapaportHyp φ) (hN : 0 < N) : 0 < cmax φ :=
  (cmin_pos hφ hN).trans_le (cmin_le_cmax hφ)

/-- `log c_min ≤ log |φ_i'(x)| ≤ log c_max` on `I`. -/
theorem log_abs_deriv_mem (hφ : RapaportHyp φ) (i : Fin N) {x : ℝ} (hx : x ∈ I) :
    Real.log (cmin φ) ≤ Real.log |deriv (φ i) x| ∧ Real.log |deriv (φ i) x| ≤ Real.log (cmax φ) :=
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by subst h; exact i.elim0
  ⟨Real.log_le_log (cmin_pos hφ hN) (cmin_le_abs_deriv i hx),
    Real.log_le_log (hφ.deriv_pos i x hx) (abs_deriv_le_cmax hφ i hx)⟩

/-- A bound for `|log |φ_i'||` on `I`. -/
theorem abs_log_abs_deriv_le (hφ : RapaportHyp φ) (i : Fin N) {x : ℝ} (hx : x ∈ I) :
    |Real.log (|deriv (φ i) x|)| ≤ |Real.log (cmin φ)| + |Real.log (cmax φ)| := by
  obtain ⟨h1, h2⟩ := log_abs_deriv_mem hφ i hx
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log (cmin φ)), abs_nonneg (Real.log (cmax φ))]
  · linarith [le_abs_self (Real.log (cmax φ)), abs_nonneg (Real.log (cmin φ))]

/-- `y ↦ log |φ_i'(y)|` is measurable. -/
theorem measurable_log_abs_deriv (i : Fin N) :
    Measurable fun y => Real.log |deriv (φ i) y| :=
  Real.measurable_log.comp (measurable_deriv (φ i)).abs

/-- `log |φ_i'|` is integrable for any finite measure carried by `I`. -/
theorem integrable_log_abs_deriv_of_compl (hφ : RapaportHyp φ) (i : Fin N) {ν : Measure ℝ}
    [IsFiniteMeasure ν] (hν : ν Iᶜ = 0) : Integrable (fun y => Real.log |deriv (φ i) y|) ν :=
  Integrable.of_bound (measurable_log_abs_deriv i).aestronglyMeasurable _ <| by
    filter_upwards [ae_mem_I_of_compl hν] with y hy
    rw [Real.norm_eq_abs]
    exact abs_log_abs_deriv_le hφ i hy

/-- `log |φ_i'|` is `μ`-integrable. -/
theorem integrable_log_abs_deriv (hφ : RapaportHyp φ) (hp : IsProbVec p) (i : Fin N) :
    Integrable (fun y => Real.log |deriv (φ i) y|) (selfConformal φ p hp) :=
  integrable_log_abs_deriv_of_compl hφ i (selfConformal_compl_I hφ hp)

/-- `∫ log |φ_i'| dμ ≤ log c_max`. -/
theorem integral_log_abs_deriv_le (hφ : RapaportHyp φ) (hp : IsProbVec p) (i : Fin N) :
    ∫ y, Real.log |deriv (φ i) y| ∂selfConformal φ p hp ≤ Real.log (cmax φ) := by
  have h := integral_mono_ae (integrable_log_abs_deriv hφ hp i)
    (integrable_const (μ := selfConformal φ p hp) (Real.log (cmax φ))) <| by
      filter_upwards [ae_mem_I hφ hp] with y hy
      exact (log_abs_deriv_mem hφ i hy).2
  rwa [integral_const, probReal_univ, one_smul] at h

/-- `log c_min ≤ ∫ log |φ_i'| dμ`. -/
theorem log_cmin_le_integral_log_abs_deriv (hφ : RapaportHyp φ) (hp : IsProbVec p) (i : Fin N) :
    Real.log (cmin φ) ≤ ∫ y, Real.log |deriv (φ i) y| ∂selfConformal φ p hp := by
  have h := integral_mono_ae
    (integrable_const (μ := selfConformal φ p hp) (Real.log (cmin φ)))
    (integrable_log_abs_deriv hφ hp i) <| by
      filter_upwards [ae_mem_I hφ hp] with y hy
      exact (log_abs_deriv_mem hφ i hy).1
  rwa [integral_const, probReal_univ, one_smul] at h

/-- `-log c_max ≤ χ`. -/
theorem neg_log_cmax_le_lyapunov (hφ : RapaportHyp φ) (hp : IsProbVec p) :
    -Real.log (cmax φ) ≤ lyapunov φ p hp := by
  rw [lyapunov, neg_le_neg_iff]
  calc ∑ i, p i * ∫ y, Real.log |deriv (φ i) y| ∂selfConformal φ p hp
      ≤ ∑ i, p i * Real.log (cmax φ) := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (integral_log_abs_deriv_le hφ hp i) (hp.1 i).le
    _ = Real.log (cmax φ) := by rw [← Finset.sum_mul, hp.2, one_mul]

/-- `χ ≤ -log c_min`. -/
theorem lyapunov_le_neg_log_cmin (hφ : RapaportHyp φ) (hp : IsProbVec p) :
    lyapunov φ p hp ≤ -Real.log (cmin φ) := by
  rw [lyapunov, neg_le_neg_iff]
  calc Real.log (cmin φ) = ∑ i, p i * Real.log (cmin φ) := by
        rw [← Finset.sum_mul, hp.2, one_mul]
    _ ≤ ∑ i, p i * ∫ y, Real.log |deriv (φ i) y| ∂selfConformal φ p hp :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (log_cmin_le_integral_log_abs_deriv hφ hp i) (hp.1 i).le

/-- `0 < χ`. -/
theorem lyapunov_pos (hφ : RapaportHyp φ) (hp : IsProbVec p) : 0 < lyapunov φ p hp := by
  have hN := pos_of_isProbVec hp
  have h : Real.log (cmax φ) < 0 := Real.log_neg (cmax_pos hφ hN) (cmax_lt_one hφ)
  linarith [neg_log_cmax_le_lyapunov hφ hp]

/-! ### The Lyapunov cocycle and the limit (2.6) -/

/-- `∫ f d(step p) = ∑_i p_i f(i)`. -/
theorem integral_step (p : Fin N → ℝ) (hp : IsProbVec p) (f : Fin N → ℝ) :
    ∫ i, f i ∂step p = ∑ i, p i * f i := by
  have : ∀ i, Integrable f (ENNReal.ofReal (p i) • Measure.dirac i) := fun i =>
    (Integrable.of_finite (μ := Measure.dirac i)).smul_measure ENNReal.ofReal_ne_top
  rw [step, integral_finsetSum_measure fun i _ => this i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hp.1 i).le, smul_eq_mul]

/-- The function `ω ↦ log |φ_{ω_0}'(Π(σ ω))|`, whose Birkhoff sums are `log |φ_{ω|_n}'|`. -/
noncomputable def lyapunovCocycle (φ : Fin N → ℝ → ℝ) (ω : ℕ → Fin N) : ℝ :=
  Real.log |deriv (φ (ω 0)) (coding φ (shift ω))|

/-- The two-variable form `(i, ω) ↦ log |φ_i'(Π ω)|` is measurable. -/
private theorem measurable_cocycle₂ (φ : Fin N → ℝ → ℝ) :
    Measurable fun q : Fin N × (ℕ → Fin N) => Real.log |deriv (φ q.1) (coding φ q.2)| := by
  refine measurable_from_prod_countable_right fun i => ?_
  exact (measurable_log_abs_deriv i).comp (measurable_coding φ)

/-- The Lyapunov cocycle is measurable. -/
theorem measurable_lyapunovCocycle (φ : Fin N → ℝ → ℝ) : Measurable (lyapunovCocycle φ) :=
  (measurable_cocycle₂ φ).comp ((measurable_pi_apply 0).prodMk measurable_shift)

/-- The Lyapunov cocycle is bounded. -/
theorem abs_lyapunovCocycle_le (hφ : RapaportHyp φ) (ω : ℕ → Fin N) :
    |lyapunovCocycle φ ω| ≤ |Real.log (cmin φ)| + |Real.log (cmax φ)| :=
  abs_log_abs_deriv_le hφ _ (coding_mem hφ _)

/-- The Lyapunov cocycle is `β`-integrable. -/
theorem integrable_lyapunovCocycle (hφ : RapaportHyp φ) (hp : IsProbVec p) :
    Integrable (lyapunovCocycle φ) (bernoulli p hp) :=
  Integrable.of_bound (measurable_lyapunovCocycle φ).aestronglyMeasurable _
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact abs_lyapunovCocycle_le hφ ω)

/-- `∫ log |φ_{ω_0}'(Π(σ ω))| dβ(ω) = -χ`, by the independence of `ω_0` and `σ ω`. -/
theorem integral_lyapunovCocycle (hφ : RapaportHyp φ) (hp : IsProbVec p) :
    ∫ ω, lyapunovCocycle φ ω ∂bernoulli p hp = -lyapunov φ p hp := by
  have := isProbabilityMeasure_step hp
  set G : Fin N × (ℕ → Fin N) → ℝ := fun q => Real.log |deriv (φ q.1) (coding φ q.2)| with hG
  have hGint : Integrable G ((step p).prod (bernoulli p hp)) :=
    Integrable.of_bound (measurable_cocycle₂ φ).aestronglyMeasurable
      (|Real.log (cmin φ)| + |Real.log (cmax φ)|) (Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs]
        exact abs_log_abs_deriv_le hφ _ (coding_mem hφ _))
  have h1 : ∫ ω, lyapunovCocycle φ ω ∂bernoulli p hp =
      ∫ q, G q ∂(step p).prod (bernoulli p hp) := by
    rw [← map_zero_shift_bernoulli hp, integral_map
      ((measurable_pi_apply 0).prodMk measurable_shift).aemeasurable
      (measurable_cocycle₂ φ).aestronglyMeasurable]
    rfl
  rw [h1, integral_prod G hGint, integral_step p hp, lyapunov, neg_neg]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [selfConformal, integral_map (measurable_coding φ).aemeasurable
    (measurable_log_abs_deriv i).aestronglyMeasurable]

/-- The Birkhoff sums of the cocycle: `S_n(ω) = log |φ_{ω|_n}'(Π(σ^n ω))|`. -/
theorem birkhoffSum_lyapunovCocycle (hφ : RapaportHyp φ) (n : ℕ) (ω : ℕ → Fin N) :
    birkhoffSum shift (lyapunovCocycle φ) n ω =
      Real.log |deriv (realComp φ (word ω n)) (coding φ (shift^[n] ω))| := by
  induction n generalizing ω with
  | zero => simp
  | succ n ih =>
    have hmem := coding_mem hφ (shift^[n + 1] ω)
    rw [birkhoffSum_succ_apply', ih, word_succ, deriv_realComp_cons hφ _ _ hmem, abs_mul,
      Real.log_mul (abs_ne_zero.2 (abs_pos.1 (hφ.deriv_pos _ _ (mapsTo_realComp hφ _ hmem))))
        (abs_ne_zero.2 (deriv_realComp_ne_zero hφ _ hmem)),
      Function.iterate_succ_apply, ← coding_eq_realComp hφ (shift ω) n]
    rfl

/-- The limit (2.6) of Rapaport: for `β`-a.e. `ω`, `(1/n) log |φ_{ω|_n}'(0)| → -χ`. -/
theorem ae_tendsto_log_abs_deriv_realComp (hφ : RapaportHyp φ) (hp : IsProbVec p) :
    ∀ᵐ ω ∂bernoulli p hp, Tendsto (fun n : ℕ => Real.log |deriv (realComp φ (word ω n)) 0| / n)
      atTop (𝓝 (-lyapunov φ p hp)) := by
  filter_upwards [FractalGeometry.Ergodic.birkhoff_ergodic (ergodic_shift hp)
    (integrable_lyapunovCocycle hφ hp)] with ω hω
  rw [integral_lyapunovCocycle hφ hp] at hω
  have hS : ∀ n : ℕ, birkhoffAverage ℝ shift (lyapunovCocycle φ) n ω =
      Real.log |deriv (realComp φ (word ω n)) (coding φ (shift^[n] ω))| / n := by
    intro n
    rw [birkhoffAverage, birkhoffSum_lyapunovCocycle hφ, smul_eq_mul, inv_mul_eq_div]
  simp_rw [hS] at hω
  have hdiff : Tendsto (fun n : ℕ => (Real.log |deriv (realComp φ (word ω n)) 0| -
      Real.log |deriv (realComp φ (word ω n)) (coding φ (shift^[n] ω))|) / n) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_)
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log (distConst φ)))
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (abs_log_abs_deriv_realComp_sub_le hφ _ zero_mem_I
      (coding_mem hφ _)) (Nat.cast_nonneg n)
  have := hω.add hdiff
  rw [add_zero] at this
  refine this.congr fun n => ?_
  rw [← add_div]
  ring_nf

end FractalGeometry.SelfConformal
