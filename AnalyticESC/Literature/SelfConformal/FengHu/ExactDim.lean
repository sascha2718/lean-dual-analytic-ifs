module

public import AnalyticESC.Literature.SelfConformal.FengHu.Radii
public import AnalyticESC.Literature.SelfConformal.FengHu.LocalDim
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.ExactDimensionTransfer
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.BallInformationEnvelope

@[expose] public section

/-!
# Exact dimensionality of self-conformal measures on the line

D.-J. Feng and H. Hu, *Dimension theory of iterated function systems*, Comm. Pure Appl. Math. 62
(2009), Theorem 2.8, for a `C^{1+Lip}` conformal system on `I = [0, 1]` (`ConformalIFS`), without
any separation condition: the self-conformal measure `μ = Π β` is exact dimensional with
dimension `(H(p) - Δ) / χ`, where `χ` is the Lyapunov exponent and
`Δ = ∫ -log (dμ_{ω_0}/dμ)(Π ω) dβ(ω)` is the conditional information of the first letter given
the coding (`condInfo`).

The proof follows the self-similar module `FractalGeometry/SelfSimilar/FengHu.lean`. Along the
lower and upper radii `radLo`, `radHi` of `Radii.lean`, the ball information
`I(Π ω, r) = -log μ(B(Π ω, r))` is bounded below and above by triangular sums of the one-step
increments `-log p_{ω_0} + log (μ_{ω_0}(B)/μ(B))`. These converge almost surely by Besicovitch
differentiation, are dominated by an integrable envelope, and their triangular averages converge
to `H(p) - Δ` by Maker's theorem. Since both radii are comparable with
`radD n ω = |φ_{ω|_n}'(Π σ^n ω)|`, whose logarithm is a Birkhoff sum of the Lyapunov cocycle, the
local dimension exists and equals `(H(p) - Δ) / χ` almost everywhere.

## Main declarations

* `condInfo`, `incrLo`, `incrHi`, `incrLim`.
* `sum_incrLo_le`, `le_sum_incrHi`: the chain inequalities.
* `ConformalIFS.lyapunov_pos'`, `ConformalIFS.ae_tendsto_log_radD`: the Lyapunov exponent.
* `ConformalIFS.integrable_condInfo`, `ConformalIFS.isExactDim_selfConformal`: exact
  dimensionality with `d = (H(p) - Δ) / χ`.

Copied from the library `FractalGeometry` (module `FractalGeometry.SelfConformal.FengHu.ExactDim`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.SelfConformal.FengHu

open MeasureTheory Set Filter Topology Metric
open AnalyticESC (I realComp IsProbVec)
open FractalGeometry.SelfSimilar.FengHu (ratioInfo densityInfo)

variable {N : ℕ} {φ : Fin N → ℝ → ℝ} {c L : ℝ} {p : Fin N → ℝ}

/-- The conditional information `-log (dμ_{ω_0}/dμ)(Π ω)` of the first letter given the coding.
-/
noncomputable def condInfo (φ : Fin N → ℝ → ℝ) (p : Fin N → ℝ) (hp : IsProbVec p)
    (ω : ℕ → Fin N) : ℝ :=
  densityInfo (kQ φ p hp (ω 0)) (selfConformal φ p hp) (coding φ ω)

/-- The increments along the lower radii. -/
noncomputable def incrLo (φ : Fin N → ℝ → ℝ) (L : ℝ) (p : Fin N → ℝ) (hp : IsProbVec p)
    (k : ℕ) (ω : ℕ → Fin N) : ℝ :=
  -Real.log (p (ω 0)) -
    ratioInfo (kQ φ p hp (ω 0)) (selfConformal φ p hp) (coding φ ω) (radLo φ L k ω)

/-- The increments along the upper radii. -/
noncomputable def incrHi (φ : Fin N → ℝ → ℝ) (c L : ℝ) (p : Fin N → ℝ) (hp : IsProbVec p)
    (k : ℕ) (ω : ℕ → Fin N) : ℝ :=
  -Real.log (p (ω 0)) -
    ratioInfo (kQ φ p hp (ω 0)) (selfConformal φ p hp) (coding φ ω) (radHi φ c L k ω)

/-- The limit of the increments, `-log p_{ω_0} + log (dμ_{ω_0}/dμ)(Π ω)`. -/
noncomputable def incrLim (φ : Fin N → ℝ → ℝ) (p : Fin N → ℝ) (hp : IsProbVec p)
    (ω : ℕ → Fin N) : ℝ :=
  -Real.log (p (ω 0)) - condInfo φ p hp ω

/-- The positivity conditions on balls needed at each point of an orbit. -/
def BallPos (φ : Fin N → ℝ → ℝ) (p : Fin N → ℝ) (hp : IsProbVec p) (ω : ℕ → Fin N) : Prop :=
  (∀ ρ, 0 < ρ → 0 < kQ φ p hp (ω 0) (closedBall (coding φ ω) ρ)) ∧
    ∀ ρ, 0 < ρ → 0 < selfConformal φ p hp (closedBall (coding φ ω) ρ)

/-- The balls around `Π ω` have positive `μ_{ω_0}`- and `μ`-measure for `β`-a.e. `ω`. -/
theorem ae_ballPos (hp : IsProbVec p) : ∀ᵐ ω ∂bernoulli p hp, BallPos φ p hp ω := by
  have h1 := FractalGeometry.SelfSimilar.FengHu.ae_of_branch (m := bernoulli p hp)
    (measurable_pi_apply 0) (measurable_coding φ)
    (P := fun a z => ∀ ρ, 0 < ρ → 0 < kQ φ p hp a (closedBall z ρ))
    fun a => ExactOverlaps.ae_closedBall_measure_pos (kQ φ p hp a)
  have h2 := ae_of_ae_map (measurable_coding φ).aemeasurable
    (ExactOverlaps.ae_closedBall_measure_pos (selfConformal φ p hp))
  filter_upwards [h1, h2] with ω h1 h2 using ⟨h1, h2⟩

/-- The positivity conditions hold along the whole orbit of `β`-a.e. `ω`. -/
theorem ae_ballPos_orbit (hp : IsProbVec p) :
    ∀ᵐ ω ∂bernoulli p hp, ∀ j, BallPos φ p hp (shift^[j] ω) :=
  ae_all_iff.2 fun j => ((measurePreserving_shift hp).iterate j).quasiMeasurePreserving.ae
    (ae_ballPos hp)

/-- The conditional information of the first letter is measurable. -/
theorem measurable_condInfo (φ : Fin N → ℝ → ℝ) (hp : IsProbVec p) :
    Measurable (condInfo φ p hp) :=
  FractalGeometry.SelfSimilar.FengHu.measurable_of_index (measurable_pi_apply 0)
    (measurable_coding φ) fun _ => FractalGeometry.SelfSimilar.FengHu.measurable_densityInfo _ _

/-- `ω ↦ -log p_{ω_0}` is measurable. -/
theorem measurable_neg_log_head (p : Fin N → ℝ) :
    Measurable fun ω : ℕ → Fin N => -Real.log (p (ω 0)) :=
  (measurable_of_finite fun a => -Real.log (p a)).comp (measurable_pi_apply 0)

/-- The limit increment is measurable. -/
theorem measurable_incrLim (φ : Fin N → ℝ → ℝ) (hp : IsProbVec p) :
    Measurable (incrLim φ p hp) :=
  (measurable_neg_log_head p).sub (measurable_condInfo φ hp)

/-- The lower increments are measurable. -/
theorem measurable_incrLo (φ : Fin N → ℝ → ℝ) (L : ℝ) (hp : IsProbVec p) (k : ℕ) :
    Measurable (incrLo φ L p hp k) :=
  (measurable_neg_log_head p).sub
    (FractalGeometry.SelfSimilar.FengHu.measurable_of_index' (measurable_pi_apply 0)
      fun _ => FractalGeometry.SelfSimilar.FengHu.measurable_ratioInfo _ _ (measurable_coding φ)
        (measurable_radLo φ L k))

/-- The upper increments are measurable. -/
theorem measurable_incrHi (φ : Fin N → ℝ → ℝ) (c L : ℝ) (hp : IsProbVec p) (k : ℕ) :
    Measurable (incrHi φ c L p hp k) :=
  (measurable_neg_log_head p).sub
    (FractalGeometry.SelfSimilar.FengHu.measurable_of_index' (measurable_pi_apply 0)
      fun _ => FractalGeometry.SelfSimilar.FengHu.measurable_ratioInfo _ _ (measurable_coding φ)
        (measurable_radHi φ c L k))

/-- Reindexing the triangular sums: the term `j = 0` and the shifted sum. -/
theorem sum_range_succ_iterate (F : ℕ → (ℕ → Fin N) → ℝ) (n : ℕ) (ω : ℕ → Fin N) :
    ∑ j ∈ Finset.range (n + 1), F (n + 1 - j) (shift^[j] ω) =
      F (n + 1) ω + ∑ j ∈ Finset.range n, F (n - j) (shift^[j] (shift ω)) := by
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.add_sub_add_right, Function.iterate_succ_apply]

namespace ConformalIFS

variable (hφ : ConformalIFS φ c L)
include hφ

/-- The lower chain: the ball information along `radLo` dominates the triangular sum. -/
theorem sum_incrLo_le (hp : IsProbVec p) : ∀ (n : ℕ) (ω : ℕ → Fin N),
    (∀ j, BallPos φ p hp (shift^[j] ω)) →
    ∑ j ∈ Finset.range n, incrLo φ L p hp (n - j) (shift^[j] ω) ≤
      ExactOverlaps.ballInformation (selfConformal φ p hp) (coding φ ω) (radLo φ L n ω)
  | 0, ω, _ => by
    simpa using ExactOverlaps.ballInformation_nonneg (selfConformal φ p hp) _ _
  | n + 1, ω, hgood => by
    rw [sum_range_succ_iterate]
    have ih := sum_incrLo_le hp n (shift ω) fun j => by
      simpa [Function.iterate_succ_apply] using hgood (j + 1)
    have h0 := hgood 0
    have h1 := hgood 1
    simp only [Function.iterate_zero, id, Function.iterate_one] at h0 h1
    have hstep := info_step_ge (kQ_le hp (ω 0)) (hp.1 (ω 0)) (h0.1 _ (hφ.radLo_pos _ _))
      (h1.2 _ (hφ.radLo_pos n _)) (hφ.kQ_closedBall_radLo_le hp n ω)
    have he : incrLo φ L p hp (n + 1) ω = -Real.log (p (ω 0)) -
        ratioInfo (kQ φ p hp (ω 0)) (selfConformal φ p hp) (coding φ ω)
          (radLo φ L (n + 1) ω) := rfl
    rw [he]
    linarith

/-- The upper chain: the ball information along `radHi` is dominated by the triangular sum. -/
theorem le_sum_incrHi (hp : IsProbVec p) : ∀ (n : ℕ) (ω : ℕ → Fin N),
    (∀ j, BallPos φ p hp (shift^[j] ω)) →
    ExactOverlaps.ballInformation (selfConformal φ p hp) (coding φ ω) (radHi φ c L n ω) ≤
      ∑ j ∈ Finset.range n, incrHi φ c L p hp (n - j) (shift^[j] ω)
  | 0, ω, _ => by
    have hI : I ⊆ closedBall (coding φ ω) 1 := fun y hy => by
      rw [mem_closedBall, Real.dist_eq]
      exact abs_sub_le_one_of_mem_I hy (hφ.coding_mem ω)
    have h1 : selfConformal φ p hp (closedBall (coding φ ω) 1) = 1 :=
      le_antisymm prob_le_one ((selfConformal_I hφ hp).symm.le.trans (measure_mono hI))
    simp [ExactOverlaps.ballInformation, radHi, h1]
  | n + 1, ω, hgood => by
    rw [sum_range_succ_iterate]
    have ih := le_sum_incrHi hp n (shift ω) fun j => by
      simpa [Function.iterate_succ_apply] using hgood (j + 1)
    have h1 := hgood 1
    simp only [Function.iterate_one] at h1
    have hstep := info_step_le (kQ_le hp (ω 0)) (hp.1 (ω 0)) (h1.2 _ (hφ.radHi_pos n _))
      (hφ.le_kQ_closedBall_radHi hp n ω)
    have he : incrHi φ c L p hp (n + 1) ω = -Real.log (p (ω 0)) -
        ratioInfo (kQ φ p hp (ω 0)) (selfConformal φ p hp) (coding φ ω)
          (radHi φ c L (n + 1) ω) := rfl
    rw [he]
    linarith

/-! ### Convergence and domination of the increments -/

/-- The lower radii tend to `0` from above. -/
theorem tendsto_radLo (ω : ℕ → Fin N) :
    Tendsto (fun k => radLo φ L k ω) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => hφ.radLo_pos k ω⟩
  exact squeeze_zero (fun k => (hφ.radLo_pos k ω).le) (fun k => hφ.radLo_le_pow k ω)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hφ.c_nonneg hφ.c_lt_one)

/-- The upper radii tend to `0` from above. -/
theorem tendsto_radHi (ω : ℕ → Fin N) :
    Tendsto (fun k => radHi φ c L k ω) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => hφ.radHi_pos k ω⟩
  exact squeeze_zero (fun k => (hφ.radHi_pos k ω).le) (fun k => hφ.radHi_le_pow k ω)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hφ.c_nonneg hφ.c_lt_one)

/-- The ratios converge along both sequences of radii (Besicovitch differentiation). -/
theorem ae_tendsto_incr (hp : IsProbVec p) :
    ∀ᵐ ω ∂bernoulli p hp,
      Tendsto (fun k => incrLo φ L p hp k ω) atTop (𝓝 (incrLim φ p hp ω)) ∧
        Tendsto (fun k => incrHi φ c L p hp k ω) atTop (𝓝 (incrLim φ p hp ω)) := by
  have h := FractalGeometry.SelfSimilar.FengHu.ae_of_branch (m := bernoulli p hp)
    (measurable_pi_apply 0) (measurable_coding φ)
    (P := fun a z => Tendsto (fun ρ => ratioInfo (kQ φ p hp a) (selfConformal φ p hp) z ρ)
      (𝓝[>] 0) (𝓝 (densityInfo (kQ φ p hp a) (selfConformal φ p hp) z)))
    fun a => FractalGeometry.SelfSimilar.FengHu.ae_tendsto_ratioInfo _ _ (kQ_le hp a)
  filter_upwards [h] with ω hω
  exact ⟨tendsto_const_nhds.sub (hω.comp (hφ.tendsto_radLo ω)),
    tendsto_const_nhds.sub (hω.comp (hφ.tendsto_radHi ω))⟩

/-- An integrable envelope for all increments and their limit. -/
theorem exists_incr_envelope (hp : IsProbVec p) :
    ∃ G : (ℕ → Fin N) → ℝ, Integrable G (bernoulli p hp) ∧
      ∀ᵐ ω ∂bernoulli p hp, (∀ k, |incrLo φ L p hp k ω| ≤ G ω) ∧
        (∀ k, |incrHi φ c L p hp k ω| ≤ G ω) ∧ |incrLim φ p hp ω| ≤ G ω := by
  choose GQ hGQm hGQi hGQ0 hGQ using fun a =>
    ExactOverlaps.exists_integrable_ballInformation_envelope (kQ φ p hp a)
      (selfConformal φ p hp) (kQ_le hp a) 1
  set C : ℝ := ∑ a, |Real.log (p a)|
  have hC : ∀ a, |-Real.log (p a)| ≤ C := fun a => by
    rw [abs_neg]
    exact Finset.single_le_sum (f := fun a => |Real.log (p a)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ a)
  refine ⟨fun ω => C + GQ (ω 0) (coding φ ω), (integrable_const C).add
    (FractalGeometry.SelfSimilar.FengHu.integrable_of_branch (measurable_pi_apply 0)
      (measurable_coding φ) hGQm hGQi), ?_⟩
  have hQ := FractalGeometry.SelfSimilar.FengHu.ae_of_branch (m := bernoulli p hp)
    (measurable_pi_apply 0) (measurable_coding φ)
    (P := fun a z => ∀ r : ℝ, 0 < r → r ≤ 1 →
      |Real.log (kQ φ p hp a (closedBall z r) / selfConformal φ p hp (closedBall z r)).toReal|
        ≤ GQ a z) hGQ
  have hk : ∀ᵐ ω ∂bernoulli p hp, (∀ k, |incrLo φ L p hp k ω| ≤ C + GQ (ω 0) (coding φ ω)) ∧
      ∀ k, |incrHi φ c L p hp k ω| ≤ C + GQ (ω 0) (coding φ ω) := by
    filter_upwards [hQ] with ω hω
    have hr : ∀ r : ℝ, 0 < r → r ≤ 1 → |-Real.log (p (ω 0)) -
        ratioInfo (kQ φ p hp (ω 0)) (selfConformal φ p hp) (coding φ ω) r| ≤
          C + GQ (ω 0) (coding φ ω) := fun r hr0 hr1 =>
      (abs_sub _ _).trans (add_le_add (hC _) (by simpa [ratioInfo] using hω r hr0 hr1))
    exact ⟨fun k => hr _ (hφ.radLo_pos k ω)
        ((hφ.radLo_le_pow k ω).trans (pow_le_one₀ hφ.c_nonneg hφ.c_lt_one.le)),
      fun k => hr _ (hφ.radHi_pos k ω)
        ((hφ.radHi_le_pow k ω).trans (pow_le_one₀ hφ.c_nonneg hφ.c_lt_one.le))⟩
  filter_upwards [hk, hφ.ae_tendsto_incr hp] with ω hω hlim
  exact ⟨hω.1, hω.2, le_of_tendsto ((continuous_abs.tendsto _).comp hlim.1)
    (Eventually.of_forall hω.1)⟩

/-- The limit increment is integrable. -/
theorem integrable_incrLim (hp : IsProbVec p) : Integrable (incrLim φ p hp) (bernoulli p hp) := by
  obtain ⟨G, hGi, hG⟩ := hφ.exists_incr_envelope hp
  exact hGi.mono' (measurable_incrLim φ hp).aestronglyMeasurable
    (hG.mono fun ω h => by rw [Real.norm_eq_abs]; exact h.2.2)

omit hφ in
/-- `ω ↦ -log p_{ω_0}` is integrable. -/
theorem integrable_neg_log_head (hp : IsProbVec p) :
    Integrable (fun ω : ℕ → Fin N => -Real.log (p (ω 0))) (bernoulli p hp) :=
  Integrable.of_bound (measurable_neg_log_head p).aestronglyMeasurable (∑ a, |Real.log (p a)|)
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_neg]
      exact Finset.single_le_sum (f := fun a => |Real.log (p a)|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ _))

/-- The conditional information of the first letter is integrable. -/
theorem integrable_condInfo (hp : IsProbVec p) :
    Integrable (condInfo φ p hp) (bernoulli p hp) := by
  have h := (integrable_neg_log_head hp).sub (hφ.integrable_incrLim hp)
  refine h.congr (Eventually.of_forall fun ω => ?_)
  simp [incrLim]

/-- `∫ (-log p_{ω_0} + log (dμ_{ω_0}/dμ)(Π ω)) dβ = H(p) - Δ`. -/
theorem integral_incrLim (hp : IsProbVec p) :
    ∫ ω, incrLim φ p hp ω ∂bernoulli p hp =
      AnalyticESC.entropy p - ∫ ω, condInfo φ p hp ω ∂bernoulli p hp := by
  rw [show incrLim φ p hp = fun ω => -Real.log (p (ω 0)) - condInfo φ p hp ω from rfl,
    integral_sub (integrable_neg_log_head hp) (hφ.integrable_condInfo hp),
    integral_head hp fun a => -Real.log (p a), AnalyticESC.entropy]
  congr 1
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/-! ### The Lyapunov exponent -/

/-- A bound for `|log |φ_a'||` on `I`. -/
theorem abs_log_abs_deriv_le' (a : Fin N) {y : ℝ} (hy : y ∈ I) :
    abs (Real.log |deriv (φ a) y|) ≤ (∑ b, abs (Real.log |deriv (φ b) 0|)) + L := by
  have h1 := hφ.abs_log_deriv_sub_le a y hy 0 zero_mem_I
  have h2 : |y - 0| ≤ 1 := abs_sub_le_one_of_mem_I hy zero_mem_I
  have h3 : abs (Real.log |deriv (φ a) 0|) ≤ ∑ b, abs (Real.log |deriv (φ b) 0|) :=
    Finset.single_le_sum (f := fun b => abs (Real.log |deriv (φ b) 0|))
      (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  have h4 : L * |y - 0| ≤ L := by nlinarith [hφ.L_nonneg, abs_nonneg (y - 0)]
  calc abs (Real.log |deriv (φ a) y|)
      ≤ abs (Real.log |deriv (φ a) y| - Real.log |deriv (φ a) 0|) +
          abs (Real.log |deriv (φ a) 0|) := by
        have := abs_add_le (Real.log |deriv (φ a) y| - Real.log |deriv (φ a) 0|)
          (Real.log |deriv (φ a) 0|)
        simpa using this
    _ ≤ _ := by linarith

/-- The Lyapunov cocycle is integrable. -/
theorem integrable_lyapunovCocycle' (hp : IsProbVec p) :
    Integrable (lyapunovCocycle φ) (bernoulli p hp) :=
  Integrable.of_bound (measurable_lyapunovCocycle φ).aestronglyMeasurable _
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact hφ.abs_log_abs_deriv_le' _ (hφ.coding_mem _))

/-- `∫ log |φ_{ω_0}'(Π σ ω)| dβ(ω) = -χ`. -/
theorem integral_lyapunovCocycle' (hp : IsProbVec p) :
    ∫ ω, lyapunovCocycle φ ω ∂bernoulli p hp = -lyapunov φ p hp := by
  have := isProbabilityMeasure_step hp
  set G : Fin N × (ℕ → Fin N) → ℝ := fun q => Real.log |deriv (φ q.1) (coding φ q.2)| with hG
  have hGm : Measurable G := measurable_from_prod_countable_right fun i =>
    (measurable_log_abs_deriv i).comp (measurable_coding φ)
  have hGint : Integrable G ((step p).prod (bernoulli p hp)) :=
    Integrable.of_bound hGm.aestronglyMeasurable _ (Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs]
      exact hφ.abs_log_abs_deriv_le' _ (hφ.coding_mem _))
  have h1 : ∫ ω, lyapunovCocycle φ ω ∂bernoulli p hp =
      ∫ q, G q ∂(step p).prod (bernoulli p hp) := by
    rw [← map_zero_shift_bernoulli hp, integral_map
      ((measurable_pi_apply 0).prodMk measurable_shift).aemeasurable hGm.aestronglyMeasurable]
    rfl
  rw [h1, integral_prod G hGint, integral_step p hp, lyapunov, neg_neg]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [selfConformal, integral_map (measurable_coding φ).aemeasurable
    (measurable_log_abs_deriv i).aestronglyMeasurable]

/-- The Lyapunov exponent is positive: `χ ≥ -log c > 0`. -/
theorem lyapunov_pos' [NeZero N] (hp : IsProbVec p) : 0 < lyapunov φ p hp := by
  have hc := hφ.c_pos
  have hle : ∫ ω, lyapunovCocycle φ ω ∂bernoulli p hp ≤ ∫ _ω, Real.log c ∂bernoulli p hp :=
    integral_mono (hφ.integrable_lyapunovCocycle' hp) (integrable_const _) fun ω =>
      Real.log_le_log (hφ.dfac_pos ω) (hφ.dfac_le ω)
  rw [hφ.integral_lyapunovCocycle' hp] at hle
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hle
  linarith [Real.log_neg hc hφ.c_lt_one]

/-- `log radD n ω` is the Birkhoff sum of the Lyapunov cocycle. -/
theorem log_radD : ∀ (n : ℕ) (ω : ℕ → Fin N),
    Real.log (radD φ n ω) = birkhoffSum shift (lyapunovCocycle φ) n ω
  | 0, _ => by simp [radD]
  | n + 1, ω => by
    rw [radD, Real.log_mul (hφ.dfac_pos ω).ne' (hφ.radD_pos n _).ne', log_radD n,
      birkhoffSum_succ_apply']
    rfl

/-- `-log radD n ω / n → χ` for `β`-a.e. `ω`. -/
theorem ae_tendsto_log_radD (hp : IsProbVec p) :
    ∀ᵐ ω ∂bernoulli p hp, Tendsto (fun n : ℕ => -Real.log (radD φ n ω) / n) atTop
      (𝓝 (lyapunov φ p hp)) := by
  filter_upwards [FractalGeometry.Ergodic.birkhoff_ergodic (ergodic_shift hp)
    (hφ.integrable_lyapunovCocycle' hp)] with ω hω
  rw [hφ.integral_lyapunovCocycle' hp] at hω
  have h := hω.neg
  rw [neg_neg] at h
  refine h.congr fun n => ?_
  rw [birkhoffAverage, smul_eq_mul, hφ.log_radD n ω]
  ring

/-! ### Exact dimensionality -/

/-- The ball information along `radD` grows like `n (H(p) - Δ)`. -/
theorem ae_tendsto_info_radD (hp : IsProbVec p) :
    ∀ᵐ ω ∂bernoulli p hp, Tendsto (fun n : ℕ =>
      ExactOverlaps.ballInformation (selfConformal φ p hp) (coding φ ω) (radD φ n ω) / n) atTop
        (𝓝 (∫ ω, incrLim φ p hp ω ∂bernoulli p hp)) := by
  obtain ⟨G, hGi, hG⟩ := hφ.exists_incr_envelope hp
  have hlo := FractalGeometry.SelfSimilar.FengHu.ae_tendsto_triangularAverage (ergodic_shift hp)
    (measurable_incrLo φ L hp) (measurable_incrLim φ hp) hGi
    (hG.mono fun ω h => ⟨h.1, h.2.2⟩) ((hφ.ae_tendsto_incr hp).mono fun ω h => h.1)
  have hhi := FractalGeometry.SelfSimilar.FengHu.ae_tendsto_triangularAverage (ergodic_shift hp)
    (measurable_incrHi φ c L hp) (measurable_incrLim φ hp) hGi
    (hG.mono fun ω h => ⟨h.2.1, h.2.2⟩) ((hφ.ae_tendsto_incr hp).mono fun ω h => h.2)
  set h' := ∫ ω, incrLim φ p hp ω ∂bernoulli p hp
  -- a fixed shift `k` with `e^{L/(1-c)} c^k ≤ 1`
  set K : ℝ := L * (1 / (1 - c)) with hK
  obtain ⟨k, hk⟩ : ∃ k : ℕ, c ^ k ≤ Real.exp (-K) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hφ.c_nonneg hφ.c_lt_one).eventually
      (ge_mem_nhds (Real.exp_pos (-K)))).exists
  have hLS : ∀ n, L * geomS c n ≤ K := fun n =>
    mul_le_mul_of_nonneg_left (hφ.geomS_le n) hφ.L_nonneg
  filter_upwards [hlo, hhi, ae_ballPos_orbit hp] with ω hωlo hωhi hgood
  set μ := selfConformal φ p hp
  set x := coding φ ω
  have hpos : ∀ t : ℝ, 0 < t → 0 < μ (closedBall x t) := by
    have := (hgood 0).2
    simpa using this
  have hanti := ExactOverlaps.ballInformation_antitoneOn μ x hpos
  -- upper bound
  have hup : ∀ n : ℕ, ExactOverlaps.ballInformation μ x (radD φ n ω) ≤
      (n + k : ℕ) * ExactOverlaps.Ergodic.triangularAverage shift (incrHi φ c L p hp)
        (n + k) ω := by
    intro n
    have hr : radHi φ c L (n + k) ω ≤ radD φ n ω := by
      calc radHi φ c L (n + k) ω ≤ Real.exp (L * geomS c (n + k)) * radD φ (n + k) ω :=
            hφ.radHi_le_exp_mul_radD _ _
        _ ≤ Real.exp K * (c ^ k * radD φ n ω) :=
            mul_le_mul (Real.exp_le_exp.2 (hLS _)) (hφ.radD_add_le k n ω)
              (hφ.radD_pos _ _).le (Real.exp_pos _).le
        _ = (Real.exp K * c ^ k) * radD φ n ω := by ring
        _ ≤ 1 * radD φ n ω := by
            refine mul_le_mul_of_nonneg_right ?_ (hφ.radD_pos n ω).le
            calc Real.exp K * c ^ k ≤ Real.exp K * Real.exp (-K) :=
                  mul_le_mul_of_nonneg_left hk (Real.exp_pos _).le
              _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        _ = radD φ n ω := one_mul _
    have h1 := hanti (hφ.radHi_pos (n + k) ω) (hφ.radD_pos n ω) hr
    have h2 := hφ.le_sum_incrHi hp (n + k) ω hgood
    have hnk : ((n + k : ℕ) : ℝ) ≠ 0 ∨ n + k = 0 := by
      rcases Nat.eq_zero_or_pos (n + k) with h | h
      · exact Or.inr h
      · exact Or.inl (by exact_mod_cast h.ne')
    rw [ExactOverlaps.Ergodic.triangularAverage]
    rcases hnk with hnk | hnk
    · rw [mul_div_cancel₀ _ hnk]
      exact h1.trans h2
    · have hn : n = 0 := by omega
      have hk0 : k = 0 := by omega
      subst hn hk0
      simp only [Nat.add_zero, CharP.cast_eq_zero, zero_mul]
      have := hφ.le_sum_incrHi hp 0 ω hgood
      simp only [Finset.range_zero, Finset.sum_empty] at this
      have h0 : radD φ 0 ω = radHi φ c L 0 ω := rfl
      rw [h0]
      exact this
  -- lower bound
  have hlow : ∀ n : ℕ, (n : ℝ) * ExactOverlaps.Ergodic.triangularAverage shift
      (incrLo φ L p hp) n ω ≤ ExactOverlaps.ballInformation μ x (radD φ (n + k) ω) := by
    intro n
    have hr : radD φ (n + k) ω ≤ radLo φ L n ω := by
      calc radD φ (n + k) ω ≤ c ^ k * radD φ n ω := hφ.radD_add_le k n ω
        _ ≤ Real.exp (-K) * radD φ n ω :=
            mul_le_mul_of_nonneg_right hk (hφ.radD_pos n ω).le
        _ ≤ Real.exp (-(L * geomS c n)) * radD φ n ω :=
            mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (neg_le_neg (hLS n)))
              (hφ.radD_pos n ω).le
        _ ≤ radLo φ L n ω := hφ.exp_mul_radD_le_radLo n ω
    have h1 := hanti (hφ.radD_pos (n + k) ω) (hφ.radLo_pos n ω) hr
    have h2 := hφ.sum_incrLo_le hp n ω hgood
    rw [ExactOverlaps.Ergodic.triangularAverage]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simpa using ExactOverlaps.ballInformation_nonneg μ x _
    · rw [mul_div_cancel₀ _ (by exact_mod_cast hn.ne')]
      exact h2.trans h1
  -- the squeeze
  have hlim_up : Tendsto (fun n : ℕ => ((n + k : ℕ) : ℝ) / n *
      ExactOverlaps.Ergodic.triangularAverage shift (incrHi φ c L p hp) (n + k) ω) atTop
        (𝓝 h') := by
    have h1 : Tendsto (fun n : ℕ => ((n + k : ℕ) : ℝ) / n) atTop (𝓝 1) := by
      have : Tendsto (fun n : ℕ => (1 : ℝ) + k / n) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
      rw [add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      push_cast
      field_simp
    have h2 := hωhi.comp (tendsto_add_atTop_nat k)
    simpa using h1.mul h2
  have hlim_lo : Tendsto (fun n : ℕ => ((n - k : ℕ) : ℝ) / n *
      ExactOverlaps.Ergodic.triangularAverage shift (incrLo φ L p hp) (n - k) ω) atTop
        (𝓝 h') := by
    have h1 := ExactOverlaps.Ergodic.tendsto_nat_sub_fraction k
    have h2 := hωlo.comp (tendsto_sub_atTop_nat k)
    simpa using h1.mul h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim_lo hlim_up ?_ ?_
  · filter_upwards [eventually_ge_atTop k, eventually_gt_atTop 0] with n hn hn0
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
    have := hlow (n - k)
    rw [Nat.sub_add_cancel hn] at this
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right this (Nat.cast_nonneg n)
  · filter_upwards [eventually_gt_atTop 0] with n hn0
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (hup n) (Nat.cast_nonneg n)

/-- **Feng–Hu, Theorem 2.8, for conformal systems on the line**: the self-conformal measure is
exact dimensional with dimension `(H(p) - Δ) / χ`. -/
theorem isExactDim_selfConformal [NeZero N] (hp : IsProbVec p) :
    FractalGeometry.IsExactDim (selfConformal φ p hp)
      ((AnalyticESC.entropy p - ∫ ω, condInfo φ p hp ω ∂bernoulli p hp) / lyapunov φ p hp) := by
  rw [← hφ.integral_incrLim hp]
  have h := ExactOverlaps.hasExactDimension_of_map_ae_local_limit (bernoulli p hp)
    (selfConformal φ p hp) (measurable_coding φ) rfl (d := (∫ ω, incrLim φ p hp ω ∂bernoulli p hp) /
      lyapunov φ p hp) (by
    filter_upwards [hφ.ae_tendsto_info_radD hp, hφ.ae_tendsto_log_radD hp, ae_ballPos hp]
      with ω hinfo hrate hgood
    exact ExactOverlaps.local_dimension_of_sampled_information _ _ hgood.2
      (hφ.radD_pos · ω) (hφ.radD_antitone ω)
      (squeeze_zero (fun n => (hφ.radD_pos n ω).le) (fun n => hφ.radD_le_pow n ω)
        (tendsto_pow_atTop_nhds_zero_of_lt_one hφ.c_nonneg hφ.c_lt_one))
      (hφ.lyapunov_pos' hp) hinfo hrate)
  exact h

end ConformalIFS

end FractalGeometry.SelfConformal.FengHu
