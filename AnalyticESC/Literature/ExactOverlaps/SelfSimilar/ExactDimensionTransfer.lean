module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.BallLocalDimension

set_option maxSynthPendingDepth 3

/-!
Transfer of an almost-sure local-dimension limit through a measurable
coding map. The transfer uses the proved countable dyadic characterization,
so no measurability of an uncountable-radius limit event is assumed.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.ExactDimensionTransfer`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Filter Metric
open scoped Topology

namespace ExactOverlaps

theorem local_limit_dyadic_information (μ : Measure ℝ) (x : ℝ) {d : ℝ}
    (hd : Tendsto (fun t : ℝ ↦ Real.log (μ (closedBall x t)).toReal / Real.log t)
      (𝓝[>] 0) (𝓝 d)) :
    Tendsto (fun n : ℕ ↦ ballInformation μ x ((1 / 2 : ℝ) ^ n) / n)
      atTop (𝓝 (d * Real.log 2)) := by
  have hr : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num),
      Eventually.of_forall (fun n ↦ pow_pos (by norm_num) n)⟩
  have h := (hd.comp hr).mul half_power_log_rate
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hl : Real.log ((1 / 2 : ℝ) ^ n) ≠ 0 := by
    simp only [one_div, Real.log_pow, Real.log_inv]
    exact mul_ne_zero hn0 (neg_ne_zero.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne')
  simp only [Function.comp_def, ballInformation]
  field_simp

theorem hasExactDimension_of_map_ae_local_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {π : Ω → ℝ} (hπ : Measurable π) (hmap : P.map π = μ) {d : ℝ}
    (hd : ∀ᵐ ω ∂P, Tendsto
      (fun t : ℝ ↦ Real.log (μ (closedBall (π ω) t)).toReal / Real.log t)
      (𝓝[>] 0) (𝓝 d)) : HasExactDimension μ d := by
  apply hasExactDimension_of_dyadic_information
  have hh := (ae_map_iff hπ.aemeasurable
    (measurableSet_dyadic_information_limit μ d)).mpr
    (hd.mono (fun ω hω ↦ local_limit_dyadic_information μ (π ω) hω))
  simpa only [hmap] using hh

end ExactOverlaps
