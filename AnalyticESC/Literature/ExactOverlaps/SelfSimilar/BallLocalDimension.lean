module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.BranchBalls
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.Dimension
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.RadiusInterpolation
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

set_option maxSynthPendingDepth 3

/-!
Standard local dimension from sampled ball-information rates. A fixed
dyadic characterization also makes the almost-sure limit property
measurable when transferring it through a coding map.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.BallLocalDimension`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Filter Metric
open scoped Topology ENNReal

namespace ExactOverlaps

noncomputable def ballInformation (μ : Measure ℝ) (x r : ℝ) : ℝ :=
  -Real.log (μ (closedBall x r)).toReal

theorem ballInformation_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (x r : ℝ) :
    0 ≤ ballInformation μ x r := by
  apply neg_nonneg.mpr
  apply Real.log_nonpos ENNReal.toReal_nonneg
  exact (ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one).trans_eq ENNReal.toReal_one

theorem ballInformation_antitoneOn (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ)
    (hpos : ∀ r : ℝ, 0 < r → 0 < μ (closedBall x r)) :
    AntitoneOn (ballInformation μ x) (Set.Ioi 0) := by
  intro r hr s _ hrs
  apply neg_le_neg
  apply Real.log_le_log (ENNReal.toReal_pos (hpos r hr).ne' (measure_ne_top _ _))
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (closedBall_subset_closedBall hrs))

theorem local_dimension_of_sampled_information (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x : ℝ) (hpos : ∀ t : ℝ, 0 < t → 0 < μ (closedBall x t))
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hanti : Antitone r)
    (hzero : Tendsto r atTop (𝓝 0)) {h L : ℝ} (hL : 0 < L)
    (hinfo : Tendsto (fun n : ℕ ↦ ballInformation μ x (r n) / n) atTop (𝓝 h))
    (hrate : Tendsto (fun n : ℕ ↦ -Real.log (r n) / n) atTop (𝓝 L)) :
    Tendsto (fun t : ℝ ↦ Real.log (μ (closedBall x t)).toReal / Real.log t)
      (𝓝[>] 0) (𝓝 (h / L)) := by
  have hh := information_radius_limit_of_sampled_rates hr hanti hzero
    (fun t _ ↦ ballInformation_nonneg μ x t) (ballInformation_antitoneOn μ x hpos) hL hinfo hrate
  simpa only [ballInformation, neg_div_neg_eq] using hh

theorem half_power_log_rate :
    Tendsto (fun n : ℕ ↦ -Real.log ((1 / 2 : ℝ) ^ n) / n) atTop (𝓝 (Real.log 2)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [one_div, Real.log_pow, Real.log_inv]
  field_simp

theorem local_dimension_of_dyadic_information (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x : ℝ) (hpos : ∀ t : ℝ, 0 < t → 0 < μ (closedBall x t)) {d : ℝ}
    (hd : Tendsto (fun n : ℕ ↦ ballInformation μ x ((1 / 2 : ℝ) ^ n) / n)
      atTop (𝓝 (d * Real.log 2))) :
    Tendsto (fun t : ℝ ↦ Real.log (μ (closedBall x t)).toReal / Real.log t)
      (𝓝[>] 0) (𝓝 d) := by
  have hh := local_dimension_of_sampled_information μ x hpos
    (fun n ↦ pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)
    (pow_right_anti₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    (Real.log_pos (by norm_num)) hd half_power_log_rate
  simpa only [mul_div_cancel_right₀ d (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'] using hh

theorem measurableSet_dyadic_information_limit (μ : Measure ℝ) [IsFiniteMeasure μ] (d : ℝ) :
    MeasurableSet {x | Tendsto
      (fun n : ℕ ↦ ballInformation μ x ((1 / 2 : ℝ) ^ n) / n)
      atTop (𝓝 (d * Real.log 2))} := by
  apply measurableSet_tendsto
  intro n
  exact (((measurable_closedBall_measure μ measurable_id measurable_const).ennreal_toReal.log).neg).div_const n

theorem hasExactDimension_of_dyadic_information (μ : Measure ℝ) [IsProbabilityMeasure μ] {d : ℝ}
    (hd : ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ ↦ ballInformation μ x ((1 / 2 : ℝ) ^ n) / n)
      atTop (𝓝 (d * Real.log 2))) : HasExactDimension μ d := by
  filter_upwards [hd, ae_closedBall_measure_pos μ] with x hx hp
  exact local_dimension_of_dyadic_information μ x hp hx

end ExactOverlaps
