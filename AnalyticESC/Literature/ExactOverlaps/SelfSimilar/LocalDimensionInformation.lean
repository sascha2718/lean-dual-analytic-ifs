module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.DyadicBallInformation
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.Dimension
public import Mathlib.Analysis.SpecificLimits.Basic

set_option maxSynthPendingDepth 3

/-!
An almost-sure local dimension is also the almost-sure limit of normalized
dyadic information. This is a pointwise result for actual Borel probability
measures; passing to entropy additionally requires control of information
tails and is not assumed in this theorem.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.LocalDimensionInformation`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps.Entropy

theorem ae_information_ball_error_tendsto_zero (μ : ProbabilityMeasure ℝ) :
    ∀ᵐ x ∂(μ : Measure ℝ), Tendsto (fun n : ℕ ↦
      (dyadicInformation μ n x - dyadicBallInformation μ n x) /
        ((n : ℝ) * Real.log 2)) atTop (𝓝 0) := by
  have hall : ∀ᵐ x ∂(μ : Measure ℝ), ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      0 ≤ dyadicInformation μ n x - dyadicBallInformation μ n x ∧
        dyadicInformation μ n x - dyadicBallInformation μ n x ≤
          (n : ℝ) * (1 / (k + 1 : ℝ)) * Real.log 2 := by
    apply ae_all_iff.mpr
    intro k
    exact ae_eventually_information_ball_error_le μ (by positivity)
  filter_upwards [hall] with x hx
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  filter_upwards [hx k, eventually_gt_atTop 0] with n hn hnpos
  have hden : 0 < (n : ℝ) * Real.log 2 :=
    mul_pos (by exact_mod_cast hnpos) (Real.log_pos (by norm_num))
  have hnonneg := div_nonneg hn.1 hden.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  apply lt_of_le_of_lt _ hk
  apply (div_le_iff₀ hden).mpr
  convert hn.2 using 1
  ring

theorem tendsto_dyadic_radius_nhdsWithin :
    Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ (-(n : ℤ))) atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have he (n : ℕ) : (2 : ℝ) ^ (-(n : ℤ)) = ((2 : ℝ)⁻¹) ^ n := by
      rw [zpow_neg, zpow_natCast, inv_pow]
    simp_rw [he]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  · exact Eventually.of_forall fun n ↦ zpow_pos (by norm_num) _

theorem ae_normalized_dyadicInformation_tendsto (μ : ProbabilityMeasure ℝ) {d : ℝ}
    (hd : ExactOverlaps.HasExactDimension (μ : Measure ℝ) d) :
    ∀ᵐ x ∂(μ : Measure ℝ), Tendsto
      (fun n : ℕ ↦ dyadicInformation μ n x / ((n : ℝ) * Real.log 2)) atTop (𝓝 d) := by
  filter_upwards [hd, ae_information_ball_error_tendsto_zero μ] with x hx herr
  have hb : Tendsto (fun n : ℕ ↦
      dyadicBallInformation μ n x / ((n : ℝ) * Real.log 2)) atTop (𝓝 d) := by
    have h := hx.comp tendsto_dyadic_radius_nhdsWithin
    simpa only [Function.comp_def, dyadicBallInformation, Real.log_zpow,
      Int.cast_neg, Int.cast_natCast, neg_mul, div_neg, neg_div] using h
  have h := hb.add herr
  simp only [add_zero] at h
  convert h using 1
  funext n
  ring

end ExactOverlaps.Entropy
