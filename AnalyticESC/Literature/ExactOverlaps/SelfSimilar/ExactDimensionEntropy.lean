module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.LocalDimensionInformation
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.DyadicTruncation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option maxSynthPendingDepth 3

/-!
For a bounded real probability measure, genuine almost-sure exact dimension
implies convergence of normalized dyadic entropy to that dimension. The
proof establishes pointwise information convergence, controls the tails,
and applies dominated convergence to the truncated information.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.ExactDimensionEntropy`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps.Entropy

theorem truncatedNormalizedInformation_eq_min (μ : ProbabilityMeasure ℝ)
    (L : ℝ) {n : ℕ} (hn : 0 < n) (x : ℝ) :
    truncatedNormalizedInformation μ L n x =
      min (dyadicInformation μ n x / ((n : ℝ) * Real.log 2)) L := by
  have hden : 0 < (n : ℝ) * Real.log 2 :=
    mul_pos (by exact_mod_cast hn) (Real.log_pos (by norm_num))
  unfold truncatedNormalizedInformation
  rw [← min_div_div_right hden.le, mul_div_cancel_right₀ _ hden.ne']

theorem truncatedNormalizedInformation_bounds (μ : ProbabilityMeasure ℝ)
    {L : ℝ} (hL : 0 ≤ L) (n : ℕ) (x : ℝ) :
    0 ≤ truncatedNormalizedInformation μ L n x ∧
      truncatedNormalizedInformation μ L n x ≤ L := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [truncatedNormalizedInformation, hL]
  · rw [truncatedNormalizedInformation_eq_min μ L hn x]
    refine ⟨le_min ?_ hL, min_le_right _ _⟩
    exact div_nonneg (dyadicInformation_nonneg μ n x)
      (mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg (by norm_num)))

/-- The entropy dimension equals the standard almost-sure local dimension. -/
theorem normalized_entropy_limit_of_exact_dimension (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) {d : ℝ} (hd : ExactOverlaps.HasExactDimension (μ : Measure ℝ) d) :
    Tendsto (normalizedDyadicEntropy μ hμ) atTop (𝓝 d) := by
  let L : ℝ := 4 + |d|
  have hL : 4 ≤ L := le_add_of_nonneg_right (abs_nonneg d)
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hdL : d ≤ L := by have := le_abs_self d; dsimp [L]; linarith
  have hlim : ∀ᵐ x ∂(μ : Measure ℝ), Tendsto
      (fun n : ℕ ↦ truncatedNormalizedInformation μ L n x) atTop (𝓝 d) := by
    filter_upwards [ae_normalized_dyadicInformation_tendsto μ hd] with x hx
    have h := hx.min (tendsto_const_nhds (x := L))
    rw [min_eq_left hdL] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact (truncatedNormalizedInformation_eq_min μ L hn x).symm
  have htrunc : Tendsto (fun n : ℕ ↦
      ∫ x, truncatedNormalizedInformation μ L n x ∂(μ : Measure ℝ)) atTop (𝓝 d) := by
    have h := tendsto_integral_of_dominated_convergence (fun _ : ℝ ↦ L)
      (fun n ↦ ?_) (integrable_const L) (fun n ↦ ?_) hlim
    · simpa using h
    · apply Measurable.aestronglyMeasurable
      exact ((measurable_dyadicInformation μ n).min measurable_const).div_const _
    · apply ae_of_all
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (truncatedNormalizedInformation_bounds μ hL0 n x).1]
      exact (truncatedNormalizedInformation_bounds μ hL0 n x).2
  have herr := normalized_entropy_truncation_error_tendsto_zero μ hμ hL
  simpa only [sub_add_cancel, zero_add] using herr.add htrunc

end ExactOverlaps.Entropy
