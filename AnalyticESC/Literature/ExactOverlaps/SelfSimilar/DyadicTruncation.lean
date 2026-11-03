module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.InformationTruncation
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.DyadicSupportGrowth
public import Mathlib.Analysis.SpecificLimits.Basic

set_option maxSynthPendingDepth 3

/-! Uniform information-tail control for bounded real probability measures. 

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.DyadicTruncation`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps.Entropy

noncomputable def dyadicTruncationError (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (L : ℝ) (n : ℕ) : ℝ :=
  dyadicEntropy μ hμ n - truncatedFiniteEntropy (dyadicLaw μ n)
    (dyadicLaw_support_finite μ hμ n) (L * ((n : ℝ) * Real.log 2))

theorem dyadicTruncationError_bounds (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    {L : ℝ} (hL : 4 ≤ L) (n : ℕ) :
    0 ≤ dyadicTruncationError μ hμ L n ∧
      dyadicTruncationError μ hμ L n ≤
        2 * (dyadicLaw_support_finite μ hμ 0).toFinset.card * (1 / 2 : ℝ) ^ n := by
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hden : 0 ≤ (n : ℝ) * Real.log 2 :=
    mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg (by norm_num))
  have h := finiteEntropy_sub_truncated_bounds (dyadicLaw μ n)
    (dyadicLaw_support_finite μ hμ n) (mul_nonneg hL0 hden)
  refine ⟨h.1, h.2.trans ?_⟩
  have hcount : ((dyadicLaw_support_finite μ hμ n).toFinset.card : ℝ) ≤
      (dyadicLaw_support_finite μ hμ 0).toFinset.card * (2 : ℝ) ^ n := by
    exact_mod_cast dyadicLaw_card_le_base_mul_pow μ hμ n
  have hexp : Real.exp (-(L * ((n : ℝ) * Real.log 2)) / 2) ≤
      Real.exp (-2 * (n : ℝ) * Real.log 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hL hden]
  have hexact : Real.exp (-2 * (n : ℝ) * Real.log 2) = ((1 / 2 : ℝ) ^ 2) ^ n := by
    rw [show -2 * (n : ℝ) * Real.log 2 = (n : ℝ) * (-2 * Real.log 2) by ring,
      Real.exp_nat_mul]
    congr 1
    rw [show -2 * Real.log 2 = -(Real.log 2 + Real.log 2) by ring,
      Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  calc
    _ ≤ 2 * ((dyadicLaw_support_finite μ hμ 0).toFinset.card * (2 : ℝ) ^ n) *
        Real.exp (-2 * (n : ℝ) * Real.log 2) := by gcongr
    _ = 2 * (dyadicLaw_support_finite μ hμ 0).toFinset.card *
        ((2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ 2) ^ n) := by rw [hexact]; ring
    _ = _ := by rw [← mul_pow]; norm_num

theorem dyadicTruncationError_tendsto_zero (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    {L : ℝ} (hL : 4 ≤ L) : Tendsto (dyadicTruncationError μ hμ L) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply squeeze_zero (fun n ↦ (dyadicTruncationError_bounds μ hμ hL n).1)
    (fun n ↦ (dyadicTruncationError_bounds μ hμ hL n).2)
  simpa only [mul_zero] using hp.const_mul
    (2 * (dyadicLaw_support_finite μ hμ 0).toFinset.card : ℝ)

noncomputable def truncatedNormalizedInformation (μ : ProbabilityMeasure ℝ)
    (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  min (dyadicInformation μ n x) (L * ((n : ℝ) * Real.log 2)) / ((n : ℝ) * Real.log 2)

theorem normalized_entropy_truncation_error_tendsto_zero (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) {L : ℝ} (hL : 4 ≤ L) :
    Tendsto (fun n : ℕ ↦ normalizedDyadicEntropy μ hμ n -
      ∫ x, truncatedNormalizedInformation μ L n x ∂(μ : Measure ℝ)) atTop (𝓝 0) := by
  have hden : Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.log 2) atTop atTop := by
    simpa only [mul_comm] using
      Tendsto.const_mul_atTop (Real.log_pos (by norm_num : (1 : ℝ) < 2)) tendsto_natCast_atTop_atTop
  have h := (dyadicTruncationError_tendsto_zero μ hμ hL).div_atTop hden
  convert h using 1
  funext n
  have hT : 0 ≤ L * ((n : ℝ) * Real.log 2) :=
    mul_nonneg (le_trans (by norm_num) hL)
      (mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg (by norm_num)))
  simp only [truncatedNormalizedInformation, integral_div,
    integral_min_dyadicInformation μ hμ n hT, normalizedDyadicEntropy, dyadicTruncationError,
    sub_div]

end ExactOverlaps.Entropy
