module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.GlobalConvolutionGain
public import AnalyticESC.Literature.ExactOverlaps.Entropy.RepeatedCoarseBounds

set_option maxSynthPendingDepth 3

/-!
# The explicit global gain for a repeated second factor

For unit-supported inputs, the coarse partition terms are bounded uniformly
in the laws. This leaves only the explicit errors 2/m and (2m+4k+2)/n.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.RepeatedGlobalGain`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set

namespace ExactOverlaps.Entropy

theorem normalizedConvolutionPowerEntropy_gain (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν)
    (hμunit : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hνunit : ∀ᵐ x ∂(ν : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (k : ℕ)
    {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (I : Finset ℕ) (hI : I ⊆ Finset.range n)
    (hgood : ∀ i ∈ I, componentEntropyLowerTailMass (realConvolutionPower ν k)
      (realConvolutionPower_hasBoundedSupport ν hν k) i m δ ≤ δ) :
    normalizedDyadicEntropy μ hμ n + (a - 2 * δ) * I.card / n -
      a * (1 - levelEntropyLowerTailMass μ hμ n m a) - 2 / (m : ℝ) -
      (2 * (m : ℝ) + 4 * k + 2) / n ≤
        normalizedDyadicEntropy (realConvolution μ (realConvolutionPower ν k))
          (realConvolution_hasBoundedSupport μ _ hμ (realConvolutionPower_hasBoundedSupport ν hν k)) n := by
  have h := normalizedConvolutionEntropy_gain μ (realConvolutionPower ν k) hμ
    (realConvolutionPower_hasBoundedSupport ν hν k) hn hm ha hδ I hI hgood
  have hzμ := dyadicEntropy_zero_le_log_two_of_closed_unit_support μ hμ hμunit
  have hzc := dyadicEntropy_convolution_power_zero_le μ ν hμ hν hμunit hνunit k
  have hz : dyadicEntropy μ hμ 0 + dyadicEntropy (realConvolution μ (realConvolutionPower ν k))
      (realConvolution_hasBoundedSupport μ _ hμ (realConvolutionPower_hasBoundedSupport ν hν k)) 0 ≤
      (4 * (k : ℝ) + 2) * Real.log 2 := by linarith
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd := div_le_div_of_nonneg_right hz (mul_pos hn' hl).le
  have he : (4 * (k : ℝ) + 2) * Real.log 2 / ((n : ℝ) * Real.log 2) =
      (4 * (k : ℝ) + 2) / n := by field_simp
  rw [he] at hd
  have he' : (2 * (m : ℝ) + 4 * k + 2) / n =
      2 * (m : ℝ) / n + (4 * (k : ℝ) + 2) / n := by ring
  rw [he']
  linarith

end ExactOverlaps.Entropy
