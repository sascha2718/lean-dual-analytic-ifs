module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.ComponentConvolution

set_option maxSynthPendingDepth 3

/-!
# Global convolution entropy from local component convolutions

Uniformly select a level below n and independently select one component of
each input at that level. The mean m-scale entropy of their convolution is
bounded by the global n-scale convolution entropy with explicit endpoint errors.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.ConvolutionAveraging`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ExactOverlaps.Entropy

noncomputable def levelAverageConvolutionComponentEntropy (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν) (n m : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, averageConvolutionComponentEntropy μ ν hμ hν i m) / n

theorem levelAverageConvolutionComponentEntropy_le (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    levelAverageConvolutionComponentEntropy μ ν hμ hν n m ≤
      normalizedDyadicEntropy (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν) n +
        (m : ℝ) / n +
        dyadicEntropy (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν) 0 /
          ((n : ℝ) * Real.log 2) + 1 / (m : ℝ) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsum : (∑ i ∈ Finset.range n, averageConvolutionComponentEntropy μ ν hμ hν i m) ≤
      (∑ i ∈ Finset.range n, averageComponentEntropy (realConvolution μ ν)
        (realConvolution_hasBoundedSupport μ ν hμ hν) i m) + (n : ℝ) * (1 / (m : ℝ)) := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, (averageComponentEntropy (realConvolution μ ν)
          (realConvolution_hasBoundedSupport μ ν hμ hν) i m + 1 / (m : ℝ)) :=
        Finset.sum_le_sum (fun i _ ↦ averageConvolutionComponentEntropy_le μ ν hμ hν i hm)
      _ = _ := by simp [Finset.sum_add_distrib]
  have hav := div_le_div_of_nonneg_right hsum hn'.le
  have he : (n : ℝ) * (1 / (m : ℝ)) / n = 1 / (m : ℝ) := by field_simp
  rw [add_div, he] at hav
  change levelAverageConvolutionComponentEntropy μ ν hμ hν n m ≤
    levelAverageComponentEntropy (realConvolution μ ν)
      (realConvolution_hasBoundedSupport μ ν hμ hν) n m + 1 / (m : ℝ) at hav
  have h := (abs_le.mp (abs_levelAverageComponentEntropy_sub_le
    (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν) hn hm)).2
  linarith

lemma dyadicEntropy_zero_le_log_two_of_closed_unit_support (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hunit : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1) :
    dyadicEntropy μ hμ 0 ≤ Real.log 2 := by
  apply finiteEntropy_le_log_of_card_le (dyadicLaw μ 0) (dyadicLaw_support_finite μ hμ 0) (N := 2)
  have hsub : (dyadicLaw_support_finite μ hμ 0).toFinset ⊆ Finset.Icc (0 : ℤ) 1 := by
    intro k hk
    have h := dyadicLaw_support_subset μ 0 hunit (by simpa using hk)
    simpa [dyadicQuantize] using h
  exact (Finset.card_le_card hsub).trans_eq (by decide)

/-- The local convolution estimate for the paper's closed unit-interval inputs. -/
theorem localConvolutionEntropy_lower_bound_of_unit_support (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν)
    (hμunit : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hνunit : ∀ᵐ x ∂(ν : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    levelAverageConvolutionComponentEntropy μ ν hμ hν n m -
      (((m : ℝ) + 3) / n + 1 / (m : ℝ)) ≤
        normalizedDyadicEntropy (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν) n := by
  have hzero : dyadicEntropy (realConvolution μ ν)
      (realConvolution_hasBoundedSupport μ ν hμ hν) 0 ≤ 3 * Real.log 2 := by
    have h := dyadicEntropy_convolution_le_add_log_two μ ν hμ hν 0
    have hμ0 := dyadicEntropy_zero_le_log_two_of_closed_unit_support μ hμ hμunit
    have hν0 := dyadicEntropy_zero_le_log_two_of_closed_unit_support ν hν hνunit
    linarith
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hz := div_le_div_of_nonneg_right hzero (mul_pos hn' hlog).le
  have he : 3 * Real.log 2 / ((n : ℝ) * Real.log 2) = 3 / (n : ℝ) := by field_simp
  rw [he] at hz
  have h := levelAverageConvolutionComponentEntropy_le μ ν hμ hν hn hm
  rw [add_div]
  linarith

end ExactOverlaps.Entropy
