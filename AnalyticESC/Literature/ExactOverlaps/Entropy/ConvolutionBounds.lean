module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.DyadicConvolution

set_option maxSynthPendingDepth 3

/-!
# Entropy bounds for bounded real convolutions

Convolution cannot decrease normalized dyadic entropy by more than `1/n`.
The estimate holds for arbitrary bounded probability measures, with atoms
allowed on all dyadic boundaries.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.ConvolutionBounds`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.Entropy

theorem dyadicEntropy_left_le_convolution_add_log_two
    (μ ν : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν) (i : ℤ) :
    dyadicEntropy μ hμ i ≤
      dyadicEntropy (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν) i +
        Real.log 2 := by
  have h := finiteEntropy_left_le_discreteConvolution (dyadicLaw μ i) (dyadicLaw ν i)
    (dyadicLaw_support_finite μ hμ i) (dyadicLaw_support_finite ν hν i)
  have hd := (abs_le.mp
    (abs_discreteConvolution_entropy_sub_dyadicEntropy_le_log_two μ ν hμ hν i)).2
  change dyadicEntropy μ hμ i ≤ _ at h
  linarith

theorem dyadicEntropy_right_le_convolution_add_log_two
    (μ ν : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν) (i : ℤ) :
    dyadicEntropy ν hν i ≤
      dyadicEntropy (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν) i +
        Real.log 2 := by
  have h := finiteEntropy_right_le_discreteConvolution (dyadicLaw μ i) (dyadicLaw ν i)
    (dyadicLaw_support_finite μ hμ i) (dyadicLaw_support_finite ν hν i)
  have hd := (abs_le.mp
    (abs_discreteConvolution_entropy_sub_dyadicEntropy_le_log_two μ ν hμ hν i)).2
  change dyadicEntropy ν hν i ≤ _ at h
  linarith

theorem dyadicEntropy_convolution_le_add_log_two
    (μ ν : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν) (i : ℤ) :
    dyadicEntropy (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν) i ≤
      dyadicEntropy μ hμ i + dyadicEntropy ν hν i + Real.log 2 := by
  have h := finiteEntropy_discreteConvolution_le_add (dyadicLaw μ i) (dyadicLaw ν i)
    (dyadicLaw_support_finite μ hμ i) (dyadicLaw_support_finite ν hν i)
  have hd := (abs_le.mp
    (abs_discreteConvolution_entropy_sub_dyadicEntropy_le_log_two μ ν hμ hν i)).1
  change _ ≤ dyadicEntropy μ hμ i + dyadicEntropy ν hν i at h
  linarith

/-- Normalized convolution monotonicity with the explicit dyadic boundary error. -/
theorem normalizedDyadicEntropy_left_le_convolution_add_inv
    (μ ν : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν)
    {n : ℕ} (hn : 0 < n) :
    normalizedDyadicEntropy μ hμ n ≤
      normalizedDyadicEntropy (realConvolution μ ν)
        (realConvolution_hasBoundedSupport μ ν hμ hν) n + 1 / (n : ℝ) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := div_le_div_of_nonneg_right
    (dyadicEntropy_left_le_convolution_add_log_two μ ν hμ hν n) (mul_pos hn' hlog).le
  have he : Real.log 2 / ((n : ℝ) * Real.log 2) = 1 / (n : ℝ) := by
    field_simp
  simpa only [add_div, he, normalizedDyadicEntropy] using h

end ExactOverlaps.Entropy
