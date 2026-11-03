module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.TupleConvolution
public import AnalyticESC.Literature.ExactOverlaps.Entropy.RepeatedGrowth
public import AnalyticESC.Literature.ExactOverlaps.Entropy.ConvolutionAveraging

set_option maxSynthPendingDepth 3

/-!
# Coarse entropy and repeated convolution identities

The repeated convolution appearing in the Gaussian argument equals the
iteration controlled by Kaimanovich–Vershik. Unit-supported inputs have a
uniform explicit coarse-entropy bound, sufficient for all averaging errors.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.RepeatedCoarseBounds`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set

namespace ExactOverlaps.Entropy

lemma realConvolution_power_eq_iterated (μ ν : ProbabilityMeasure ℝ) (k : ℕ) :
    realConvolution μ (realConvolutionPower ν k) = iteratedRealConvolution μ ν k := by
  induction k with
  | zero => exact realConvolution_zero_right μ
  | succ k ih =>
    change realConvolution μ (realConvolution ν (realConvolutionPower ν k)) =
      realConvolution (iteratedRealConvolution μ ν k) ν
    rw [realConvolution_comm ν (realConvolutionPower ν k), ← realConvolution_assoc, ih]

lemma dyadicEntropy_convolution_power_zero_le (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν)
    (hμunit : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hνunit : ∀ᵐ x ∂(ν : Measure ℝ), x ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    dyadicEntropy (realConvolution μ (realConvolutionPower ν k))
      (realConvolution_hasBoundedSupport μ _ hμ (realConvolutionPower_hasBoundedSupport ν hν k)) 0 ≤
      (4 * (k : ℝ) + 1) * Real.log 2 := by
  have hμ0 := dyadicEntropy_zero_le_log_two_of_closed_unit_support μ hμ hμunit
  have hν0 := dyadicEntropy_zero_le_log_two_of_closed_unit_support ν hν hνunit
  have hc := dyadicEntropy_convolution_le_add_log_two μ ν hμ hν 0
  have h := dyadicEntropy_iteratedRealConvolution_le_linear_error μ ν hμ hν 0 k
  have hmul := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg k)
  have hmulν := mul_le_mul_of_nonneg_left hν0 (Nat.cast_nonneg k)
  simp only [realConvolution_power_eq_iterated]
  nlinarith

end ExactOverlaps.Entropy
