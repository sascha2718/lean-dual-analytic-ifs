module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.RepeatedRealConvolution

set_option maxSynthPendingDepth 3

/-!
# Repeated convolution controlled by one entropy increment

This is the normalized real-measure consequence of Kaimanovich–Vershik and
the proved dyadic carry coupling. The error is explicitly at most `2*k/n`.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.RepeatedGrowth`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.Entropy

lemma log_nat_add_one_le_mul_log_two (k : ℕ) :
    Real.log ((k : ℝ) + 1) ≤ (k : ℝ) * Real.log 2 := by
  have hk : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
    simpa only [one_mul, show (1 : ℝ) + 1 = 2 by norm_num] using
      Real.mul_add_one_le_add_one_pow (a := 1) (by norm_num) k
  calc
    _ ≤ Real.log ((2 : ℝ) ^ k) := Real.log_le_log (by positivity) hk
    _ = _ := by rw [Real.log_pow]

theorem dyadicEntropy_iteratedRealConvolution_le_linear_error
    (μ ν : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν)
    (i : ℤ) (k : ℕ) :
    dyadicEntropy (iteratedRealConvolution μ ν k)
      (iteratedRealConvolution_hasBoundedSupport μ ν hμ hν k) i ≤
    dyadicEntropy μ hμ i + (k : ℝ) *
      (dyadicEntropy (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν) i -
        dyadicEntropy μ hμ i) + 2 * (k : ℝ) * Real.log 2 := by
  have h := dyadicEntropy_iteratedRealConvolution_le μ ν hμ hν i k
  have hk := log_nat_add_one_le_mul_log_two k
  nlinarith

/-- The real repeated-convolution entropy bound with the explicit `2*k/n` error. -/
theorem normalizedDyadicEntropy_iteratedRealConvolution_le
    (μ ν : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν)
    {n : ℕ} (hn : 0 < n) (k : ℕ) :
    normalizedDyadicEntropy (iteratedRealConvolution μ ν k)
      (iteratedRealConvolution_hasBoundedSupport μ ν hμ hν k) n ≤
    normalizedDyadicEntropy μ hμ n + (k : ℝ) *
      (normalizedDyadicEntropy (realConvolution μ ν)
          (realConvolution_hasBoundedSupport μ ν hμ hν) n -
        normalizedDyadicEntropy μ hμ n) + 2 * (k : ℝ) / n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := div_le_div_of_nonneg_right
    (dyadicEntropy_iteratedRealConvolution_le_linear_error μ ν hμ hν n k) (mul_pos hn' hlog).le
  unfold normalizedDyadicEntropy
  apply h.trans_eq
  field_simp

end ExactOverlaps.Entropy
