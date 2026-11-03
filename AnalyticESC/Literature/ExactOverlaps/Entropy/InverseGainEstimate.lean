module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.RepeatedGlobalGain

set_option maxSynthPendingDepth 3

/-!
# Quantitative one-step gain from many uniform convolution levels

The positive gain for a long repeated convolution is transferred back to a
single convolution by the proved Kaimanovich–Vershik estimate. All constants
and finite-scale errors are retained in the hypotheses and conclusion.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.InverseGainEstimate`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set

namespace ExactOverlaps.Entropy

theorem one_step_gain_of_many_uniform_levels (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν)
    (hμunit : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    (hνunit : ∀ᵐ x ∂(ν : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    {n m k : ℕ} (hn : 0 < n) (hm : 0 < m) (hk : 0 < k)
    {a e : ℝ} (ha : 0 < a) (he : 0 < e) (hdepth : 128 ≤ (m : ℝ) * a * e)
    (herror : (2 * (m : ℝ) + 4 * k + 2) / n ≤ a * e / 32)
    (hiteration : 2 * (k : ℝ) / n ≤ a * e / 32)
    (hdeficient : 1 - e / 32 ≤ levelEntropyLowerTailMass μ hμ n m a)
    (I : Finset ℕ) (hI : I ⊆ Finset.range n) (hdensity : (e / 4) * n < I.card)
    (hgood : ∀ i ∈ I, componentEntropyLowerTailMass (realConvolutionPower ν k)
      (realConvolutionPower_hasBoundedSupport ν hν k) i m (a / 8) ≤ a / 8) :
    normalizedDyadicEntropy μ hμ n + a * e / (32 * (k : ℝ)) ≤
      normalizedDyadicEntropy (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν) n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hae : 0 < a * e := mul_pos ha he
  have hglobal := normalizedConvolutionPowerEntropy_gain μ ν hμ hν hμunit hνunit hn hm k
    ha.le (show 0 ≤ a / 8 by positivity) I hI hgood
  have hboost : 3 * a * e / 16 ≤ (a - 2 * (a / 8)) * I.card / n := by
    have hd : e / 4 ≤ (I.card : ℝ) / n := ((lt_div_iff₀ hn').2 hdensity).le
    calc
      _ = (a - 2 * (a / 8)) * (e / 4) := by ring
      _ ≤ (a - 2 * (a / 8)) * ((I.card : ℝ) / n) :=
        mul_le_mul_of_nonneg_left hd (by linarith)
      _ = _ := by ring
  have hbad : a * (1 - levelEntropyLowerTailMass μ hμ n m a) ≤ a * e / 32 := by
    have h := mul_le_mul_of_nonneg_left (show 1 - levelEntropyLowerTailMass μ hμ n m a ≤ e / 32 by
      linarith) ha.le
    nlinarith
  have hresolution : 2 / (m : ℝ) ≤ a * e / 64 := (div_le_iff₀ hm').2 (by nlinarith)
  have hlong : normalizedDyadicEntropy μ hμ n + a * e / 16 ≤
      normalizedDyadicEntropy (realConvolution μ (realConvolutionPower ν k))
        (realConvolution_hasBoundedSupport μ _ hμ (realConvolutionPower_hasBoundedSupport ν hν k)) n := by
    linarith
  have hKV := normalizedDyadicEntropy_iteratedRealConvolution_le μ ν hμ hν hn k
  simp only [realConvolution_power_eq_iterated] at hlong
  have hprod : a * e / 32 ≤ (k : ℝ) *
      (normalizedDyadicEntropy (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν) n -
        normalizedDyadicEntropy μ hμ n) := by linarith
  have hδ : a * e / (32 * (k : ℝ)) ≤
      normalizedDyadicEntropy (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν) n -
        normalizedDyadicEntropy μ hμ n := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 32) hk')).2
    nlinarith
  linarith

end ExactOverlaps.Entropy
