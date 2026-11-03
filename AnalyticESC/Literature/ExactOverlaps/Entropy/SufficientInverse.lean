module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.ManyUniformLevels
public import AnalyticESC.Literature.ExactOverlaps.Entropy.InverseGainEstimate
public import AnalyticESC.Literature.ExactOverlaps.Entropy.InverseScaleThresholds

set_option maxSynthPendingDepth 3

/-!
# A sufficient inverse entropy theorem

A law whose components have a fixed entropy deficit outside a separately
small exceptional mass gains entropy when convolved with any law of positive
entropy. The block depth is chosen sufficiently large after the deficit and
input entropy threshold. This order is sufficient for the self-similar
application through uniform entropy dimension.

The exceptional mass is e/32, independently specified from the entropy
deficit a; it is not identified with a. Every convolution, component law,
variance and Gaussian approximation used below is proved for the actual
Borel probability measures.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.SufficientInverse`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set

namespace ExactOverlaps.Entropy

theorem sufficient_inverse_entropy_at_depth {a e : ℝ} (ha : 0 < a) (he : 0 < e)
    {m : ℕ} (hm : 0 < m) (hdepth : 16 ≤ (m : ℝ) * e)
    (hresolution : 128 ≤ (m : ℝ) * a * e) :
    ∃ γ > 0, ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (μ ν : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν),
      (∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1) →
      (∀ᵐ x ∂(ν : Measure ℝ), x ∈ Icc (0 : ℝ) 1) →
      1 - e / 32 ≤ levelEntropyLowerTailMass μ hμ n m a →
      e < normalizedDyadicEntropy ν hν n →
      normalizedDyadicEntropy μ hμ n + γ ≤
        normalizedDyadicEntropy (realConvolution μ ν)
          (realConvolution_hasBoundedSupport μ ν hμ hν) n := by
  obtain ⟨k, hk, C, hC, hlevels⟩ := exists_many_uniform_levels_of_positive_entropy he
    (show 0 < a / 8 by positivity) hm hdepth
  have hae : 0 < a * e / 32 := by positivity
  obtain ⟨N₁, hN₁, hscale₁⟩ := exists_nat_div_le C (show 0 < e / 4 by positivity)
  obtain ⟨N₂, hN₂, hscale₂⟩ := exists_nat_div_le (2 * (m : ℝ) + 4 * k + 2) hae
  obtain ⟨N₃, hN₃, hscale₃⟩ := exists_nat_div_le (2 * (k : ℝ)) hae
  refine ⟨a * e / (32 * (k : ℝ)), by positivity,
    max N₁ (max N₂ N₃), lt_of_lt_of_le hN₁ (le_max_left _ _), ?_⟩
  intro n hn μ ν hμ hν hμunit hνunit hdeficient heν
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn₃ : N₃ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnpos : 0 < n := lt_of_lt_of_le hN₁ hn₁
  obtain ⟨I, hI, hdense, hgood⟩ := hlevels ν hν hνunit n hnpos (hscale₁ n hn₁) heν
  exact one_step_gain_of_many_uniform_levels μ ν hμ hν hμunit hνunit hnpos hm hk ha he
    hresolution (hscale₂ n hn₂) (hscale₃ n hn₃) hdeficient I hI hdense hgood

/-- Parameter order suitable for self-similar measures with uniform entropy dimension. -/
theorem exists_sufficient_inverse_entropy {a e : ℝ} (ha : 0 < a) (he : 0 < e) :
    ∃ M : ℕ, 0 < M ∧ ∀ m : ℕ, M ≤ m →
      ∃ γ > 0, ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (μ ν : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν),
      (∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1) →
      (∀ᵐ x ∂(ν : Measure ℝ), x ∈ Icc (0 : ℝ) 1) →
      1 - e / 32 ≤ levelEntropyLowerTailMass μ hμ n m a →
      e < normalizedDyadicEntropy ν hν n →
      normalizedDyadicEntropy μ hμ n + γ ≤
        normalizedDyadicEntropy (realConvolution μ ν)
          (realConvolution_hasBoundedSupport μ ν hμ hν) n := by
  obtain ⟨M, hM, hblock⟩ := exists_inverse_block_depth ha he
  refine ⟨M, hM, ?_⟩
  intro m hm
  exact sufficient_inverse_entropy_at_depth ha he (lt_of_lt_of_le hM hm)
    (hblock m hm).1 (hblock m hm).2

end ExactOverlaps.Entropy
