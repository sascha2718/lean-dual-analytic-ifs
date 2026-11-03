module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.LocalConvolutionGain

set_option maxSynthPendingDepth 3

/-!
# Global entropy gain on a set of uniform component levels

The entropy deficit of the first law is charged globally, so a small total
exceptional mass suffices even when the good levels of the second law are
chosen adaptively. Every averaging and dyadic carry error is explicit.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.GlobalConvolutionGain`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

theorem levelAverageConvolutionEntropy_gain (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (I : Finset ℕ) (hI : I ⊆ Finset.range n)
    (hgood : ∀ i ∈ I, componentEntropyLowerTailMass ν hν i m δ ≤ δ) :
    levelAverageComponentEntropy μ hμ n m + (a - 2 * δ) * I.card / n -
      a * (1 - levelEntropyLowerTailMass μ hμ n m a) - 1 / (m : ℝ) ≤
        levelAverageConvolutionComponentEntropy μ ν hμ hν n m := by
  classical
  have hpoint (i : ℕ) : averageComponentEntropy μ hμ i m +
      (if i ∈ I then a - 2 * δ else 0) -
      a * (1 - componentEntropyLowerTailMass μ hμ i m a) - 1 / (m : ℝ) ≤
        averageConvolutionComponentEntropy μ ν hμ hν i m := by
    by_cases hi : i ∈ I
    · simp only [hi, ite_true]
      have h := localConvolutionEntropy_gain μ ν hμ hν i hm a hδ
      have hg := hgood i hi
      nlinarith
    · simp only [hi, ite_false, add_zero]
      have h := averageComponentEntropy_left_le_convolution_add_inv μ ν hμ hν i hm
      have hb := componentEntropyLowerTailMass_le_one μ hμ i m a
      nlinarith
  have hs := Finset.sum_le_sum (s := Finset.range n) (fun i _ ↦ hpoint i)
  have hfilter : (Finset.range n).filter (fun i ↦ i ∈ I) = I := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h ↦ h.2, fun hi ↦ ⟨hI hi, hi⟩⟩
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_filter, hfilter,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hs
  have hd := div_le_div_of_nonneg_right hs (Nat.cast_nonneg n)
  unfold levelAverageComponentEntropy levelEntropyLowerTailMass levelAverageConvolutionComponentEntropy
  apply le_trans _ hd
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  apply le_of_eq
  field_simp

theorem normalizedConvolutionEntropy_gain (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (I : Finset ℕ) (hI : I ⊆ Finset.range n)
    (hgood : ∀ i ∈ I, componentEntropyLowerTailMass ν hν i m δ ≤ δ) :
    normalizedDyadicEntropy μ hμ n + (a - 2 * δ) * I.card / n -
      a * (1 - levelEntropyLowerTailMass μ hμ n m a) - 2 / (m : ℝ) -
      2 * (m : ℝ) / n -
      (dyadicEntropy μ hμ 0 + dyadicEntropy (realConvolution μ ν)
        (realConvolution_hasBoundedSupport μ ν hμ hν) 0) / ((n : ℝ) * Real.log 2) ≤
        normalizedDyadicEntropy (realConvolution μ ν)
          (realConvolution_hasBoundedSupport μ ν hμ hν) n := by
  have hgain := levelAverageConvolutionEntropy_gain μ ν hμ hν hn hm ha hδ I hI hgood
  have hμavg := (abs_le.mp (abs_levelAverageComponentEntropy_sub_le μ hμ hn hm)).1
  have hconv := levelAverageConvolutionComponentEntropy_le μ ν hμ hν hn hm
  have he₁ : (2 : ℝ) / m = 2 * (1 / (m : ℝ)) := by ring
  have he₂ : 2 * (m : ℝ) / n = 2 * ((m : ℝ) / n) := by ring
  rw [add_div, he₁, he₂]
  linarith

end ExactOverlaps.Entropy
