module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.VarianceEntropyMean
public import AnalyticESC.Literature.ExactOverlaps.Entropy.ConvolutionAveraging

set_option maxSynthPendingDepth 3

/-!
# Positive entropy forces many variable component levels

At a sufficiently long block depth, low mean component variance forces low
mean component entropy. The local-to-global entropy identity therefore
forces a positive density of levels with variance above a uniform threshold.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.VarianceLevelDensity`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators Classical

namespace ExactOverlaps.Entropy

theorem exists_component_variance_level_density {e : ℝ} (he : 0 < e)
    {m : ℕ} (hm : 0 < m) (hdepth : 16 ≤ (m : ℝ) * e) :
    ∃ σ > 0, ∀ (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ),
      (∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1) →
      ∀ n : ℕ, 0 < n → ((m : ℝ) + 1) / n ≤ e / 4 →
      e < normalizedDyadicEntropy μ hμ n →
      (e / 2) * n < ((Finset.range n).filter (fun i : ℕ ↦ σ < averageComponentVariance μ hμ (i : ℤ))).card := by
  obtain ⟨η, hη, hηE⟩ := exists_component_entropy_variance_bound hm
  refine ⟨η * e / 8, by positivity, ?_⟩
  intro μ hμ hunit n hn hsize hentropy
  classical
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hblock : 2 / (m : ℝ) ≤ e / 8 := (div_le_iff₀ hm').2 (by nlinarith)
  have hsmall (i : ℕ) (hi : averageComponentVariance μ hμ i ≤ η * e / 8) :
      averageComponentEntropy μ hμ i m ≤ e / 4 := by
    have hv : averageComponentVariance μ hμ i / η ≤ e / 8 :=
      (div_le_iff₀ hη).2 (by nlinarith)
    linarith [hηE μ hμ i]
  let I := (Finset.range n).filter (fun i : ℕ ↦ η * e / 8 < averageComponentVariance μ hμ (i : ℤ))
  have hsum : (∑ i ∈ Finset.range n, averageComponentEntropy μ hμ i m) ≤
      (n : ℝ) * (e / 4) + I.card := by
    have hp (i : ℕ) : averageComponentEntropy μ hμ i m ≤ e / 4 +
        (if η * e / 8 < averageComponentVariance μ hμ i then (1 : ℝ) else 0) := by
      split_ifs with hi
      · linarith [averageComponentEntropy_le_one μ hμ (i : ℤ) hm]
      · simpa only [add_zero] using hsmall i (le_of_not_gt hi)
    have h := Finset.sum_le_sum (s := Finset.range n) (fun i _ ↦ hp i)
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, I] using h
  have hz := div_le_div_of_nonneg_right
    (dyadicEntropy_zero_le_log_two_of_closed_unit_support μ hμ hunit) (mul_pos hn' hlog).le
  have heq : Real.log 2 / ((n : ℝ) * Real.log 2) = 1 / (n : ℝ) := by field_simp
  rw [heq] at hz
  have hav := (abs_le.mp (abs_levelAverageComponentEntropy_sub_le μ hμ hn hm)).1
  have hsumdiv := div_le_div_of_nonneg_right hsum hn'.le
  change levelAverageComponentEntropy μ hμ n m ≤
    ((n : ℝ) * (e / 4) + I.card) / n at hsumdiv
  have hrhs : ((n : ℝ) * (e / 4) + I.card) / n = e / 4 + (I.card : ℝ) / n := by
    field_simp
  rw [hrhs] at hsumdiv
  have hcard : e / 2 < (I.card : ℝ) / n := by
    have herr : (m : ℝ) / n + 1 / (n : ℝ) ≤ e / 4 := by
      rw [← add_div]
      exact hsize
    linarith
  exact (lt_div_iff₀ hn').1 hcard

end ExactOverlaps.Entropy
