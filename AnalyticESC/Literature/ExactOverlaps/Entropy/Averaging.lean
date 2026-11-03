module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.LocalEntropy

set_option maxSynthPendingDepth 3

/-!
# Global entropy from local entropy averages

The average ranges over levels `0 ≤ i < n`. The explicit error consists of a
window-length term and the entropy of the initial partition. This convention
avoids hiding endpoint adjustments in asymptotic notation.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.Averaging`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace ExactOverlaps.Entropy

lemma sum_window_differences (a : ℕ → ℝ) (n m : ℕ) :
    (∑ i ∈ Finset.range n, (a (i + m) - a i)) =
      ∑ j ∈ Finset.range m, (a (n + j) - a j) := by
  simp only [Finset.sum_sub_distrib]
  have h₁ := Finset.sum_range_add a n m
  have h₂ := Finset.sum_range_add a m n
  have he : (∑ i ∈ Finset.range n, a (i + m)) =
      ∑ i ∈ Finset.range n, a (m + i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_comm]
  rw [Nat.add_comm m n] at h₂
  rw [he]
  linarith

lemma abs_sum_entropy_windows_sub_le (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n m : ℕ) :
    |(∑ i ∈ Finset.range n, (dyadicEntropy μ hμ ((i + m : ℕ) : ℤ) -
      dyadicEntropy μ hμ i)) - (m : ℝ) * dyadicEntropy μ hμ n| ≤
      (m : ℝ) * (dyadicEntropy μ hμ 0 + (m : ℝ) * Real.log 2) := by
  let a : ℕ → ℝ := fun j ↦ dyadicEntropy μ hμ j
  let b : ℕ → ℝ := fun j ↦ a (n + j) - a j - a n
  have hL : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have ha (j : ℕ) : 0 ≤ a j := dyadicEntropy_nonneg μ hμ j
  have hincr (s t : ℕ) : a (s + t) - a s ≤ (t : ℝ) * Real.log 2 := by
    simpa only [a, Nat.cast_add] using dyadicEntropy_increment_le μ hμ (s : ℤ) t
  have hb (j : ℕ) (hj : j ∈ Finset.range m) : |b j| ≤ a 0 + (m : ℝ) * Real.log 2 := by
    have hjm : (j : ℝ) ≤ m := by exact_mod_cast (Finset.mem_range.mp hj).le
    have hscale := mul_le_mul_of_nonneg_right hjm hL
    have hsmall := hincr 0 j
    simp only [Nat.zero_add] at hsmall
    have hlarge := hincr n j
    have hmono : a n ≤ a (n + j) := by
      simpa only [a, Nat.cast_add] using dyadicEntropy_le_add_nat μ hμ (n : ℤ) j
    unfold b
    rw [abs_le]
    constructor <;> linarith [ha 0, ha j]
  change |(∑ i ∈ Finset.range n, (a (i + m) - a i)) - (m : ℝ) * a n| ≤ _
  rw [sum_window_differences]
  have he : (∑ j ∈ Finset.range m, (a (n + j) - a j)) - (m : ℝ) * a n =
      ∑ j ∈ Finset.range m, b j := by
    simp [b, Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ j ∈ Finset.range m, |b j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range m, (a 0 + (m : ℝ) * Real.log 2) :=
      Finset.sum_le_sum hb
    _ = (m : ℝ) * (dyadicEntropy μ hμ 0 + (m : ℝ) * Real.log 2) := by
      simp [a]
      ring

/-- The mean normalized component entropy over levels `0,…,n−1`. -/
noncomputable def levelAverageComponentEntropy (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n m : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, averageComponentEntropy μ hμ i m) / n

/-- A quantified local-to-global entropy identity with an explicit boundary error. -/
theorem abs_levelAverageComponentEntropy_sub_le (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    |levelAverageComponentEntropy μ hμ n m - normalizedDyadicEntropy μ hμ n| ≤
      (m : ℝ) / n + dyadicEntropy μ hμ 0 / ((n : ℝ) * Real.log 2) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < (n : ℝ) * m * Real.log 2 := mul_pos (mul_pos hn' hm') hL
  have he : levelAverageComponentEntropy μ hμ n m - normalizedDyadicEntropy μ hμ n =
      ((∑ i ∈ Finset.range n, (dyadicEntropy μ hμ ((i + m : ℕ) : ℤ) -
        dyadicEntropy μ hμ i)) - (m : ℝ) * dyadicEntropy μ hμ n) /
          ((n : ℝ) * m * Real.log 2) := by
    unfold levelAverageComponentEntropy normalizedDyadicEntropy
    simp only [averageComponentEntropy_eq_increment, Nat.cast_add]
    rw [← Finset.sum_div]
    field_simp
  rw [he, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  have hright : ((m : ℝ) / n + dyadicEntropy μ hμ 0 / ((n : ℝ) * Real.log 2)) *
      ((n : ℝ) * m * Real.log 2) =
      (m : ℝ) * (dyadicEntropy μ hμ 0 + (m : ℝ) * Real.log 2) := by
    field_simp
    ring
  rw [hright]
  exact abs_sum_entropy_windows_sub_le μ hμ n m

end ExactOverlaps.Entropy
