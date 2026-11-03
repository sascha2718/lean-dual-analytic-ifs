module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.VarianceLevelDensity
public import AnalyticESC.Literature.ExactOverlaps.Entropy.RepeatedUniformity
public import AnalyticESC.Literature.ExactOverlaps.Entropy.ShiftedLevelSets

set_option maxSynthPendingDepth 3

/-!
# Positive input entropy gives many uniform levels after convolution

The number of convolution factors is uniform over all input laws. The
endpoint threshold accounts explicitly for the integer square-root shift.
Only a positive-density conclusion is asserted, as needed for the sufficient
inverse theorem.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.ManyUniformLevels`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators Classical

namespace ExactOverlaps.Entropy

theorem exists_many_uniform_levels_of_positive_entropy {e δ : ℝ}
    (he : 0 < e) (hδ : 0 < δ) {m : ℕ} (hm : 0 < m) (hdepth : 16 ≤ (m : ℝ) * e) :
    ∃ k : ℕ, 0 < k ∧ ∃ C > 0, ∀ (ν : ProbabilityMeasure ℝ) (hν : HasBoundedSupport ν),
      (∀ᵐ x ∂(ν : Measure ℝ), x ∈ Icc (0 : ℝ) 1) →
      ∀ n : ℕ, 0 < n → C / n ≤ e / 4 → e < normalizedDyadicEntropy ν hν n →
      ∃ I : Finset ℕ, I ⊆ Finset.range n ∧ (e / 4) * n < I.card ∧
        ∀ i ∈ I, componentEntropyLowerTailMass (realConvolutionPower ν k)
          (realConvolutionPower_hasBoundedSupport ν hν k) i m δ ≤ δ := by
  obtain ⟨σ, hσ, hσdense⟩ := exists_component_variance_level_density he hm hdepth
  obtain ⟨p, k, hk, hp⟩ := exists_repeated_convolution_component_uniformity hσ hδ hm
  let s : ℤ := (p : ℤ) - dyadicSqrtScale k
  let C : ℝ := (m : ℝ) + 1 + 2 * s.natAbs
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨k, hk, C, hC, ?_⟩
  intro ν hν hunit n hn hsize heν
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsize₁ : ((m : ℝ) + 1) / n ≤ e / 4 := by
    apply le_trans _ hsize
    exact div_le_div_of_nonneg_right (by dsimp [C]; linarith [(show (0 : ℝ) ≤ (s.natAbs : ℝ) from Nat.cast_nonneg _)]) hn'.le
  have hsize₂ : 2 * (s.natAbs : ℝ) ≤ (e / 4) * n := by
    have h : C ≤ (e / 4) * n := (div_le_iff₀ hn').1 hsize
    dsimp only [C] at h
    linarith [(show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg _)]
  let A := (Finset.range n).filter (fun i : ℕ ↦ σ < averageComponentVariance ν hν (i : ℤ))
  have hA : A ⊆ Finset.range n := Finset.filter_subset _ _
  have hdense : (e / 2) * n < (A.card : ℝ) := hσdense ν hν hunit n hn hsize₁ heν
  obtain ⟨I, hI, hcard, hshift⟩ := exists_shifted_level_set A hA s
  refine ⟨I, hI, ?_, ?_⟩
  · have hc : (A.card : ℝ) ≤ (I.card : ℝ) + 2 * (s.natAbs : ℝ) := by exact_mod_cast hcard
    linarith
  · intro i hi
    obtain ⟨j, hj, hji⟩ := hshift i hi
    have hjvar := (Finset.mem_filter.mp hj).2
    have h := (hp k le_rfl ν hν j hjvar).le
    convert h using 1
    congr 1
    dsimp only [s] at hji
    omega

end ExactOverlaps.Entropy
