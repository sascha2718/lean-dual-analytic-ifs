module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.GaussianCentralMass
public import AnalyticESC.Literature.ExactOverlaps.Entropy.CellApproximation

set_option maxSynthPendingDepth 3

/-!
# Stability of the mass of central cell blocks

A consecutive block of half-open dyadic cells is a single half-open interval.
Its probability transfers with one interval error, independently of the
number of constituent cells and without assumptions about boundary atoms.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.CentralCellApproximation`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace ExactOverlaps.Entropy

lemma dyadicQuantize_preimage_Icc (i a b : ℤ) :
    {x : ℝ | dyadicQuantize i x ∈ Finset.Icc a b} =
      Ico ((a : ℝ) / (2 : ℝ) ^ i) (((b : ℝ) + 1) / (2 : ℝ) ^ i) := by
  ext x
  simp only [Set.mem_ofPred_eq, Finset.mem_Icc, mem_Ico, dyadicQuantize,
    Int.le_floor, Int.floor_le_iff, div_le_iff₀ (dyadic_scale_pos i),
    lt_div_iff₀ (dyadic_scale_pos i), mul_comm]

theorem dyadicLaw_Icc_mass_error (μ ν : ProbabilityMeasure ℝ) {ε : ℝ}
    (hclose : ∀ a b : ℝ, |((μ : Measure ℝ) (Ico a b)).toReal -
      ((ν : Measure ℝ) (Ico a b)).toReal| ≤ ε) (i a b : ℤ) :
    |(∑ k ∈ Finset.Icc a b, ((dyadicLaw μ i) k).toReal) -
      ∑ k ∈ Finset.Icc a b, ((dyadicLaw ν i) k).toReal| ≤ ε := by
  rw [dyadicLaw_finset_mass, dyadicLaw_finset_mass, dyadicQuantize_preimage_Icc]
  exact hclose _ _

theorem central_labels_mass_ge_of_gaussian_interval_error (μ : ProbabilityMeasure ℝ)
    (b : ℝ) (v : ℝ≥0) {ε : ℝ}
    (hclose : ∀ a c : ℝ, |((μ : Measure ℝ) (Ico a c)).toReal -
      (gaussianReal b v (Ico a c)).toReal| ≤ ε) (i : ℤ) {R : ℝ} (hR : 0 < R) :
    1 - (v : ℝ) / R ^ 2 - ε ≤
      ∑ k ∈ Finset.Icc (dyadicQuantize i (b - R)) (dyadicQuantize i (b + R)),
        ((dyadicLaw μ i) k).toReal := by
  have h := (abs_le.mp (dyadicLaw_Icc_mass_error μ (gaussianProbability b v)
    hclose i (dyadicQuantize i (b - R)) (dyadicQuantize i (b + R)))).1
  have hg := gaussian_central_labels_mass_ge b v i hR
  linarith

end ExactOverlaps.Entropy
