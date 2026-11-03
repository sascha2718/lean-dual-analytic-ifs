module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.DensityComponent

set_option maxSynthPendingDepth 3

/-!
# Stability of conditional cell masses under interval approximation

Uniform errors in actual half-open interval masses control conditional fine
cell masses whenever the reference coarse cell has a positive lower mass.
No absence of atoms is assumed for either law.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.CellApproximation`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.Entropy

lemma ratio_le_of_mass_errors {p q p₀ q₀ A B c ε : ℝ}
    (hq : 0 < q) (hA : 0 ≤ A) (hAB : A ≤ B) (hc : c ≤ q₀)
    (hpq : p₀ ≤ A * q₀) (hp : |p - p₀| ≤ ε) (hqq : |q - q₀| ≤ ε)
    (hε : (B + 1) * ε ≤ (B - A) * c) : p / q ≤ B := by
  apply (div_le_iff₀ hq).2
  have hp' := (abs_le.mp hp).2
  have hq' := (abs_le.mp hqq).1
  have hgap := mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr hAB)
  have hB : 0 ≤ B := hA.trans hAB
  have hden := mul_le_mul_of_nonneg_left hq' hB
  nlinarith

lemma dyadicCell_mass_error_of_interval_error (μ ν : ProbabilityMeasure ℝ) {ε : ℝ}
    (hclose : ∀ a b : ℝ, |((μ : Measure ℝ) (Ico a b)).toReal -
      ((ν : Measure ℝ) (Ico a b)).toReal| ≤ ε) (i k : ℤ) :
    |((μ : Measure ℝ) (dyadicCell i k)).toReal -
      ((ν : Measure ℝ) (dyadicCell i k)).toReal| ≤ ε := by
  rw [dyadicCell_eq_Ico]
  exact hclose _ _

lemma dyadicCell_inter_mass_error_of_interval_error (μ ν : ProbabilityMeasure ℝ) {ε : ℝ}
    (hclose : ∀ a b : ℝ, |((μ : Measure ℝ) (Ico a b)).toReal -
      ((ν : Measure ℝ) (Ico a b)).toReal| ≤ ε) (i k j ℓ : ℤ) :
    |((μ : Measure ℝ) (dyadicCell i k ∩ dyadicCell j ℓ)).toReal -
      ((ν : Measure ℝ) (dyadicCell i k ∩ dyadicCell j ℓ)).toReal| ≤ ε := by
  rw [dyadicCell_eq_Ico, dyadicCell_eq_Ico, Ico_inter_Ico]
  exact hclose _ _

theorem rawComponent_atom_le_of_interval_error (μ ν : ProbabilityMeasure ℝ)
    {ε A B c : ℝ}
    (hclose : ∀ a b : ℝ, |((μ : Measure ℝ) (Ico a b)).toReal -
      ((ν : Measure ℝ) (Ico a b)).toReal| ≤ ε)
    (i : ℤ) (k : (dyadicLaw μ i).support) (m : ℕ)
    (hA : 0 ≤ A) (hAB : A ≤ B)
    (hc : c ≤ ((ν : Measure ℝ) (dyadicCell i k)).toReal)
    (href : ∀ j : ℤ, ((ν : Measure ℝ) (dyadicCell i k ∩ dyadicCell (i + m) j)).toReal ≤
      A * ((ν : Measure ℝ) (dyadicCell i k)).toReal)
    (hε : (B + 1) * ε ≤ (B - A) * c) (j : ℤ) :
    ((dyadicLaw (rawComponent μ i k) (i + m)) j).toReal ≤ B := by
  have hq : 0 < ((μ : Measure ℝ) (dyadicCell i k)).toReal :=
    ENNReal.toReal_pos (dyadicCell_measure_ne_zero μ i k) (measure_ne_top _ _)
  rw [dyadicLaw_apply, rawComponent_apply, ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [mul_comm, ← div_eq_mul_inv]
  exact ratio_le_of_mass_errors hq hA hAB hc (href j)
    (dyadicCell_inter_mass_error_of_interval_error μ ν hclose i k (i + m) j)
    (dyadicCell_mass_error_of_interval_error μ ν hclose i k) hε

end ExactOverlaps.Entropy
