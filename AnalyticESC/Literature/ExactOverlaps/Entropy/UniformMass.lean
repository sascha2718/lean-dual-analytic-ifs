module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Dyadic

set_option maxSynthPendingDepth 3

/-!
# Entropy from uniform bounds on atom masses

An atom bound of C/N gives entropy at least log N minus log C. This applies
to the actual dyadic PMF and is the finite information input to density-based
local uniformity estimates.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.UniformMass`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

theorem neg_log_max_mass_le_finiteEntropy {α : Type*} (p : PMF α)
    (hp : p.support.Finite) {M : ℝ} (hM : 0 < M)
    (hbound : ∀ a ∈ p.support, (p a).toReal ≤ M) :
    -Real.log M ≤ finiteEntropy p hp := by
  calc
    _ = ∑ a ∈ hp.toFinset, (p a).toReal * (-Real.log M) := by
      rw [← Finset.sum_mul, sum_support_toReal, one_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a ha
      have ha' : a ∈ p.support := by simpa using ha
      have hpos := ENNReal.toReal_pos ha' (p.apply_ne_top a)
      have hl := (Real.log_le_log_iff hpos hM).2 (hbound a ha')
      have hmul := mul_le_mul_of_nonneg_left hl hpos.le
      unfold Real.negMulLog
      nlinarith

theorem log_card_sub_log_factor_le_finiteEntropy {α : Type*} (p : PMF α)
    (hp : p.support.Finite) {C N : ℝ} (hC : 0 < C) (hN : 0 < N)
    (hbound : ∀ a ∈ p.support, (p a).toReal ≤ C / N) :
    Real.log N - Real.log C ≤ finiteEntropy p hp := by
  have h := neg_log_max_mass_le_finiteEntropy p hp (div_pos hC hN) hbound
  rw [Real.log_div hC.ne' hN.ne'] at h
  linarith

theorem dyadicEntropy_ge_of_atom_bound (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (m : ℕ) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ k ∈ (dyadicLaw μ m).support,
      ((dyadicLaw μ m) k).toReal ≤ C / (2 : ℝ) ^ m) :
    (m : ℝ) * Real.log 2 - Real.log C ≤ dyadicEntropy μ hμ m := by
  have h := log_card_sub_log_factor_le_finiteEntropy
    (dyadicLaw μ m) (dyadicLaw_support_finite μ hμ m) hC
    (pow_pos (by norm_num) m) hbound
  simpa only [Real.log_pow, dyadicEntropy] using h

theorem normalizedDyadicEntropy_ge_of_atom_bound (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) {m : ℕ} (hm : 0 < m) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ k ∈ (dyadicLaw μ m).support,
      ((dyadicLaw μ m) k).toReal ≤ C / (2 : ℝ) ^ m) :
    1 - Real.log C / ((m : ℝ) * Real.log 2) ≤ normalizedDyadicEntropy μ hμ m := by
  have hden : 0 < (m : ℝ) * Real.log 2 :=
    mul_pos (Nat.cast_pos.mpr hm) (Real.log_pos (by norm_num))
  have h := div_le_div_of_nonneg_right (dyadicEntropy_ge_of_atom_bound μ hμ m hC hbound) hden.le
  simpa only [sub_div, div_self hden.ne', normalizedDyadicEntropy] using h

end ExactOverlaps.Entropy
