module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
Adapted from the LpSelfSimilar entropy library.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Finite

set_option maxSynthPendingDepth 3

@[expose] public section

/-!
Elementary bounds for finite Shannon entropy. The support is explicit, and
the upper bound uses its actual cardinality. These estimates apply to finite
digit laws and to shifted-grid quantizations without arithmetic assumptions.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.Bounds`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

lemma sum_support_toReal {α : Type*} (p : PMF α) (hp : p.support.Finite) :
    ∑ a ∈ hp.toFinset, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ ↦ p.apply_ne_top a)]
  have hs : ∑ a ∈ hp.toFinset, p a = 1 := by
    rw [← p.tsum_coe]
    exact (tsum_eq_sum (fun a ha ↦ by simpa using ha)).symm
  rw [hs, ENNReal.toReal_one]

lemma finiteEntropy_nonneg {α : Type*} (p : PMF α) (hp : p.support.Finite) :
    0 ≤ finiteEntropy p hp := by
  apply Finset.sum_nonneg
  intro a _
  exact Real.negMulLog_nonneg ENNReal.toReal_nonneg
    (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using p.coe_le_one a))

lemma negMulLog_le_log_bound {x N : ℝ} (hx : 0 < x) (hN : 0 < N) :
    Real.negMulLog x ≤ x * Real.log N + 1 / N - x := by
  have h := Real.log_le_sub_one_of_pos (div_pos zero_lt_one (mul_pos hN hx))
  rw [one_div, Real.log_inv, Real.log_mul hN.ne' hx.ne'] at h
  have hm := mul_le_mul_of_nonneg_left h hx.le
  have heq : x * (N * x)⁻¹ = 1 / N := by field_simp
  rw [mul_sub, heq] at hm
  unfold Real.negMulLog
  nlinarith

/-- Entropy is bounded by the logarithm of the number of possible atoms. -/
lemma finiteEntropy_le_log_card {α : Type*} (p : PMF α) (hp : p.support.Finite) :
    finiteEntropy p hp ≤ Real.log hp.toFinset.card := by
  have hN : (0 : ℝ) < hp.toFinset.card := by
    exact_mod_cast Finset.card_pos.mpr (by simp)
  calc
    finiteEntropy p hp ≤ ∑ a ∈ hp.toFinset,
        ((p a).toReal * Real.log hp.toFinset.card + 1 / hp.toFinset.card - (p a).toReal) := by
      apply Finset.sum_le_sum
      intro a ha
      have hpa : p a ≠ 0 := by simpa using ha
      exact negMulLog_le_log_bound (ENNReal.toReal_pos hpa (p.apply_ne_top a)) hN
    _ = Real.log hp.toFinset.card := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
        sum_support_toReal]
      simp only [Finset.sum_const, nsmul_eq_mul, one_mul]
      field_simp; ring

end ExactOverlaps.Entropy
