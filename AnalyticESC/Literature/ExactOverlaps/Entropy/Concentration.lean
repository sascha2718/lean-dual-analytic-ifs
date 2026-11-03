module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Dyadic

set_option maxSynthPendingDepth 3

/-!
# Small entropy gives a large atom

The collision deficit is bounded by Shannon entropy in natural units.
Consequently some atom has mass at least one minus the entropy.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.Concentration`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace ExactOverlaps.Entropy

lemma mul_one_sub_le_negMulLog {x : ℝ} (hx : 0 < x) :
    x * (1 - x) ≤ Real.negMulLog x := by
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hx) hx.le
  unfold Real.negMulLog
  nlinarith

theorem one_sub_collision_le_finiteEntropy {α : Type*} (p : PMF α)
    (hp : p.support.Finite) :
    1 - ∑ a ∈ hp.toFinset, (p a).toReal ^ 2 ≤ finiteEntropy p hp := by
  calc
    _ = ∑ a ∈ hp.toFinset, (p a).toReal * (1 - (p a).toReal) := by
      simp_rw [mul_sub, mul_one, ← pow_two]
      rw [Finset.sum_sub_distrib, sum_support_toReal]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a ha
      have ha' : p a ≠ 0 := by simpa using ha
      exact mul_one_sub_le_negMulLog (ENNReal.toReal_pos ha' (p.apply_ne_top a))

theorem exists_atom_one_sub_entropy_le {α : Type*} (p : PMF α)
    (hp : p.support.Finite) :
    ∃ a ∈ p.support, 1 - finiteEntropy p hp ≤ (p a).toReal := by
  obtain ⟨a, ha, hmax⟩ := hp.toFinset.exists_max_image (fun a ↦ (p a).toReal) (by simp)
  have hsq : (∑ b ∈ hp.toFinset, (p b).toReal ^ 2) ≤ (p a).toReal := by
    calc
      _ ≤ ∑ b ∈ hp.toFinset, (p b).toReal * (p a).toReal := by
        apply Finset.sum_le_sum
        intro b hb
        simpa only [pow_two] using
          mul_le_mul_of_nonneg_left (hmax b hb) ENNReal.toReal_nonneg
      _ = _ := by rw [← Finset.sum_mul, sum_support_toReal, one_mul]
  refine ⟨a, by simpa using ha, ?_⟩
  linarith [one_sub_collision_le_finiteEntropy p hp]

theorem exists_dyadicCell_one_sub_entropy_le (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) :
    ∃ k ∈ (dyadicLaw μ i).support,
      1 - dyadicEntropy μ hμ i ≤ ((μ : Measure ℝ) (dyadicCell i k)).toReal := by
  obtain ⟨k, hk, h⟩ := exists_atom_one_sub_entropy_le
    (dyadicLaw μ i) (dyadicLaw_support_finite μ hμ i)
  exact ⟨k, hk, by simpa only [dyadicEntropy, dyadicLaw_apply] using h⟩

end ExactOverlaps.Entropy
