module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.VarianceConcentration

set_option maxSynthPendingDepth 3

/-!
# Central dyadic cells

Every cell with label between the endpoint labels of a centered interval
lies within one additional cell width of that interval.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.CentralCells`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open Set

namespace ExactOverlaps.Entropy

lemma dyadicCell_left_endpoint_mem (i k : ℤ) :
    (k : ℝ) / (2 : ℝ) ^ i ∈ dyadicCell i k := by
  rw [dyadicCell_eq_Ico, mem_Ico]
  refine ⟨le_rfl, ?_⟩
  exact (div_lt_div_iff_of_pos_right (dyadic_scale_pos i)).2 (by linarith)

lemma abs_sub_center_le_of_label_bounds (b R : ℝ) (i k : ℤ)
    (hk : k ∈ Icc (dyadicQuantize i (b - R)) (dyadicQuantize i (b + R)))
    {x : ℝ} (hx : x ∈ dyadicCell i k) :
    |x - b| ≤ R + (2 : ℝ) ^ (-i) := by
  have hs := dyadic_scale_pos i
  have hleft := Int.lt_floor_add_one ((2 : ℝ) ^ i * (b - R))
  have hright := Int.floor_le ((2 : ℝ) ^ i * (b + R))
  have hkl : (dyadicQuantize i (b - R) : ℝ) ≤ k := by exact_mod_cast hk.1
  have hku : (k : ℝ) ≤ dyadicQuantize i (b + R) := by exact_mod_cast hk.2
  have hx' := (mem_dyadicCell_iff i k x).1 hx
  change (2 : ℝ) ^ i * (b - R) < (dyadicQuantize i (b - R) : ℝ) + 1 at hleft
  change (dyadicQuantize i (b + R) : ℝ) ≤ (2 : ℝ) ^ i * (b + R) at hright
  have hw : (2 : ℝ) ^ i * (2 : ℝ) ^ (-i) = 1 := by
    rw [zpow_neg, mul_inv_cancel₀ hs.ne']
  apply abs_le.mpr
  constructor
  · apply (mul_le_mul_iff_right₀ hs).mp
    nlinarith [hx'.1]
  · apply (mul_le_mul_iff_right₀ hs).mp
    nlinarith [hx'.2]

lemma abs_sub_center_le_add_one_of_label_bounds (b R : ℝ) (i : ℕ) (k : ℤ)
    (hk : k ∈ Icc (dyadicQuantize i (b - R)) (dyadicQuantize i (b + R)))
    {x : ℝ} (hx : x ∈ dyadicCell i k) : |x - b| ≤ R + 1 := by
  have hw : (2 : ℝ) ^ (-(i : ℤ)) ≤ 1 := by
    rw [zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  exact (abs_sub_center_le_of_label_bounds b R i k hk hx).trans (add_le_add le_rfl hw)

end ExactOverlaps.Entropy
