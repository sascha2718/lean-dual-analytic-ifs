module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic

set_option maxSynthPendingDepth 3

/-!
# Translating finite sets of levels

Clipping a translate back to the original range loses at most twice the
absolute shift. The estimate is uniform over every subset of the range and
retains the actual signed relation between each original and output level.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.ShiftedLevelSets`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

namespace ExactOverlaps.Entropy

theorem exists_shifted_level_set (I : Finset ℕ) {n : ℕ} (hI : I ⊆ Finset.range n) (s : ℤ) :
    ∃ J : Finset ℕ, J ⊆ Finset.range n ∧ I.card ≤ J.card + 2 * s.natAbs ∧
      ∀ j ∈ J, ∃ i ∈ I, (j : ℤ) = (i : ℤ) + s := by
  classical
  let L := s.natAbs
  let S := I.filter (fun i ↦ L ≤ i ∧ i + L < n)
  let J := S.image (fun i : ℕ ↦ ((i : ℤ) + s).toNat)
  have hhi : s ≤ (L : ℤ) := Int.le_natAbs
  have hlo : -(L : ℤ) ≤ s := by
    have hneg : -s ≤ ((-s).natAbs : ℤ) := Int.le_natAbs
    simp only [Int.natAbs_neg] at hneg
    dsimp only [L]
    omega
  have hs (i : ℕ) (hi : i ∈ S) : 0 ≤ (i : ℤ) + s ∧ (i : ℤ) + s < n := by
    have hh := (Finset.mem_filter.mp hi).2
    omega
  have hJ : J ⊆ Finset.range n := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hh := hs i hi
    simp only [Finset.mem_range]
    omega
  have hcard : J.card = S.card := by
    apply Finset.card_image_iff.mpr
    intro i hi j hj he
    change ((i : ℤ) + s).toNat = ((j : ℤ) + s).toNat at he
    have hi' := hs i hi
    have hj' := hs j hj
    omega
  have hsub : I \ S ⊆ Finset.range L ∪ Finset.Ico (n - L) n := by
    intro i hi
    obtain ⟨hiI, hiS⟩ := Finset.mem_sdiff.mp hi
    have hin : i < n := Finset.mem_range.mp (hI hiI)
    have hnot : ¬ (L ≤ i ∧ i + L < n) := by
      intro h
      exact hiS (Finset.mem_filter.mpr ⟨hiI, h⟩)
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    omega
  have hboundary : (I \ S).card ≤ 2 * L := by
    have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    simp only [Finset.card_range, Nat.card_Ico] at h
    omega
  have hScard : (I \ S).card + S.card = I.card := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun i ↦ L ≤ i ∧ i + L < n) I)
  refine ⟨J, hJ, ?_, ?_⟩
  · change I.card ≤ J.card + 2 * L
    omega
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    refine ⟨i, (Finset.mem_filter.mp hi).1, ?_⟩
    have hh := hs i hi
    omega

end ExactOverlaps.Entropy
