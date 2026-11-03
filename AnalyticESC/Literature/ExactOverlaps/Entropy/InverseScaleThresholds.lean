module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

set_option maxSynthPendingDepth 3

/-!
# Uniform finite-scale thresholds

Elementary Archimedean choices used to make the explicit entropy errors
uniformly small after the mathematical parameters have been fixed.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.InverseScaleThresholds`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

namespace ExactOverlaps.Entropy

lemma exists_nat_div_le (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → C / n ≤ ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 0 (C / ε))
  have hNpos : (0 : ℝ) < N := (le_max_left _ _).trans_lt hN
  refine ⟨N, Nat.cast_pos.mp hNpos, ?_⟩
  intro n hn
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := hNpos.trans_le hn'
  have hlarge : C / ε < (n : ℝ) := ((le_max_right _ _).trans_lt hN).trans_le hn'
  apply (div_le_iff₀ hnpos).2
  have h := (div_lt_iff₀ hε).1 hlarge
  nlinarith

lemma exists_inverse_block_depth {a e : ℝ} (ha : 0 < a) (he : 0 < e) :
    ∃ M : ℕ, 0 < M ∧ ∀ m : ℕ, M ≤ m →
      16 ≤ (m : ℝ) * e ∧ 128 ≤ (m : ℝ) * a * e := by
  obtain ⟨M, hM⟩ := exists_nat_gt (max 0 (max (16 / e) (128 / (a * e))))
  have hMpos : (0 : ℝ) < M := (le_max_left _ _).trans_lt hM
  refine ⟨M, Nat.cast_pos.mp hMpos, ?_⟩
  intro m hm
  have hm' : (M : ℝ) ≤ m := by exact_mod_cast hm
  have hbig : max (16 / e) (128 / (a * e)) < (m : ℝ) :=
    ((le_max_right _ _).trans_lt hM).trans_le hm'
  have h₁ := (div_lt_iff₀ he).1 ((le_max_left _ _).trans_lt hbig)
  have h₂ := (div_lt_iff₀ (mul_pos ha he)).1 ((le_max_right _ _).trans_lt hbig)
  constructor <;> nlinarith

end ExactOverlaps.Entropy
