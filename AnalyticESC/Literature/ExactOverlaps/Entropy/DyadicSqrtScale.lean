module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.RealConvolutionVariance
public import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option maxSynthPendingDepth 3

/-!
# The integer dyadic normalization at the square-root scale

The natural logarithm to base four equals the integer part of log base two
of the square root. The squared dilation factor times n lies in [1,4),
so variance ranges are preserved with explicit universal constants.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.DyadicSqrtScale`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ExactOverlaps.Entropy

def dyadicSqrtScale (n : ℕ) : ℕ := Nat.log 4 n

lemma dyadicSqrtScale_eq_floor_log_sqrt (n : ℕ) :
    (dyadicSqrtScale n : ℤ) = ⌊Real.log (Real.sqrt n) / Real.log 2⌋ := by
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      _ = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = _ := Real.log_pow (2 : ℝ) 2
  have he : Real.log (Real.sqrt n) / Real.log 2 = Real.logb 4 n := by
    rw [Real.log_sqrt (Nat.cast_nonneg n), Real.logb, h4]
    ring
  rw [he]
  change (Nat.log 4 n : ℤ) = ⌊Real.logb (4 : ℕ) (n : ℝ)⌋
  rw [Real.floor_logb_natCast (Nat.cast_nonneg n), Int.log_natCast]

lemma dyadicSqrtScale_factor_sq (n : ℕ) :
    ((2 : ℝ) ^ (-(dyadicSqrtScale n : ℤ))) ^ 2 = 1 / (4 : ℝ) ^ dyadicSqrtScale n := by
  have hp : ((2 : ℝ) ^ dyadicSqrtScale n) ^ 2 = (4 : ℝ) ^ dyadicSqrtScale n := by
    rw [← pow_mul, Nat.mul_comm (dyadicSqrtScale n) 2, pow_mul]
    norm_num
  rw [zpow_neg, zpow_natCast, inv_pow, hp, one_div]

theorem dyadicSqrtScale_count_bounds {n : ℕ} (hn : 0 < n) :
    1 ≤ (n : ℝ) * ((2 : ℝ) ^ (-(dyadicSqrtScale n : ℤ))) ^ 2 ∧
      (n : ℝ) * ((2 : ℝ) ^ (-(dyadicSqrtScale n : ℤ))) ^ 2 < 4 := by
  have hlo : (4 : ℝ) ^ dyadicSqrtScale n ≤ (n : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 4 hn.ne'
  have hhi : (n : ℝ) < (4 : ℝ) ^ (dyadicSqrtScale n + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) n
  rw [pow_succ] at hhi
  rw [dyadicSqrtScale_factor_sq, mul_one_div]
  have hp : 0 < (4 : ℝ) ^ dyadicSqrtScale n := by positivity
  constructor
  · exact (one_le_div hp).2 hlo
  · exact (div_lt_iff₀ hp).2 (by nlinarith)

theorem dyadicSqrtScale_variance_bounds {n : ℕ} (hn : 0 < n) {σ V v : ℝ}
    (hσ : 0 ≤ σ) (hV : 0 ≤ V) (hlo : σ * n ≤ v) (hhi : v ≤ V * n) :
    σ ≤ ((2 : ℝ) ^ (-(dyadicSqrtScale n : ℤ))) ^ 2 * v ∧
      ((2 : ℝ) ^ (-(dyadicSqrtScale n : ℤ))) ^ 2 * v ≤ 4 * V := by
  let t : ℝ := ((2 : ℝ) ^ (-(dyadicSqrtScale n : ℤ))) ^ 2
  have ht : 0 ≤ t := sq_nonneg _
  have hb := dyadicSqrtScale_count_bounds hn
  have h₁ := mul_le_mul_of_nonneg_left hlo ht
  have h₂ := mul_le_mul_of_nonneg_left hhi ht
  have h₃ := mul_le_mul_of_nonneg_left hb.1 hσ
  have h₄ := mul_le_mul_of_nonneg_left hb.2.le hV
  change σ ≤ t * v ∧ t * v ≤ 4 * V
  change 1 ≤ (n : ℝ) * t ∧ (n : ℝ) * t < 4 at hb
  change σ * 1 ≤ σ * ((n : ℝ) * t) at h₃
  change V * ((n : ℝ) * t) ≤ V * 4 at h₄
  constructor <;> nlinarith

theorem exists_dyadicSqrtScale_factor_lt {η : ℝ} (hη : 0 < η) :
    ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ, K ≤ n → (2 : ℝ) ^ (-(dyadicSqrtScale n : ℤ)) < η := by
  obtain ⟨K, hK⟩ := exists_nat_gt (max 0 (4 / η ^ 2))
  have hKpos : (0 : ℝ) < K := (le_max_left _ _).trans_lt hK
  refine ⟨K, Nat.cast_pos.mp hKpos, ?_⟩
  intro n hn
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.cast_pos.mp hKpos) hn
  have hn' : (K : ℝ) ≤ n := by exact_mod_cast hn
  have hlarge : 4 < (n : ℝ) * η ^ 2 := by
    have hdiv : 4 / η ^ 2 < (n : ℝ) := ((le_max_right _ _).trans_lt hK).trans_le hn'
    exact (div_lt_iff₀ (sq_pos_of_pos hη)).1 hdiv
  have hbound := (dyadicSqrtScale_count_bounds hnpos).2
  by_contra h
  have hs : η ^ 2 ≤ ((2 : ℝ) ^ (-(dyadicSqrtScale n : ℤ))) ^ 2 :=
    (sq_le_sq₀ hη.le (by positivity)).2 (le_of_not_gt h)
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n)
  linarith

end ExactOverlaps.Entropy
