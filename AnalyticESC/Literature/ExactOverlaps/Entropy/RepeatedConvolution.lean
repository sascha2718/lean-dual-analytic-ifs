module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.KaimanovichVershik

set_option maxSynthPendingDepth 3

/-!
# Entropy of repeated convolution

Starting from `p`, repeatedly add an independent sample with law `q`.
The entropy sequence has decreasing increments, and its total increase
is bounded by the number of steps times its first increase.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.RepeatedConvolution`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

namespace ExactOverlaps.Entropy

noncomputable def iteratedConvolution {G : Type*} [Add G] (p q : PMF G) : ℕ → PMF G
  | 0 => p
  | n + 1 => discreteConvolution (iteratedConvolution p q n) q

lemma iteratedConvolution_support_finite {G : Type*} [Add G]
    (p q : PMF G) (hp : p.support.Finite) (hq : q.support.Finite) (n : ℕ) :
    (iteratedConvolution p q n).support.Finite := by
  induction n with
  | zero => exact hp
  | succ n ih => exact discreteConvolution_support_finite _ _ ih hq

noncomputable def iteratedEntropy {G : Type*} [Add G]
    (p q : PMF G) (hp : p.support.Finite) (hq : q.support.Finite) (n : ℕ) : ℝ :=
  finiteEntropy (iteratedConvolution p q n) (iteratedConvolution_support_finite p q hp hq n)

/-- Repeated convolution gives a concave sequence of finite entropies. -/
theorem iteratedEntropy_second_difference_le {G : Type*} [AddCommGroup G]
    (p q : PMF G) (hp : p.support.Finite) (hq : q.support.Finite) (n : ℕ) :
    iteratedEntropy p q hp hq (n + 2) + iteratedEntropy p q hp hq n ≤
      iteratedEntropy p q hp hq (n + 1) + iteratedEntropy p q hp hq (n + 1) := by
  have h := finiteEntropy_convolution_increment_le q (iteratedConvolution p q n) q
    hq (iteratedConvolution_support_finite p q hp hq n) hq
  simpa only [discreteConvolution_comm q (iteratedConvolution p q n),
    iteratedEntropy, iteratedConvolution] using h

lemma sequence_le_affine_of_second_difference_nonpos (a : ℕ → ℝ)
    (h : ∀ n, a (n + 2) + a n ≤ a (n + 1) + a (n + 1)) (n : ℕ) :
    a n ≤ a 0 + (n : ℝ) * (a 1 - a 0) := by
  have hstep : ∀ k, a (k + 1) - a k ≤ a 1 - a 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk := h k
      have he : k + 1 + 1 = k + 2 := by omega
      change a (k + 1 + 1) - a (k + 1) ≤ _
      rw [he]
      linarith
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := hstep n
    push_cast
    linarith

/-- The correct telescoped Kaimanovich–Vershik bound, anchored at the initial law. -/
theorem iteratedEntropy_le_first_increment {G : Type*} [AddCommGroup G]
    (p q : PMF G) (hp : p.support.Finite) (hq : q.support.Finite) (n : ℕ) :
    iteratedEntropy p q hp hq n ≤ finiteEntropy p hp + (n : ℝ) *
      (finiteEntropy (discreteConvolution p q) (discreteConvolution_support_finite p q hp hq) -
        finiteEntropy p hp) :=
  sequence_le_affine_of_second_difference_nonpos (iteratedEntropy p q hp hq)
    (iteratedEntropy_second_difference_le p q hp hq) n

end ExactOverlaps.Entropy
