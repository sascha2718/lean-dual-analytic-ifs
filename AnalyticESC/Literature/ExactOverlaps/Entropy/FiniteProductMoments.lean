module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.FiniteProductLaw
public import AnalyticESC.Literature.ExactOverlaps.Probability.IndependentExpectations

set_option maxSynthPendingDepth 3

/-!
# Exact moments of finite independent sums

All expectations and variances refer to the constructed product PMFs.
The iid sum has mean n times the one-coordinate mean and variance n times
the one-coordinate variance, with no assumptions beyond finite support.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.FiniteProductMoments`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open scoped ENNReal
open ExactOverlaps.FiniteProbability

namespace ExactOverlaps.Entropy

lemma expectation_independentPair_add {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (f : α → ℝ) (g : β → ℝ) :
    expectation (independentPair p q) (independentPair_support_finite p q hp hq)
      (fun z ↦ f z.1 + g z.2) = expectation p hp f + expectation q hq g := by
  rw [expectation_independentPair]
  change expectation p hp (fun a ↦ expectation q hq (fun b ↦ f a + g b)) = _
  simp_rw [expectation_add, expectation_const]

lemma variance_independentPair_add {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (f : α → ℝ) (g : β → ℝ) :
    FiniteProbability.variance (independentPair p q) (independentPair_support_finite p q hp hq)
      (fun z ↦ f z.1 + g z.2) =
        FiniteProbability.variance p hp f + FiniteProbability.variance q hq g := by
  rw [variance_eq_secondMoment_sub, expectation_independentPair_add,
    variance_eq_secondMoment_sub p hp, variance_eq_secondMoment_sub q hq,
    expectation_independentPair]
  change expectation p hp (fun a ↦ expectation q hq (fun b ↦ (f a + g b) ^ 2)) -
    (expectation p hp f + expectation q hq g) ^ 2 = _
  have hsq (a : α) (b : β) : (f a + g b) ^ 2 =
      f a ^ 2 + (2 * f a) * g b + g b ^ 2 := by ring
  simp_rw [hsq, expectation_add, expectation_const, expectation_const_mul,
    expectation_mul_const]
  ring_nf
  rw [expectation_mul_const]
  ring

theorem expectation_iidTupleSum {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → ℝ) (n : ℕ) :
    expectation (iidTupleLaw p n) (iidTupleLaw_support_finite p hp n) (tupleSum f n) =
      (n : ℝ) * expectation p hp f := by
  induction n with
  | zero => simp only [tupleSum, expectation_const, Nat.cast_zero, zero_mul]
  | succ n ih =>
    change expectation (independentPair p (iidTupleLaw p n)) _
      (fun z ↦ f z.1 + tupleSum f n z.2) = _
    rw [expectation_independentPair_add p (iidTupleLaw p n) hp
      (iidTupleLaw_support_finite p hp n), ih, Nat.cast_add, Nat.cast_one]
    ring

theorem variance_iidTupleSum {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → ℝ) (n : ℕ) :
    FiniteProbability.variance (iidTupleLaw p n) (iidTupleLaw_support_finite p hp n) (tupleSum f n) =
      (n : ℝ) * FiniteProbability.variance p hp f := by
  induction n with
  | zero => simp only [tupleSum, FiniteProbability.variance, expectation_const, sub_self,
      zero_pow (by decide : 2 ≠ 0), Nat.cast_zero, zero_mul]
  | succ n ih =>
    change FiniteProbability.variance (independentPair p (iidTupleLaw p n)) _
      (fun z ↦ f z.1 + tupleSum f n z.2) = _
    rw [variance_independentPair_add p (iidTupleLaw p n) hp
      (iidTupleLaw_support_finite p hp n), ih, Nat.cast_add, Nat.cast_one]
    ring

end ExactOverlaps.Entropy
