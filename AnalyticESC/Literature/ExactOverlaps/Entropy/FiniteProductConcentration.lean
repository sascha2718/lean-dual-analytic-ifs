module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.FiniteProductMoments

set_option maxSynthPendingDepth 3

/-!
# Chebyshev concentration for actual finite iid products

The exceptional probability is the actual weighted mass of the indicated
event in the constructed product law. The bound is uniform over bounded
observables and does not assume a law of large numbers.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.FiniteProductConcentration`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open scoped ENNReal BigOperators
open ExactOverlaps.FiniteProbability

namespace ExactOverlaps.Entropy

noncomputable def finiteDeviationMass {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → ℝ) (c r : ℝ) : ℝ := by
  classical
  exact ∑ a ∈ hp.toFinset, if r ≤ |f a - c| then (p a).toReal else 0

lemma finiteDeviationMass_eq_event_probability {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → ℝ) (c r : ℝ) :
    finiteDeviationMass p hp f c r =
      ((p.map (fun a ↦ decide (r ≤ |f a - c|))) true).toReal := by
  classical
  rw [marginal_toReal_eq_finite_sum p hp]
  simp only [finiteDeviationMass, decide_eq_true_eq]

lemma finiteDeviationMass_nonneg {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → ℝ) (c r : ℝ) : 0 ≤ finiteDeviationMass p hp f c r := by
  unfold finiteDeviationMass
  apply Finset.sum_nonneg
  intro a _
  split_ifs <;> positivity

lemma finiteDeviationMass_le_variance {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → ℝ) {r : ℝ} (hr : 0 < r) :
    finiteDeviationMass p hp f (expectation p hp f) r ≤
      FiniteProbability.variance p hp f / r ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  unfold finiteDeviationMass FiniteProbability.variance expectation
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  split_ifs with ha
  · have hs : r ^ 2 ≤ (f a - ∑ a ∈ hp.toFinset, (p a).toReal * f a) ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ hr.le (abs_nonneg _)).2 ha
    exact mul_le_mul_of_nonneg_left hs ENNReal.toReal_nonneg
  · simp only [zero_mul]
    positivity

theorem iidTupleSum_deviation_le {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → ℝ) {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    finiteDeviationMass (iidTupleLaw p n) (iidTupleLaw_support_finite p hp n)
      (tupleSum f n) ((n : ℝ) * expectation p hp f) ((n : ℝ) * ε) ≤
        FiniteProbability.variance p hp f / ((n : ℝ) * ε ^ 2) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h := finiteDeviationMass_le_variance (iidTupleLaw p n)
    (iidTupleLaw_support_finite p hp n) (tupleSum f n) (mul_pos hn' hε)
  rw [expectation_iidTupleSum p hp f n, variance_iidTupleSum p hp f n] at h
  have he : ((n : ℝ) * FiniteProbability.variance p hp f) / ((n : ℝ) * ε) ^ 2 =
      FiniteProbability.variance p hp f / ((n : ℝ) * ε ^ 2) := by
    field_simp
  rwa [he] at h

lemma finiteVariance_le_one_of_unit_bounds {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → ℝ) (hf : ∀ a ∈ p.support, 0 ≤ f a ∧ f a ≤ 1) :
    FiniteProbability.variance p hp f ≤ 1 := by
  have he : expectation p hp (fun a ↦ f a ^ 2) ≤ 1 := by
    rw [← expectation_const p hp 1]
    apply expectation_mono p hp
    intro a ha
    have h := hf a ha
    nlinarith
  rw [variance_eq_secondMoment_sub]
  linarith [sq_nonneg (expectation p hp f)]

theorem iidTupleSum_deviation_le_of_unit_bounds {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → ℝ)
    (hf : ∀ a ∈ p.support, 0 ≤ f a ∧ f a ≤ 1)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    finiteDeviationMass (iidTupleLaw p n) (iidTupleLaw_support_finite p hp n)
      (tupleSum f n) ((n : ℝ) * expectation p hp f) ((n : ℝ) * ε) ≤
        1 / ((n : ℝ) * ε ^ 2) :=
  (iidTupleSum_deviation_le p hp f hn hε).trans
    (div_le_div_of_nonneg_right (finiteVariance_le_one_of_unit_bounds p hp f hf) (by positivity))

end ExactOverlaps.Entropy
