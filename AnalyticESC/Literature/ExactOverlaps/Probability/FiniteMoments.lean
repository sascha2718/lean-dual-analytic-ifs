module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
Adapted from the LpSelfSimilar probability library.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Bounds
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Probability.Moments.Variance

set_option maxSynthPendingDepth 3

@[expose] public section

/-!
Moments of finitely supported probability laws. Finite weighted formulas are
identified with the actual Bochner expectation and Mathlib variance. The
pairwise squared-distance identity is the bridge from grid disagreement to
conditional variance.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Probability.FiniteMoments`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ExactOverlaps.FiniteProbability

/-- Finite weighted expectation. -/
noncomputable def expectation {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → ℝ) : ℝ := ∑ a ∈ hp.toFinset, (p a).toReal * f a

/-- Finite weighted central second moment. -/
noncomputable def variance {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → ℝ) : ℝ := expectation p hp (fun a ↦ (f a - expectation p hp f) ^ 2)

lemma expectation_const {α : Type*} (p : PMF α) (hp : p.support.Finite) (c : ℝ) :
    expectation p hp (fun _ ↦ c) = c := by
  rw [expectation, ← Finset.sum_mul, Entropy.sum_support_toReal, one_mul]

lemma expectation_add {α : Type*} (p : PMF α) (hp : p.support.Finite) (f g : α → ℝ) :
    expectation p hp (fun a ↦ f a + g a) = expectation p hp f + expectation p hp g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

lemma expectation_sub {α : Type*} (p : PMF α) (hp : p.support.Finite) (f g : α → ℝ) :
    expectation p hp (fun a ↦ f a - g a) = expectation p hp f - expectation p hp g := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

lemma expectation_const_mul {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (c : ℝ) (f : α → ℝ) : expectation p hp (fun a ↦ c * f a) = c * expectation p hp f := by
  simp [expectation, Finset.mul_sum, mul_left_comm]

lemma expectation_mono {α : Type*} (p : PMF α) (hp : p.support.Finite)
    {f g : α → ℝ} (hfg : ∀ a ∈ p.support, f a ≤ g a) :
    expectation p hp f ≤ expectation p hp g := by
  apply Finset.sum_le_sum
  intro a ha
  exact mul_le_mul_of_nonneg_left (hfg a (by simpa using ha)) ENNReal.toReal_nonneg

lemma expectation_nonneg {α : Type*} (p : PMF α) (hp : p.support.Finite)
    {f : α → ℝ} (hf : ∀ a ∈ p.support, 0 ≤ f a) : 0 ≤ expectation p hp f := by
  rw [← expectation_const p hp 0]
  exact expectation_mono p hp hf

lemma variance_nonneg {α : Type*} (p : PMF α) (hp : p.support.Finite) (f : α → ℝ) :
    0 ≤ variance p hp f := expectation_nonneg p hp (fun _ _ ↦ sq_nonneg _)

lemma variance_eq_secondMoment_sub {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → ℝ) : variance p hp f = expectation p hp (fun a ↦ f a ^ 2) - expectation p hp f ^ 2 := by
  have he (a : α) : (f a - expectation p hp f) ^ 2 =
      f a ^ 2 - (2 * expectation p hp f) * f a + expectation p hp f ^ 2 := by ring
  unfold variance
  simp_rw [he]
  rw [expectation_add, expectation_sub, expectation_const_mul, expectation_const]
  ring

lemma expectation_sq_sub {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → ℝ) (c : ℝ) :
    expectation p hp (fun a ↦ (c - f a) ^ 2) =
      c ^ 2 - 2 * c * expectation p hp f + expectation p hp (fun a ↦ f a ^ 2) := by
  have he (a : α) : (c - f a) ^ 2 = c ^ 2 - (2 * c) * f a + f a ^ 2 := by ring
  simp_rw [he]
  rw [expectation_add, expectation_sub, expectation_const_mul, expectation_const]

lemma pairwise_sq_distance_eq_two_variance {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → ℝ) :
    expectation p hp (fun a ↦ expectation p hp (fun b ↦ (f a - f b) ^ 2)) =
      2 * variance p hp f := by
  simp_rw [expectation_sq_sub]
  have he (a : α) : 2 * f a * expectation p hp f = (2 * expectation p hp f) * f a := by ring
  simp_rw [he]
  rw [expectation_add, expectation_sub, expectation_const_mul, expectation_const,
    variance_eq_secondMoment_sub]
  ring

lemma integrable_of_finite_support {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (hp : p.support.Finite) (f : α → ℝ) : Integrable f p.toMeasure := by
  have h : IntegrableOn f p.support p.toMeasure := IntegrableOn.of_finite hp
  rwa [IntegrableOn, PMF.restrict_toMeasure_support] at h

lemma expectation_eq_integral {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (hp : p.support.Finite) (f : α → ℝ) :
    expectation p hp f = ∫ a, f a ∂p.toMeasure := by
  rw [PMF.integral_eq_tsum p f (integrable_of_finite_support p hp f)]
  symm
  apply tsum_eq_sum
  intro a ha
  have hz : p a = 0 := by simpa using ha
  simp [hz]

lemma variance_eq_measure_variance {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (hp : p.support.Finite) (f : α → ℝ) :
    variance p hp f = ProbabilityTheory.variance f p.toMeasure := by
  rw [ProbabilityTheory.variance_eq_integral (integrable_of_finite_support p hp f).aemeasurable]
  unfold variance
  rw [expectation_eq_integral p hp f, expectation_eq_integral]

lemma expectation_sq_le_expectation_sq {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → ℝ) : expectation p hp f ^ 2 ≤ expectation p hp (fun a ↦ f a ^ 2) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul hp.toFinset
    (r := fun a ↦ (p a).toReal * f a) (f := fun a ↦ (p a).toReal)
    (g := fun a ↦ (p a).toReal * f a ^ 2)
    (fun _ _ ↦ ENNReal.toReal_nonneg) (fun _ _ ↦ by positivity)
    (fun a _ ↦ by ring_nf; exact le_rfl)
  rw [Entropy.sum_support_toReal, one_mul] at h
  exact h

lemma pairwise_abs_distance_le_sqrt_two_variance {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → ℝ) :
    expectation p hp (fun a ↦ expectation p hp (fun b ↦ |f a - f b|)) ≤
      Real.sqrt (2 * variance p hp f) := by
  have hi (a : α) : expectation p hp (fun b ↦ |f a - f b|) ^ 2 ≤
      expectation p hp (fun b ↦ (f a - f b) ^ 2) := by
    simpa only [sq_abs] using expectation_sq_le_expectation_sq p hp (fun b ↦ |f a - f b|)
  have h := (expectation_sq_le_expectation_sq p hp
    (fun a ↦ expectation p hp (fun b ↦ |f a - f b|))).trans
      (expectation_mono p hp (fun a _ ↦ hi a))
  rw [pairwise_sq_distance_eq_two_variance] at h
  have hv := variance_nonneg p hp f
  have hs := Real.sq_sqrt (show 0 ≤ 2 * variance p hp f by positivity)
  nlinarith [Real.sqrt_nonneg (2 * variance p hp f)]

end ExactOverlaps.FiniteProbability
