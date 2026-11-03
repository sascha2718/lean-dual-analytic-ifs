module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.InformationIntegral
public import Mathlib.Analysis.Real.Sqrt

set_option maxSynthPendingDepth 3

/-!
Quantitative truncation of finite information. The estimate
-p log p <= 2 sqrt p makes information tails small using only the number
of possible labels, without a lower bound on their positive masses.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.InformationTruncation`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace ExactOverlaps.Entropy

theorem negMulLog_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.negMulLog x ≤ 2 * Real.sqrt x := by
  have hh : Real.negMulLog (Real.sqrt x) ≤ 1 :=
    (Real.negMulLog_le_one_sub_self (Real.sqrt_nonneg x)).trans (by linarith [Real.sqrt_nonneg x])
  have h := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * Real.sqrt x by positivity)
  have he : (2 * Real.sqrt x) * Real.negMulLog (Real.sqrt x) = Real.negMulLog x := by
    rw [Real.negMulLog, Real.log_sqrt hx, Real.negMulLog]
    calc
      2 * Real.sqrt x * (-(Real.sqrt x) * (Real.log x / 2)) =
          -(Real.sqrt x ^ 2) * Real.log x := by ring
      _ = -x * Real.log x := by rw [Real.sq_sqrt hx]
  simpa only [he, mul_one] using h

theorem pointInformation_truncation_bound {α : Type*} (p : PMF α) (a : α)
    {T : ℝ} (hT : 0 ≤ T) :
    (p a).toReal * (pointInformation p a - min (pointInformation p a) T) ≤
      2 * Real.exp (-T / 2) := by
  by_cases hsmall : pointInformation p a ≤ T
  · rw [min_eq_left hsmall, sub_self, mul_zero]
    positivity
  · have hlarge : T < -Real.log (p a).toReal := lt_of_not_ge hsmall
    have hp0 : 0 < (p a).toReal := by
      apply lt_of_le_of_ne ENNReal.toReal_nonneg
      intro hz
      rw [← hz, Real.log_zero, neg_zero] at hlarge
      exact (not_lt_of_ge hT) hlarge
    have hpbound : (p a).toReal < Real.exp (-T) :=
      (Real.log_lt_iff_lt_exp hp0).mp (by linarith)
    have hsqrt : Real.sqrt (p a).toReal ≤ Real.exp (-T / 2) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨Real.exp_nonneg _, ?_⟩
      have he : Real.exp (-T / 2) ^ 2 = Real.exp (-T) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [he]
      exact hpbound.le
    rw [min_eq_right (le_of_not_ge hsmall)]
    calc
      (p a).toReal * (pointInformation p a - T) ≤ (p a).toReal * pointInformation p a :=
        mul_le_mul_of_nonneg_left (sub_le_self _ hT) ENNReal.toReal_nonneg
      _ = Real.negMulLog (p a).toReal := by simp only [pointInformation, Real.negMulLog, mul_neg, neg_mul]
      _ ≤ 2 * Real.sqrt (p a).toReal := negMulLog_le_two_sqrt ENNReal.toReal_nonneg
      _ ≤ 2 * Real.exp (-T / 2) := mul_le_mul_of_nonneg_left hsqrt (by norm_num)

noncomputable def truncatedFiniteEntropy {α : Type*} (p : PMF α)
    (hp : p.support.Finite) (T : ℝ) : ℝ :=
  ∑ a ∈ hp.toFinset, (p a).toReal * min (pointInformation p a) T

theorem finiteEntropy_sub_truncated_bounds {α : Type*} (p : PMF α)
    (hp : p.support.Finite) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ finiteEntropy p hp - truncatedFiniteEntropy p hp T ∧
      finiteEntropy p hp - truncatedFiniteEntropy p hp T ≤
        2 * hp.toFinset.card * Real.exp (-T / 2) := by
  have he : finiteEntropy p hp - truncatedFiniteEntropy p hp T =
      ∑ a ∈ hp.toFinset, (p a).toReal *
        (pointInformation p a - min (pointInformation p a) T) := by
    unfold finiteEntropy truncatedFiniteEntropy
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp only [pointInformation, Real.negMulLog]
    ring
  rw [he]
  constructor
  · exact Finset.sum_nonneg fun a _ ↦
      mul_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr (min_le_left _ _))
  · calc
      _ ≤ ∑ _a ∈ hp.toFinset, 2 * Real.exp (-T / 2) :=
        Finset.sum_le_sum fun a _ ↦ pointInformation_truncation_bound p a hT
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

theorem integrable_min_pointInformation {α : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (p : PMF α) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun a ↦ min (pointInformation p a) T) p.toMeasure := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable T
  apply ae_of_all
  intro a
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min (pointInformation_nonneg p a) hT)]
  exact min_le_right _ _

theorem integral_min_pointInformation {α : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (p : PMF α)
    (hp : p.support.Finite) {T : ℝ} (hT : 0 ≤ T) :
    ∫ a, min (pointInformation p a) T ∂p.toMeasure = truncatedFiniteEntropy p hp T := by
  rw [PMF.integral_eq_tsum p _ (integrable_min_pointInformation p hT)]
  rw [tsum_eq_sum (s := hp.toFinset) (fun a ha ↦ ?_)]
  · rfl
  · have hz : p a = 0 := by simpa using ha
    simp [hz]

theorem integral_min_dyadicInformation (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (i : ℤ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ x, min (dyadicInformation μ i x) T ∂(μ : Measure ℝ) =
      truncatedFiniteEntropy (dyadicLaw μ i) (dyadicLaw_support_finite μ hμ i) T := by
  rw [← integral_min_pointInformation _ _ hT, dyadicLaw_toMeasure,
    integral_map (measurable_dyadicQuantize i).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
  rfl

end ExactOverlaps.Entropy
