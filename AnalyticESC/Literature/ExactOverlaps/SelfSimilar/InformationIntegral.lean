module

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Dyadic
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option maxSynthPendingDepth 3

/-!
Information density for finite probability laws and bounded Borel measures.
Its integral is the actual Shannon entropy. Values at zero-mass labels are
set to zero by the total real logarithm and do not affect the integral.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.InformationIntegral`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace ExactOverlaps.Entropy

noncomputable def pointInformation {α : Type*} (p : PMF α) (a : α) : ℝ :=
  -Real.log (p a).toReal

theorem pointInformation_nonneg {α : Type*} (p : PMF α) (a : α) :
    0 ≤ pointInformation p a := by
  apply neg_nonneg.mpr
  apply Real.log_nonpos ENNReal.toReal_nonneg
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one a)

theorem pointInformation_eq_zero_of_not_mem_support {α : Type*} (p : PMF α)
    {a : α} (ha : a ∉ p.support) : pointInformation p a = 0 := by
  have hz : p a = 0 := by simpa using ha
  simp [pointInformation, hz]

theorem integrable_pointInformation {α : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (p : PMF α) (hp : p.support.Finite) :
    Integrable (pointInformation p) p.toMeasure := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
    (∑ a ∈ hp.toFinset, ‖pointInformation p a‖)
  apply ae_of_all
  intro a
  by_cases ha : a ∈ p.support
  · exact Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) (by simpa using ha)
  · rw [pointInformation_eq_zero_of_not_mem_support p ha, norm_zero]
    exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

theorem integral_pointInformation {α : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (p : PMF α) (hp : p.support.Finite) :
    ∫ a, pointInformation p a ∂p.toMeasure = finiteEntropy p hp := by
  rw [PMF.integral_eq_tsum p _ (integrable_pointInformation p hp)]
  rw [tsum_eq_sum (s := hp.toFinset) (fun a ha ↦ ?_)]
  · unfold finiteEntropy
    apply Finset.sum_congr rfl
    intro a _
    simp only [pointInformation, smul_eq_mul, Real.negMulLog, mul_neg, neg_mul]
  · have hz : p a = 0 := by simpa using ha
    simp [hz]

/-- Information in the dyadic cell containing x. -/
noncomputable def dyadicInformation (μ : ProbabilityMeasure ℝ) (i : ℤ) (x : ℝ) : ℝ :=
  pointInformation (dyadicLaw μ i) (dyadicQuantize i x)

theorem measurable_dyadicInformation (μ : ProbabilityMeasure ℝ) (i : ℤ) :
    Measurable (dyadicInformation μ i) :=
  (measurable_of_countable (pointInformation (dyadicLaw μ i))).comp (measurable_dyadicQuantize i)

theorem dyadicInformation_nonneg (μ : ProbabilityMeasure ℝ) (i : ℤ) (x : ℝ) :
    0 ≤ dyadicInformation μ i x := pointInformation_nonneg _ _

theorem integrable_dyadicInformation (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (i : ℤ) : Integrable (dyadicInformation μ i) (μ : Measure ℝ) := by
  have h := integrable_pointInformation (dyadicLaw μ i) (dyadicLaw_support_finite μ hμ i)
  rw [dyadicLaw_toMeasure] at h
  exact h.comp_measurable (measurable_dyadicQuantize i)

theorem integral_dyadicInformation (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (i : ℤ) : ∫ x, dyadicInformation μ i x ∂(μ : Measure ℝ) = dyadicEntropy μ hμ i := by
  rw [dyadicEntropy, ← integral_pointInformation]
  rw [dyadicLaw_toMeasure,
    integral_map (measurable_dyadicQuantize i).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
  rfl

theorem integral_normalized_dyadicInformation (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n : ℕ) :
    ∫ x, dyadicInformation μ n x / ((n : ℝ) * Real.log 2) ∂(μ : Measure ℝ) =
      normalizedDyadicEntropy μ hμ n := by
  rw [integral_div, integral_dyadicInformation, normalizedDyadicEntropy]

end ExactOverlaps.Entropy
