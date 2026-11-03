module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.Moments
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

set_option maxSynthPendingDepth 3

/-!
# Actual moments and independence under normalization

Dividing every centered summand by the same positive number preserves
independence and scales second and third absolute moments by the expected
powers. These are equalities of actual integrals.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.NormalizationMoments`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ExactOverlaps.GaussianApproximation

lemma memLp_three_div_const {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : MemLp X 3 μ) (s : ℝ) :
    MemLp (fun ω ↦ X ω / s) 3 μ := by
  simpa only [div_eq_mul_inv, mul_comm] using hX.const_mul s⁻¹

lemma independent_div_const {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (X : ι → Ω → ℝ) (hind : iIndepFun X μ) (s : ℝ) :
    iIndepFun (fun i ω ↦ X i ω / s) μ :=
  hind.comp (fun _ x ↦ x / s) (fun _ ↦ measurable_id.div_const s)

lemma integral_div_const_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hmean : (∫ ω, X ω ∂μ) = 0) (s : ℝ) :
    (∫ ω, X ω / s ∂μ) = 0 := by
  rw [integral_div, hmean, zero_div]

lemma sum_secondMoment_div_eq_one {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} (X : ι → Ω → ℝ) {s : ℝ} (hs : s ≠ 0)
    (hv : (∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) = s ^ 2) :
    (∑ i, ∫ ω, (X i ω / s) ^ 2 ∂μ) = 1 := by
  simp only [div_pow, integral_div, ← Finset.sum_div, hv, div_self (pow_ne_zero 2 hs)]

lemma sum_thirdMoment_div {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} (X : ι → Ω → ℝ) {s : ℝ} (hs : 0 < s) :
    (∑ i, ∫ ω, |X i ω / s| ^ 3 ∂μ) =
      (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) / s ^ 3 := by
  simp only [abs_div, abs_of_pos hs, div_pow, integral_div, Finset.sum_div]

end ExactOverlaps.GaussianApproximation
