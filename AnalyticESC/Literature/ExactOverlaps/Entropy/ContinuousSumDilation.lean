module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.ContinuousSumMoments

set_option maxSynthPendingDepth 3

/-!
# Common dilation of a continuous convolution

Dilation commutes with the actual finite sum law. Support intervals and
marginal variances transform with their exact scalar factors.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.ContinuousSumDilation`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

lemma continuousSumLaw_map_mul {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) (c : ℝ) :
    continuousSumLaw (fun i ↦ (ν i).map (fun x ↦ c * x)) =
      (continuousSumLaw ν).map (fun x ↦ c * x) := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_continuousSumLaw, ProbabilityMeasure.toMeasure_map,
    charFun_map_mul, charFun_continuousSumLaw]
  apply Finset.prod_congr rfl
  intro i _
  rw [ProbabilityMeasure.toMeasure_map, charFun_map_mul]

lemma ae_map_mul_mem_Icc (μ : ProbabilityMeasure ℝ) {a b c : ℝ} (hc : 0 ≤ c)
    (hab : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a b) :
    ∀ᵐ x ∂(μ.map (fun x ↦ c * x) : Measure ℝ), x ∈ Icc (c * a) (c * b) := by
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff (by fun_prop) measurableSet_Icc).mpr
  filter_upwards [hab] with x hx
  exact ⟨mul_le_mul_of_nonneg_left hx.1 hc, mul_le_mul_of_nonneg_left hx.2 hc⟩

lemma variance_map_mul (μ : ProbabilityMeasure ℝ) (c : ℝ) :
    variance (id : ℝ → ℝ) (μ.map (fun x ↦ c * x) : Measure ℝ) =
      c ^ 2 * variance (id : ℝ → ℝ) (μ : Measure ℝ) := by
  rw [ProbabilityMeasure.toMeasure_map, variance_map measurable_id.aemeasurable (by fun_prop)]
  change variance (fun x : ℝ ↦ c * x) (μ : Measure ℝ) = _
  exact variance_const_mul c (id : ℝ → ℝ) (μ : Measure ℝ)

lemma map_componentRescale_zero (μ : ProbabilityMeasure ℝ) (s : ℤ) :
    μ.map (componentRescale s 0) = μ.map (fun x ↦ (2 : ℝ) ^ s * x) := by
  congr 1
  funext x
  simp [componentRescale]

end ExactOverlaps.Entropy
