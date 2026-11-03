module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.ContinuousProductBounds

set_option maxSynthPendingDepth 3

/-!
# Mean and variance of genuine continuous sums

The finite sum law has bounded support, its mean and variance are the sums
of the marginal means and variances, and subtracting its mean gives exactly
the pushforward of the sum of the independent centered coordinates.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.ContinuousSumMoments`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

lemma continuousSumLaw_hasBoundedSupport {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) (hν : ∀ i, HasBoundedSupport (ν i)) :
    HasBoundedSupport (continuousSumLaw ν) := by
  choose a b hab using hν
  refine ⟨∑ i, a i, ∑ i, b i, ?_⟩
  change ∀ᵐ x ∂((continuousProductLaw ν : Measure (ι → ℝ)).map
    (fun w ↦ ∑ i, w i)), x ∈ Icc (∑ i, a i) (∑ i, b i)
  have hm : Measurable (fun w : ι → ℝ ↦ ∑ i, w i) := by fun_prop
  apply (ae_map_iff hm.aemeasurable measurableSet_Icc).mpr
  have hc := ae_all_iff.mpr (fun i ↦ ae_continuousProduct_coordinate_mem_Icc ν i (hab i))
  filter_upwards [hc] with w hw
  exact ⟨Finset.sum_le_sum (fun i _ ↦ (hw i).1),
    Finset.sum_le_sum (fun i _ ↦ (hw i).2)⟩

lemma realLawMean_continuousSumLaw {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) (hν : ∀ i, HasBoundedSupport (ν i)) :
    realLawMean (continuousSumLaw ν) = ∑ i, realLawMean (ν i) := by
  unfold realLawMean continuousSumLaw
  rw [ProbabilityMeasure.toMeasure_map, integral_map (f := fun x : ℝ ↦ x) (by fun_prop) measurable_id.aestronglyMeasurable]
  change (∫ w : ι → ℝ, ∑ i, w i ∂(continuousProductLaw ν : Measure (ι → ℝ))) = _
  rw [integral_finsetSum _ (fun i _ ↦
    (continuousProduct_coordinate_memLp ν hν 1 i).integrable (by norm_num))]
  exact Finset.sum_congr rfl (fun i _ ↦ integral_continuousProduct_coordinate ν i)

lemma variance_continuousSumLaw {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) (hν : ∀ i, HasBoundedSupport (ν i)) :
    variance (id : ℝ → ℝ) (continuousSumLaw ν : Measure ℝ) =
      ∑ i, variance (id : ℝ → ℝ) (ν i : Measure ℝ) := by
  rw [continuousSumLaw, ProbabilityMeasure.toMeasure_map,
    variance_map measurable_id.aemeasurable (by fun_prop)]
  change variance (fun w : ι → ℝ ↦ ∑ i, w i)
    (Measure.pi (fun i ↦ (ν i : Measure ℝ))) = _
  have h := (variance_sum_pi (X := fun _ ↦ (id : ℝ → ℝ))
      (fun i ↦ memLp_id_of_hasBoundedSupport (ν i) (hν i) 2))
  convert h using 1
  congr 1
  funext w
  simp only [Finset.sum_apply, id_eq]

lemma continuousSumLaw_map_center {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) :
    ((continuousSumLaw ν).map (fun x ↦ x - ∑ i, realLawMean (ν i)) : Measure ℝ) =
      (continuousProductLaw ν : Measure (ι → ℝ)).map
        (fun w ↦ ∑ i, centeredProductCoordinate ν i w) := by
  change ((continuousProductLaw ν : Measure (ι → ℝ)).map (fun w ↦ ∑ i, w i)).map
    (fun x ↦ x - ∑ i, realLawMean (ν i)) = _
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext w
  simp only [Function.comp_def, centeredProductCoordinate, Finset.sum_sub_distrib]

end ExactOverlaps.Entropy
