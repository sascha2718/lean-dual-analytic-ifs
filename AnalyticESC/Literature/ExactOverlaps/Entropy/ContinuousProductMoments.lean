module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.ContinuousProductLaw

set_option maxSynthPendingDepth 3

/-!
# Centered coordinates of a continuous product law

Coordinate moments are transferred from the genuine marginal laws. Centering
preserves independence and gives actual zero expectations, providing the
random-variable interface for non-identical-summand Gaussian approximation.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.ContinuousProductMoments`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

noncomputable def realLawMean (μ : ProbabilityMeasure ℝ) : ℝ :=
  ∫ x : ℝ, x ∂(μ : Measure ℝ)

lemma continuousProduct_coordinate_memLp {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) (hν : ∀ i, HasBoundedSupport (ν i)) (p : ℝ≥0∞) (i : ι) :
    MemLp (fun w : ι → ℝ ↦ w i) p (continuousProductLaw ν : Measure (ι → ℝ)) := by
  exact (memLp_id_of_hasBoundedSupport (ν i) (hν i) p).comp_measurePreserving
    (measurePreserving_eval (fun j ↦ (ν j : Measure ℝ)) i)

lemma integral_continuousProduct_coordinate {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) (i : ι) :
    (∫ w : ι → ℝ, w i ∂(continuousProductLaw ν : Measure (ι → ℝ))) = realLawMean (ν i) := by
  have h := integral_map (μ := (continuousProductLaw ν : Measure (ι → ℝ)))
    (measurable_pi_apply i).aemeasurable (measurable_id.aestronglyMeasurable)
  change (∫ x : ℝ, x ∂((continuousProductLaw ν : Measure (ι → ℝ)).map (fun w ↦ w i))) =
    (∫ w : ι → ℝ, w i ∂(continuousProductLaw ν : Measure (ι → ℝ))) at h
  have hmap : (continuousProductLaw ν : Measure (ι → ℝ)).map (fun w ↦ w i) =
      (ν i : Measure ℝ) :=
    (measurePreserving_eval (fun j ↦ (ν j : Measure ℝ)) i).map_eq
  rw [hmap] at h
  exact h.symm

noncomputable def centeredProductCoordinate {ι : Type*}
    (ν : ι → ProbabilityMeasure ℝ) (i : ι) (w : ι → ℝ) : ℝ := w i - realLawMean (ν i)

lemma centeredProductCoordinate_memLp {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) (hν : ∀ i, HasBoundedSupport (ν i)) (p : ℝ≥0∞) (i : ι) :
    MemLp (centeredProductCoordinate ν i) p (continuousProductLaw ν : Measure (ι → ℝ)) := by
  exact (continuousProduct_coordinate_memLp ν hν p i).sub (memLp_const (realLawMean (ν i)))

lemma centeredProductCoordinate_independent {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) :
    iIndepFun (centeredProductCoordinate ν) (continuousProductLaw ν : Measure (ι → ℝ)) := by
  exact (continuousProductLaw_independent ν).comp
    (fun i x ↦ x - realLawMean (ν i)) (fun _ ↦ measurable_id.sub_const _)

lemma integral_centeredProductCoordinate {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) (hν : ∀ i, HasBoundedSupport (ν i)) (i : ι) :
    (∫ w, centeredProductCoordinate ν i w ∂(continuousProductLaw ν : Measure (ι → ℝ))) = 0 := by
  unfold centeredProductCoordinate
  rw [integral_sub ((continuousProduct_coordinate_memLp ν hν 1 i).integrable (by norm_num))
    (integrable_const _), integral_continuousProduct_coordinate]
  simp

lemma integral_sq_centeredProductCoordinate {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) (i : ι) :
    (∫ w, (centeredProductCoordinate ν i w) ^ 2 ∂(continuousProductLaw ν : Measure (ι → ℝ))) =
      variance (id : ℝ → ℝ) (ν i : Measure ℝ) := by
  have h := integral_map (μ := (continuousProductLaw ν : Measure (ι → ℝ)))
    (measurable_pi_apply i).aemeasurable
    ((measurable_id.sub_const (realLawMean (ν i))).pow_const 2).aestronglyMeasurable
  have hmap : (continuousProductLaw ν : Measure (ι → ℝ)).map (fun w ↦ w i) =
      (ν i : Measure ℝ) :=
    (measurePreserving_eval (fun j ↦ (ν j : Measure ℝ)) i).map_eq
  rw [hmap] at h
  rw [variance_eq_integral measurable_id.aemeasurable]
  exact h.symm

end ExactOverlaps.Entropy
