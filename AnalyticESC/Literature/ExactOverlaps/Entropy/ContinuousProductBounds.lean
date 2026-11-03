module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.ContinuousProductMoments

set_option maxSynthPendingDepth 3

/-!
# Interval bounds for centered independent coordinates

An actual mean lies in the support interval. Consequently centering a law
supported on an interval of length L gives summands bounded by L, regardless
of the location of the interval.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.ContinuousProductBounds`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

lemma realLawMean_mem_Icc (μ : ProbabilityMeasure ℝ) {a b : ℝ}
    (hab : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a b) : realLawMean μ ∈ Icc a b := by
  have hi : Integrable (id : ℝ → ℝ) (μ : Measure ℝ) :=
    (memLp_id_of_hasBoundedSupport μ ⟨a, b, hab⟩ 1).integrable (by norm_num)
  constructor
  · have h := integral_mono_ae (integrable_const a) hi (hab.mono fun _ hx ↦ hx.1)
    simpa [realLawMean] using h
  · have h := integral_mono_ae hi (integrable_const b) (hab.mono fun _ hx ↦ hx.2)
    simpa [realLawMean] using h

lemma abs_sub_realLawMean_le (μ : ProbabilityMeasure ℝ) {a b : ℝ}
    (hab : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a b) :
    ∀ᵐ x ∂(μ : Measure ℝ), |x - realLawMean μ| ≤ b - a := by
  have hm := realLawMean_mem_Icc μ hab
  filter_upwards [hab] with x hx
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hm.1, hm.2]

lemma ae_continuousProduct_coordinate_mem_Icc {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) (i : ι) {a b : ℝ}
    (hab : ∀ᵐ x ∂(ν i : Measure ℝ), x ∈ Icc a b) :
    ∀ᵐ w ∂(continuousProductLaw ν : Measure (ι → ℝ)), w i ∈ Icc a b := by
  have hmap : (continuousProductLaw ν : Measure (ι → ℝ)).map (fun w ↦ w i) =
      (ν i : Measure ℝ) :=
    (measurePreserving_eval (fun j ↦ (ν j : Measure ℝ)) i).map_eq
  rw [← hmap] at hab
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hab

lemma abs_centeredProductCoordinate_le {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) (i : ι) {a b : ℝ}
    (hab : ∀ᵐ x ∂(ν i : Measure ℝ), x ∈ Icc a b) :
    ∀ᵐ w ∂(continuousProductLaw ν : Measure (ι → ℝ)),
      |centeredProductCoordinate ν i w| ≤ b - a := by
  have hm := realLawMean_mem_Icc (ν i) hab
  filter_upwards [ae_continuousProduct_coordinate_mem_Icc ν i hab] with w hw
  change |w i - realLawMean (ν i)| ≤ b - a
  rw [abs_le]
  constructor <;> linarith [hw.1, hw.2, hm.1, hm.2]

end ExactOverlaps.Entropy
