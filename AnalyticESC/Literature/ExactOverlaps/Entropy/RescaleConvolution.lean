module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Components
public import AnalyticESC.Literature.ExactOverlaps.Entropy.RealConvolution

set_option maxSynthPendingDepth 3

/-!
# Affine normalization of a pair of dyadic components

Rescaling both inputs rescales their sum with the sum of the two cell labels.
At dyadic fine levels this is an exact bijective relabeling, with no entropy error.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.RescaleConvolution`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set

namespace ExactOverlaps.Entropy

lemma componentRescale_hasBoundedSupport (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i k : ℤ) : HasBoundedSupport (μ.map (componentRescale i k)) := by
  obtain ⟨a, b, hab⟩ := hμ
  refine ⟨componentRescale i k a, componentRescale i k b, ?_⟩
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff (measurable_componentRescale i k).aemeasurable
    (p := fun x : ℝ ↦ x ∈ Icc (componentRescale i k a) (componentRescale i k b))
    measurableSet_Icc).mpr
  filter_upwards [hab] with x hx
  exact ⟨sub_le_sub_right (mul_le_mul_of_nonneg_left hx.1 (dyadic_scale_pos i).le) _,
    sub_le_sub_right (mul_le_mul_of_nonneg_left hx.2 (dyadic_scale_pos i).le) _⟩

lemma dyadicLaw_map_componentRescale (μ : ProbabilityMeasure ℝ) (i k : ℤ) (m : ℕ) :
    dyadicLaw (μ.map (componentRescale i k)) m =
      (dyadicLaw μ (i + m)).map (fun j : ℤ ↦ j - (2 ^ m : ℤ) * k) := by
  apply PMF.toMeasure_injective
  rw [dyadicLaw_toMeasure, ← PMF.toMeasure_map _ _ (measurable_of_countable _), dyadicLaw_toMeasure]
  change ((μ : Measure ℝ).map (componentRescale i k)).map (dyadicQuantize m) = _
  rw [Measure.map_map (measurable_dyadicQuantize m) (measurable_componentRescale i k),
    Measure.map_map (measurable_of_countable _) (measurable_dyadicQuantize (i + m))]
  congr 1
  funext x
  exact dyadicQuantize_componentRescale i k m x

lemma dyadicEntropy_map_componentRescale (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i k : ℤ) (m : ℕ) :
    dyadicEntropy (μ.map (componentRescale i k)) (componentRescale_hasBoundedSupport μ hμ i k) m =
      dyadicEntropy μ hμ (i + m) := by
  have hinj : Function.Injective (fun j : ℤ ↦ j - (2 ^ m : ℤ) * k) := by
    intro a b hab
    exact (Int.sub_left_inj _).mp hab
  have h := finiteEntropy_map_of_injective (dyadicLaw μ (i + m))
    (dyadicLaw_support_finite μ hμ (i + m)) hinj
  simpa only [← dyadicLaw_map_componentRescale, dyadicEntropy] using h

lemma realConvolution_map_componentRescale (μ ν : ProbabilityMeasure ℝ) (i j k : ℤ) :
    realConvolution (μ.map (componentRescale i j)) (ν.map (componentRescale i k)) =
      (realConvolution μ ν).map (componentRescale i (j + k)) := by
  apply ProbabilityMeasure.toMeasure_injective
  change (((μ : Measure ℝ).map (componentRescale i j)).prod
    ((ν : Measure ℝ).map (componentRescale i k))).map (fun x : ℝ × ℝ ↦ x.1 + x.2) =
      (((μ : Measure ℝ).prod (ν : Measure ℝ)).map (fun x : ℝ × ℝ ↦ x.1 + x.2)).map
        (componentRescale i (j + k))
  rw [Measure.map_prod_map _ _ (measurable_componentRescale i j) (measurable_componentRescale i k),
    Measure.map_map measurable_add
      ((measurable_componentRescale i j).prodMap (measurable_componentRescale i k)),
    Measure.map_map (measurable_componentRescale i (j + k)) measurable_add]
  congr 1
  funext x
  simp only [Function.comp_apply, Prod.map, componentRescale, Int.cast_add]
  ring

/-- Fine entropy of raw component convolution equals entropy in normalized component coordinates. -/
theorem dyadicEntropy_convolution_rescaledComponents (μ ν : ProbabilityMeasure ℝ) (i : ℤ)
    (j : (dyadicLaw μ i).support) (k : (dyadicLaw ν i).support) (m : ℕ) :
    dyadicEntropy (realConvolution (rescaledComponent μ i j) (rescaledComponent ν i k))
      (realConvolution_hasBoundedSupport _ _ (rescaledComponent_hasBoundedSupport μ i j)
        (rescaledComponent_hasBoundedSupport ν i k)) m =
    dyadicEntropy (realConvolution (rawComponent μ i j) (rawComponent ν i k))
      (realConvolution_hasBoundedSupport _ _ (rawComponent_hasBoundedSupport μ i j)
        (rawComponent_hasBoundedSupport ν i k)) (i + m) := by
  have h := dyadicEntropy_map_componentRescale
    (realConvolution (rawComponent μ i j) (rawComponent ν i k))
    (realConvolution_hasBoundedSupport _ _ (rawComponent_hasBoundedSupport μ i j)
      (rawComponent_hasBoundedSupport ν i k)) i (j + k) m
  simpa only [← realConvolution_map_componentRescale, rescaledComponent] using h

end ExactOverlaps.Entropy
