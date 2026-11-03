module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Convolution
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.QuantizedCoupling
public import Mathlib.MeasureTheory.Group.Convolution

set_option maxSynthPendingDepth 3

/-!
# Real convolution and its independent dyadic labels

These constructions use arbitrary bounded Borel probability measures, including
nonatomic measures. Their dyadic label pair is exactly the independent product
of the two discretized laws.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.RealConvolution`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.Entropy

noncomputable def realIndependentPair (μ ν : ProbabilityMeasure ℝ) :
    ProbabilityMeasure (ℝ × ℝ) := ((μ : Measure ℝ).prod (ν : Measure ℝ)).toProbabilityMeasure

lemma realIndependentPair_map_fst (μ ν : ProbabilityMeasure ℝ) :
    (realIndependentPair μ ν).map Prod.fst = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((μ : Measure ℝ).prod (ν : Measure ℝ)).map Prod.fst = (μ : Measure ℝ)
  simp only [Measure.map_fst_prod, measure_univ, one_smul]

lemma realIndependentPair_map_snd (μ ν : ProbabilityMeasure ℝ) :
    (realIndependentPair μ ν).map Prod.snd = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((μ : Measure ℝ).prod (ν : Measure ℝ)).map Prod.snd = (ν : Measure ℝ)
  simp only [Measure.map_snd_prod, measure_univ, one_smul]

noncomputable def realConvolution (μ ν : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  (realIndependentPair μ ν).map (fun x ↦ x.1 + x.2)

lemma realConvolution_toMeasure (μ ν : ProbabilityMeasure ℝ) :
    (realConvolution μ ν : Measure ℝ) = (μ : Measure ℝ) ∗ (ν : Measure ℝ) := by
  rw [realConvolution, ProbabilityMeasure.toMeasure_map]
  rfl

lemma realConvolution_comm (μ ν : ProbabilityMeasure ℝ) : realConvolution μ ν = realConvolution ν μ := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [realConvolution_toMeasure, Measure.conv_comm]

lemma realConvolution_assoc (μ ν ρ : ProbabilityMeasure ℝ) :
    realConvolution (realConvolution μ ν) ρ = realConvolution μ (realConvolution ν ρ) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [realConvolution_toMeasure, Measure.conv_assoc]

lemma ae_realIndependentPair_mem (μ ν : ProbabilityMeasure ℝ) {a b c d : ℝ}
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a b)
    (hν : ∀ᵐ y ∂(ν : Measure ℝ), y ∈ Icc c d) :
    ∀ᵐ z ∂(realIndependentPair μ ν : Measure (ℝ × ℝ)), z.1 ∈ Icc a b ∧ z.2 ∈ Icc c d := by
  change ∀ᵐ z ∂((μ : Measure ℝ).prod (ν : Measure ℝ)), z ∈ Icc a b ×ˢ Icc c d
  apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Icc.prod measurableSet_Icc)).mpr
  filter_upwards [hμ] with x hx
  filter_upwards [hν] with y hy
  exact ⟨hx, hy⟩

lemma realConvolution_hasBoundedSupport (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν) :
    HasBoundedSupport (realConvolution μ ν) := by
  obtain ⟨a, b, hab⟩ := hμ
  obtain ⟨c, d, hcd⟩ := hν
  refine ⟨a + c, b + d, ?_⟩
  rw [realConvolution, ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff (measurable_fst.add measurable_snd).aemeasurable
    (p := fun x : ℝ ↦ x ∈ Icc (a + c) (b + d)) measurableSet_Icc).mpr
  filter_upwards [ae_realIndependentPair_mem μ ν hab hcd] with z hz
  exact ⟨add_le_add hz.1.1 hz.2.1, add_le_add hz.1.2 hz.2.2⟩

/-- Quantizing independent real inputs yields the actual independent discrete pair. -/
theorem dyadicPairLaw_eq_independentPair (μ ν : ProbabilityMeasure ℝ) (i : ℤ) :
    integerCouplingLaw (realIndependentPair μ ν)
      (fun x ↦ dyadicQuantize i x.1) (fun x ↦ dyadicQuantize i x.2) =
      independentPair (dyadicLaw μ i) (dyadicLaw ν i) := by
  ext z
  rcases z with ⟨j, k⟩
  have hfst : Measurable (fun x : ℝ × ℝ ↦ dyadicQuantize i x.1) :=
    (measurable_dyadicQuantize i).comp measurable_fst
  have hsnd : Measurable (fun x : ℝ × ℝ ↦ dyadicQuantize i x.2) :=
    (measurable_dyadicQuantize i).comp measurable_snd
  rw [integerCouplingLaw_apply _ _ _ hfst hsnd, independentPair_apply,
    dyadicLaw_apply, dyadicLaw_apply]
  change ((μ : Measure ℝ).prod (ν : Measure ℝ))
      {x : ℝ × ℝ | (dyadicQuantize i x.1, dyadicQuantize i x.2) = (j, k)} = _
  have he : {x : ℝ × ℝ | (dyadicQuantize i x.1, dyadicQuantize i x.2) = (j, k)} =
      dyadicCell i j ×ˢ dyadicCell i k := by
    ext x
    simp only [mem_ofPred_eq, Prod.mk.injEq, mem_prod, dyadicCell]
  rw [he, Measure.prod_prod]

end ExactOverlaps.Entropy
