module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.PairEntropyComparison
public import AnalyticESC.Literature.ExactOverlaps.Entropy.Dyadic

set_option maxSynthPendingDepth 3

/-!
Quantized couplings of Borel probability measures. All probability masses are
actual pushforwards. Almost-sure support and label-difference bounds transfer
to these finite laws, allowing the entropy comparison theorem to be applied
to nonatomic measures as well as atomic ones.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.DyadicStability`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Classical ENNReal

namespace ExactOverlaps.Entropy

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The joint law of two integer-valued statistics. -/
noncomputable def integerCouplingLaw (μ : ProbabilityMeasure Ω)
    (f g : Ω → ℤ) : PMF (ℤ × ℤ) :=
  (μ.map (fun x ↦ (f x, g x))).toMeasure.toPMF

theorem integerCouplingLaw_apply (μ : ProbabilityMeasure Ω) (f g : Ω → ℤ)
    (hf : Measurable f) (hg : Measurable g) (z : ℤ × ℤ) :
    integerCouplingLaw μ f g z = (μ : Measure Ω) {x | (f x, g x) = z} := by
  rw [integerCouplingLaw, Measure.toPMF_apply,
    ProbabilityMeasure.map_apply' μ (hf.prodMk hg).aemeasurable
      (measurableSet_singleton z)]
  rfl

/-- An almost-sure relation between statistics holds at every positive-mass atom. -/
theorem integerCouplingLaw_support_subset (μ : ProbabilityMeasure Ω) (f g : Ω → ℤ)
    (hf : Measurable f) (hg : Measurable g) {S : Set (ℤ × ℤ)}
    (hS : ∀ᵐ x ∂(μ : Measure Ω), (f x, g x) ∈ S) :
    (integerCouplingLaw μ f g).support ⊆ S := by
  intro z hz
  by_contra hnot
  apply hz
  rw [integerCouplingLaw_apply μ f g hf hg]
  apply measure_mono_null (t := {x | (f x, g x) ∉ S})
  · intro x hx
    change (f x, g x) = z at hx
    change (f x, g x) ∉ S
    simpa only [hx] using hnot
  · exact ae_iff.mp hS

theorem integerCouplingLaw_support_finite (μ : ProbabilityMeasure Ω) (f g : Ω → ℤ)
    (hf : Measurable f) (hg : Measurable g) {A B : Set ℤ}
    (hA : A.Finite) (hB : B.Finite)
    (hbound : ∀ᵐ x ∂(μ : Measure Ω), f x ∈ A ∧ g x ∈ B) :
    (integerCouplingLaw μ f g).support.Finite :=
  (hA.prod hB).subset (integerCouplingLaw_support_subset μ f g hf hg hbound)

/-- The first marginal of the joint quantized law is the direct pushforward law. -/
theorem integerCouplingLaw_map_fst (μ : ProbabilityMeasure Ω) (f g : Ω → ℤ)
    (hf : Measurable f) (hg : Measurable g) :
    (integerCouplingLaw μ f g).map Prod.fst = (μ.map f).toMeasure.toPMF := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  simp only [integerCouplingLaw, Measure.toPMF_toMeasure, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (measurable_of_countable _) (hf.prodMk hg)]
  rfl

theorem integerCouplingLaw_map_snd (μ : ProbabilityMeasure Ω) (f g : Ω → ℤ)
    (hf : Measurable f) (hg : Measurable g) :
    (integerCouplingLaw μ f g).map Prod.snd = (μ.map g).toMeasure.toPMF := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  simp only [integerCouplingLaw, Measure.toPMF_toMeasure, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (measurable_of_countable _) (hf.prodMk hg)]
  rfl

end ExactOverlaps.Entropy
