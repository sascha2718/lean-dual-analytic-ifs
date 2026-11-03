module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.ConvolutionBounds
public import AnalyticESC.Literature.ExactOverlaps.Entropy.DiscreteMeasureConvolution

set_option maxSynthPendingDepth 3

/-!
# Coupling real sums to sums of their dyadic labels

A probability law on a real coordinate and an integer coordinate remembers
the original sum together with its discretized sum. Convolution preserves
both marginals and adds at most one extra unit of dyadic rounding error.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.ConvolutionCoupling`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set

namespace ExactOverlaps.Entropy

noncomputable def mixedConvolution (P Q : ProbabilityMeasure (ℝ × ℤ)) :
    ProbabilityMeasure (ℝ × ℤ) := ((P : Measure (ℝ × ℤ)) ∗ (Q : Measure (ℝ × ℤ))).toProbabilityMeasure

lemma mixedConvolution_map_fst (P Q : ProbabilityMeasure (ℝ × ℤ)) :
    (mixedConvolution P Q).map Prod.fst = realConvolution (P.map Prod.fst) (Q.map Prod.fst) := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [realConvolution_toMeasure]
  let L : (ℝ × ℤ) →+ ℝ :=
    { toFun := Prod.fst, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  exact Measure.map_conv_addMonoidHom L measurable_fst

lemma mixedConvolution_integerLaw (P Q : ProbabilityMeasure (ℝ × ℤ)) :
    ((mixedConvolution P Q).map Prod.snd).toMeasure.toPMF =
      discreteConvolution (P.map Prod.snd).toMeasure.toPMF (Q.map Prod.snd).toMeasure.toPMF := by
  apply PMF.toMeasure_injective
  rw [Measure.toPMF_toMeasure, discreteConvolution_toMeasure, Measure.toPMF_toMeasure,
    Measure.toPMF_toMeasure]
  let L : (ℝ × ℤ) →+ ℤ :=
    { toFun := Prod.snd, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  exact Measure.map_conv_addMonoidHom L measurable_snd

noncomputable def dyadicLift (μ : ProbabilityMeasure ℝ) (i : ℤ) : ProbabilityMeasure (ℝ × ℤ) :=
  μ.map (fun x ↦ (x, dyadicQuantize i x))

lemma measurable_dyadicLiftMap (i : ℤ) :
    Measurable (fun x : ℝ ↦ (x, dyadicQuantize i x)) :=
  measurable_id.prodMk (measurable_dyadicQuantize i)

lemma dyadicLift_map_fst (μ : ProbabilityMeasure ℝ) (i : ℤ) :
    (dyadicLift μ i).map Prod.fst = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((μ : Measure ℝ).map (fun x ↦ (x, dyadicQuantize i x))).map Prod.fst = (μ : Measure ℝ)
  rw [Measure.map_map measurable_fst (measurable_dyadicLiftMap i)]
  exact Measure.map_id

lemma dyadicLift_integerLaw (μ : ProbabilityMeasure ℝ) (i : ℤ) :
    ((dyadicLift μ i).map Prod.snd).toMeasure.toPMF = dyadicLaw μ i := by
  apply PMF.toMeasure_injective
  rw [Measure.toPMF_toMeasure, dyadicLaw_toMeasure]
  change ((μ : Measure ℝ).map (fun x ↦ (x, dyadicQuantize i x))).map Prod.snd = _
  rw [Measure.map_map measurable_snd (measurable_dyadicLiftMap i)]
  rfl

/-- A downward dyadic label error of at most K units, almost surely. -/
def HasDyadicCarryBound (P : ProbabilityMeasure (ℝ × ℤ)) (i : ℤ) (K : ℕ) : Prop :=
  ∀ᵐ z ∂(P : Measure (ℝ × ℤ)), z.2 - dyadicQuantize i z.1 ∈ Icc (-(K : ℤ)) 0

lemma measurableSet_dyadicCarryBound (i : ℤ) (K : ℕ) :
    MeasurableSet {z : ℝ × ℤ | z.2 - dyadicQuantize i z.1 ∈ Icc (-(K : ℤ)) 0} :=
  measurableSet_Icc.preimage
    (measurable_snd.sub ((measurable_dyadicQuantize i).comp measurable_fst))

lemma dyadicLift_carryBound (μ : ProbabilityMeasure ℝ) (i : ℤ) :
    HasDyadicCarryBound (dyadicLift μ i) i 0 := by
  unfold HasDyadicCarryBound dyadicLift
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff (measurable_dyadicLiftMap i).aemeasurable
    (measurableSet_dyadicCarryBound i 0)).mpr
  exact Filter.Eventually.of_forall (fun x ↦ by simp)

lemma mixedConvolution_carryBound (P Q : ProbabilityMeasure (ℝ × ℤ))
    (i : ℤ) {K L : ℕ} (hP : HasDyadicCarryBound P i K) (hQ : HasDyadicCarryBound Q i L) :
    HasDyadicCarryBound (mixedConvolution P Q) i (K + L + 1) := by
  unfold HasDyadicCarryBound at *
  change ∀ᵐ z ∂(((P : Measure (ℝ × ℤ)).prod (Q : Measure (ℝ × ℤ))).map
    (fun x ↦ x.1 + x.2)), z.2 - dyadicQuantize i z.1 ∈ Icc (-((K + L + 1 : ℕ) : ℤ)) 0
  apply (ae_map_iff measurable_add.aemeasurable (measurableSet_dyadicCarryBound i (K + L + 1))).mpr
  apply (Measure.ae_prod_iff_ae_ae
    ((measurableSet_dyadicCarryBound i (K + L + 1)).preimage measurable_add)).mpr
  filter_upwards [hP] with x hx
  filter_upwards [hQ] with y hy
  have hc := dyadicQuantize_add_carry i x.1 y.1
  change x.2 + y.2 - dyadicQuantize i (x.1 + y.1) ∈ Icc (-((K + L + 1 : ℕ) : ℤ)) 0
  simp only [mem_Icc, Nat.cast_add, Nat.cast_one] at *
  constructor <;> omega

end ExactOverlaps.Entropy
