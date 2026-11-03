module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.RealConvolution

set_option maxSynthPendingDepth 3

/-!
# Entropy of a dyadic convolution and the discretization carry

The dyadic label of a sum differs from the sum of its labels by either zero
or one. A genuine coupling therefore bounds the entropy discrepancy by log 2,
for arbitrary bounded Borel probability measures and every integer level.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.DyadicConvolution`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.Entropy

lemma dyadicQuantize_add_carry (i : ℤ) (x y : ℝ) :
    dyadicQuantize i x + dyadicQuantize i y - dyadicQuantize i (x + y) ∈
      Icc (-1 : ℤ) 0 := by
  have hlo := Int.le_floor_add ((2 : ℝ) ^ i * x) ((2 : ℝ) ^ i * y)
  have hhi := Int.le_floor_add_floor ((2 : ℝ) ^ i * x) ((2 : ℝ) ^ i * y)
  simp only [dyadicQuantize, mul_add, mem_Icc]
  constructor <;> omega

lemma sum_dyadicPairLaw (μ ν : ProbabilityMeasure ℝ) (i : ℤ) :
    ((realIndependentPair μ ν).map
      (fun x ↦ dyadicQuantize i x.1 + dyadicQuantize i x.2)).toMeasure.toPMF =
      discreteConvolution (dyadicLaw μ i) (dyadicLaw ν i) := by
  rw [discreteConvolution, ← dyadicPairLaw_eq_independentPair μ ν i]
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  simp only [integerCouplingLaw, Measure.toPMF_toMeasure, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (measurable_of_countable _) (by
    exact ((measurable_dyadicQuantize i).comp measurable_fst).prodMk
      ((measurable_dyadicQuantize i).comp measurable_snd))]
  rfl

/-- Quantize after convolution or convolve the quantized laws: the cost is at most log 2. -/
theorem abs_discreteConvolution_entropy_sub_dyadicEntropy_le_log_two
    (μ ν : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν) (i : ℤ) :
    |finiteEntropy (discreteConvolution (dyadicLaw μ i) (dyadicLaw ν i))
        (discreteConvolution_support_finite _ _ (dyadicLaw_support_finite μ hμ i)
          (dyadicLaw_support_finite ν hν i)) -
      dyadicEntropy (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν) i| ≤
        Real.log 2 := by
  let P := realIndependentPair μ ν
  let f : ℝ × ℝ → ℤ := fun x ↦ dyadicQuantize i (x.1 + x.2)
  let g : ℝ × ℝ → ℤ := fun x ↦ dyadicQuantize i x.1 + dyadicQuantize i x.2
  have hf : Measurable f := (measurable_dyadicQuantize i).comp (measurable_fst.add measurable_snd)
  have hg : Measurable g := ((measurable_dyadicQuantize i).comp measurable_fst).add
    ((measurable_dyadicQuantize i).comp measurable_snd)
  let p := integerCouplingLaw P f g
  have hp : p.support.Finite := by
    obtain ⟨a, b, hab⟩ := realConvolution_hasBoundedSupport μ ν hμ hν
    have hab' : ∀ᵐ x ∂(P : Measure (ℝ × ℝ)), x.1 + x.2 ∈ Icc a b :=
      ae_of_ae_map (measurable_fst.add measurable_snd).aemeasurable hab
    apply integerCouplingLaw_support_finite P f g hf hg
      (Set.finite_Icc (dyadicQuantize i a) (dyadicQuantize i b))
      (Set.finite_Icc (dyadicQuantize i a - 1) (dyadicQuantize i b))
    filter_upwards [hab'] with x hx
    have hlo : dyadicQuantize i a ≤ f x :=
      Int.floor_mono (mul_le_mul_of_nonneg_left hx.1 (dyadic_scale_pos i).le)
    have hhi : f x ≤ dyadicQuantize i b :=
      Int.floor_mono (mul_le_mul_of_nonneg_left hx.2 (dyadic_scale_pos i).le)
    have hc : g x - f x ∈ Icc (-1 : ℤ) 0 := dyadicQuantize_add_carry i x.1 x.2
    exact ⟨⟨hlo, hhi⟩, ⟨by have := hc.1; omega, by have := hc.2; omega⟩⟩
  have hband : ∀ z ∈ p.support, z.2 - z.1 ∈ Icc (-1 : ℤ) 0 := by
    apply integerCouplingLaw_support_subset P f g hf hg
    exact Filter.Eventually.of_forall (fun x ↦ dyadicQuantize_add_carry i x.1 x.2)
  have hfst : p.map Prod.fst = dyadicLaw (realConvolution μ ν) i :=
    (integerCouplingLaw_map_fst P f g hf hg).trans
      (dyadicLaw_map P (fun x ↦ x.1 + x.2) (measurable_fst.add measurable_snd) i).symm
  have hsnd : p.map Prod.snd = discreteConvolution (dyadicLaw μ i) (dyadicLaw ν i) :=
    (integerCouplingLaw_map_snd P f g hf hg).trans (sum_dyadicPairLaw μ ν i)
  have h := abs_snd_entropy_sub_fst_le_of_sub_mem_Icc p hp hband
  simpa only [hfst, hsnd, dyadicEntropy, show (0 - (-1 : ℤ) + 1).toNat = 2 from by decide,
    Nat.cast_ofNat] using h

end ExactOverlaps.Entropy
