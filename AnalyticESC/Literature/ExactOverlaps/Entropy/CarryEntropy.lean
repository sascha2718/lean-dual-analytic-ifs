module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.ConvolutionCoupling

set_option maxSynthPendingDepth 3

/-!
# Entropy cost of a bounded dyadic carry

The real and integer coordinates may be dependent. An almost-sure carry in
an interval of K+1 integers costs at most log(K+1) in Shannon entropy.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.CarryEntropy`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set

namespace ExactOverlaps.Entropy

theorem abs_integerLaw_entropy_sub_dyadicEntropy_le
    (P : ProbabilityMeasure (ℝ × ℤ)) (hX : HasBoundedSupport (P.map Prod.fst))
    (hY : (P.map Prod.snd).toMeasure.toPMF.support.Finite)
    (i : ℤ) (K : ℕ) (hc : HasDyadicCarryBound P i K) :
    |finiteEntropy (P.map Prod.snd).toMeasure.toPMF hY -
      dyadicEntropy (P.map Prod.fst) hX i| ≤ Real.log ((K : ℝ) + 1) := by
  let f : ℝ × ℤ → ℤ := fun x ↦ dyadicQuantize i x.1
  let g : ℝ × ℤ → ℤ := Prod.snd
  have hf : Measurable f := (measurable_dyadicQuantize i).comp measurable_fst
  have hg : Measurable g := measurable_snd
  let p := integerCouplingLaw P f g
  have hp : p.support.Finite := by
    obtain ⟨a, b, hab⟩ := hX
    have hab' : ∀ᵐ x ∂(P : Measure (ℝ × ℤ)), x.1 ∈ Icc a b :=
      ae_of_ae_map measurable_fst.aemeasurable hab
    apply integerCouplingLaw_support_finite P f g hf hg
      (Set.finite_Icc (dyadicQuantize i a) (dyadicQuantize i b))
      (Set.finite_Icc (dyadicQuantize i a - K) (dyadicQuantize i b))
    filter_upwards [hab', hc] with x hx hcarry
    have hlo : dyadicQuantize i a ≤ f x :=
      Int.floor_mono (mul_le_mul_of_nonneg_left hx.1 (dyadic_scale_pos i).le)
    have hhi : f x ≤ dyadicQuantize i b :=
      Int.floor_mono (mul_le_mul_of_nonneg_left hx.2 (dyadic_scale_pos i).le)
    change g x - f x ∈ Icc (-(K : ℤ)) 0 at hcarry
    exact ⟨⟨hlo, hhi⟩, ⟨by have := hcarry.1; omega, by have := hcarry.2; omega⟩⟩
  have hband : ∀ z ∈ p.support, z.2 - z.1 ∈ Icc (-(K : ℤ)) 0 :=
    integerCouplingLaw_support_subset P f g hf hg hc
  have hfst : p.map Prod.fst = dyadicLaw (P.map Prod.fst) i :=
    (integerCouplingLaw_map_fst P f g hf hg).trans
      (dyadicLaw_map P Prod.fst measurable_fst i).symm
  have hsnd : p.map Prod.snd = (P.map Prod.snd).toMeasure.toPMF :=
    integerCouplingLaw_map_snd P f g hf hg
  have h := abs_snd_entropy_sub_fst_le_of_sub_mem_Icc p hp hband
  have hcount : (0 - (-(K : ℤ)) + 1).toNat = K + 1 := by omega
  simpa only [hfst, hsnd, dyadicEntropy, hcount, Nat.cast_add, Nat.cast_one] using h

end ExactOverlaps.Entropy
