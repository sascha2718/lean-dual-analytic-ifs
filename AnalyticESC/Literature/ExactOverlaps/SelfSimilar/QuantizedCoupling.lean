module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.DyadicStability

set_option maxSynthPendingDepth 3

/-!
Bounded-displacement stability for dyadic entropy. The comparison is expressed
using a genuine coupling, so it applies to finite approximation and stationary
laws even when the stationary law is nonatomic.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.QuantizedCoupling`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Classical ENNReal

namespace ExactOverlaps.Entropy

variable {Ω : Type*} [MeasurableSpace Ω]

theorem dyadicLaw_map (P : ProbabilityMeasure Ω) (X : Ω → ℝ)
    (hX : Measurable X) (i : ℤ) :
    dyadicLaw (P.map X) i = (P.map (dyadicQuantize i ∘ X)).toMeasure.toPMF := by
  apply PMF.toMeasure_injective
  simp only [dyadicLaw, Measure.toPMF_toMeasure, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (measurable_dyadicQuantize i) hX]

theorem dyadicCoupling_support_finite (P : ProbabilityMeasure Ω) (X Y : Ω → ℝ)
    (hXm : Measurable X) (hYm : Measurable Y)
    (hX : HasBoundedSupport (P.map X)) (hY : HasBoundedSupport (P.map Y)) (i : ℤ) :
    (integerCouplingLaw P (dyadicQuantize i ∘ X) (dyadicQuantize i ∘ Y)).support.Finite := by
  obtain ⟨a, b, hab⟩ := hX
  obtain ⟨c, d, hcd⟩ := hY
  rw [ProbabilityMeasure.toMeasure_map] at hab hcd
  have hab' := ae_of_ae_map hXm.aemeasurable hab
  have hcd' := ae_of_ae_map hYm.aemeasurable hcd
  apply integerCouplingLaw_support_finite P _ _
    ((measurable_dyadicQuantize i).comp hXm) ((measurable_dyadicQuantize i).comp hYm)
    (Set.finite_Icc (dyadicQuantize i a) (dyadicQuantize i b))
    (Set.finite_Icc (dyadicQuantize i c) (dyadicQuantize i d))
  filter_upwards [hab', hcd'] with ω hωX hωY
  exact ⟨⟨Int.floor_mono (mul_le_mul_of_nonneg_left hωX.1 (dyadic_scale_pos i).le),
    Int.floor_mono (mul_le_mul_of_nonneg_left hωX.2 (dyadic_scale_pos i).le)⟩,
    ⟨Int.floor_mono (mul_le_mul_of_nonneg_left hωY.1 (dyadic_scale_pos i).le),
    Int.floor_mono (mul_le_mul_of_nonneg_left hωY.2 (dyadic_scale_pos i).le)⟩⟩

theorem floor_sub_mem_Icc_of_abs_sub_le {x y : ℝ} {K : ℕ} (h : |y - x| ≤ K) :
    ⌊y⌋ - ⌊x⌋ ∈ Icc (-(K : ℤ) - 1) ((K : ℤ) + 1) := by
  obtain ⟨hl, hu⟩ := abs_le.mp h
  have hxlo := Int.floor_le x
  have hxhi := Int.lt_floor_add_one x
  have hylo := Int.floor_le y
  have hyhi := Int.lt_floor_add_one y
  constructor
  · have hh : -(K : ℝ) - 1 ≤ (⌊y⌋ : ℝ) - (⌊x⌋ : ℝ) := by linarith
    exact_mod_cast hh
  · have hh : (⌊y⌋ : ℝ) - (⌊x⌋ : ℝ) ≤ (K : ℝ) + 1 := by linarith
    exact_mod_cast hh

/-- Entropy is stable under displacement bounded by K mesh widths. -/
theorem abs_dyadicEntropy_sub_le_of_coupling (P : ProbabilityMeasure Ω)
    (X Y : Ω → ℝ) (hXm : Measurable X) (hYm : Measurable Y)
    (hX : HasBoundedSupport (P.map X)) (hY : HasBoundedSupport (P.map Y))
    (i : ℤ) (K : ℕ)
    (hdisp : ∀ᵐ ω ∂(P : Measure Ω), |(2 : ℝ) ^ i * (Y ω - X ω)| ≤ K) :
    |dyadicEntropy (P.map Y) hY i - dyadicEntropy (P.map X) hX i| ≤
      Real.log (2 * K + 3 : ℝ) := by
  let f := dyadicQuantize i ∘ X
  let g := dyadicQuantize i ∘ Y
  have hf : Measurable f := (measurable_dyadicQuantize i).comp hXm
  have hg : Measurable g := (measurable_dyadicQuantize i).comp hYm
  let p := integerCouplingLaw P f g
  have hp : p.support.Finite := dyadicCoupling_support_finite P X Y hXm hYm hX hY i
  have hband : ∀ z ∈ p.support, z.2 - z.1 ∈ Icc (-(K : ℤ) - 1) ((K : ℤ) + 1) := by
    apply integerCouplingLaw_support_subset P f g hf hg
    filter_upwards [hdisp] with ω hω
    apply floor_sub_mem_Icc_of_abs_sub_le
    simpa only [mul_sub] using hω
  have h := abs_snd_entropy_sub_fst_le_of_sub_mem_Icc p hp hband
  have hfst : p.map Prod.fst = dyadicLaw (P.map X) i :=
    (integerCouplingLaw_map_fst P f g hf hg).trans (dyadicLaw_map P X hXm i).symm
  have hsnd : p.map Prod.snd = dyadicLaw (P.map Y) i :=
    (integerCouplingLaw_map_snd P f g hf hg).trans (dyadicLaw_map P Y hYm i).symm
  have hcount : (((K : ℤ) + 1 - (-(K : ℤ) - 1) + 1).toNat : ℝ) = 2 * K + 3 := by
    have he : (K : ℤ) + 1 - (-(K : ℤ) - 1) + 1 = ((2 * K + 3 : ℕ) : ℤ) := by omega
    rw [he, Int.toNat_natCast]
    push_cast
    rfl
  simpa only [hfst, hsnd, hcount, dyadicEntropy] using h

end ExactOverlaps.Entropy
