module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Dyadic
public import Mathlib.Probability.ConditionalProbability

set_option maxSynthPendingDepth 3

/-!
# Dyadic component probability measures

Components are normalized restrictions of the original probability measure,
indexed only by cells of positive mass. Rescaled components are their actual
affine push-forwards. In particular no arbitrary choice on a null cell enters
the entropy averages.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.Components`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

lemma dyadicCell_measure_ne_zero (μ : ProbabilityMeasure ℝ) (i : ℤ)
    (k : (dyadicLaw μ i).support) : (μ : Measure ℝ) (dyadicCell i k) ≠ 0 := by
  rw [← dyadicLaw_apply]
  exact k.property

/-- The normalized restriction to a dyadic cell of positive mass. -/
noncomputable def rawComponent (μ : ProbabilityMeasure ℝ) (i : ℤ)
    (k : (dyadicLaw μ i).support) : ProbabilityMeasure ℝ :=
  ⟨(μ : Measure ℝ)[|dyadicCell i k],
    cond_isProbabilityMeasure (dyadicCell_measure_ne_zero μ i k)⟩

lemma rawComponent_apply (μ : ProbabilityMeasure ℝ) (i : ℤ)
    (k : (dyadicLaw μ i).support) (s : Set ℝ) :
    (rawComponent μ i k : Measure ℝ) s =
      ((μ : Measure ℝ) (dyadicCell i k))⁻¹ *
        (μ : Measure ℝ) (dyadicCell i k ∩ s) :=
  cond_apply (measurableSet_dyadicCell i k) _ _

lemma ae_rawComponent_mem (μ : ProbabilityMeasure ℝ) (i : ℤ)
    (k : (dyadicLaw μ i).support) :
    ∀ᵐ x ∂(rawComponent μ i k : Measure ℝ), x ∈ dyadicCell i k :=
  ae_cond_mem (measurableSet_dyadicCell i k)

lemma rawComponent_hasBoundedSupport (μ : ProbabilityMeasure ℝ) (i : ℤ)
    (k : (dyadicLaw μ i).support) : HasBoundedSupport (rawComponent μ i k) := by
  refine ⟨(k : ℝ) / (2 : ℝ) ^ i, ((k : ℝ) + 1) / (2 : ℝ) ^ i, ?_⟩
  filter_upwards [ae_rawComponent_mem μ i k] with x hx
  rw [dyadicCell_eq_Ico] at hx
  exact ⟨hx.1, hx.2.le⟩

/-- Affine coordinates sending a level-`i` cell to `[0,1)`. -/
noncomputable def componentRescale (i k : ℤ) (x : ℝ) : ℝ := (2 : ℝ) ^ i * x - k

@[fun_prop] lemma measurable_componentRescale (i k : ℤ) :
    Measurable (componentRescale i k) := by
  unfold componentRescale
  fun_prop

/-- The normalized component in unit-cell coordinates. -/
noncomputable def rescaledComponent (μ : ProbabilityMeasure ℝ) (i : ℤ)
    (k : (dyadicLaw μ i).support) : ProbabilityMeasure ℝ :=
  (rawComponent μ i k).map (componentRescale i k)

lemma ae_rescaledComponent_mem_Ico (μ : ProbabilityMeasure ℝ) (i : ℤ)
    (k : (dyadicLaw μ i).support) :
    ∀ᵐ x ∂(rescaledComponent μ i k : Measure ℝ), x ∈ Ico (0 : ℝ) 1 := by
  change ∀ᵐ x ∂((rawComponent μ i k : Measure ℝ).map (componentRescale i k)),
    x ∈ Ico (0 : ℝ) 1
  apply (ae_map_iff (measurable_componentRescale i k).aemeasurable
    (p := fun x : ℝ ↦ x ∈ Ico (0 : ℝ) 1) measurableSet_Ico).2
  filter_upwards [ae_rawComponent_mem μ i k] with x hx
  rw [mem_dyadicCell_iff] at hx
  dsimp [componentRescale]
  constructor <;> linarith [hx.1, hx.2]

lemma rescaledComponent_hasBoundedSupport (μ : ProbabilityMeasure ℝ) (i : ℤ)
    (k : (dyadicLaw μ i).support) : HasBoundedSupport (rescaledComponent μ i k) := by
  refine ⟨0, 1, ?_⟩
  filter_upwards [ae_rescaledComponent_mem_Ico μ i k] with x hx
  exact ⟨hx.1, hx.2.le⟩

lemma dyadicCell_inter_finer (i k j : ℤ) (m : ℕ) :
    dyadicCell i k ∩ dyadicCell (i + m) j =
      if j / (2 ^ m : ℕ) = k then dyadicCell (i + m) j else ∅ := by
  ext x
  by_cases h : j / (2 ^ m : ℕ) = k
  · rw [ite_eq_left h]
    simp only [mem_inter_iff, and_iff_right_iff_imp]
    intro hx
    change dyadicQuantize i x = k
    rw [dyadicQuantize_add_nat, show dyadicQuantize (i + m) x = j from hx]
    exact h
  · rw [ite_eq_right h]
    apply iff_false_intro
    rintro ⟨hx, hj⟩
    apply h
    change dyadicQuantize i x = k at hx
    change dyadicQuantize (i + m) x = j at hj
    rwa [dyadicQuantize_add_nat, hj] at hx

/-- The finer labels in a raw component have the actual conditional discrete law. -/
lemma dyadicLaw_rawComponent (μ : ProbabilityMeasure ℝ) (i : ℤ)
    (k : (dyadicLaw μ i).support) (m : ℕ) :
    dyadicLaw (rawComponent μ i k) (i + m) =
      conditionalPMF (dyadicLaw μ (i + m)) (fun j : ℤ ↦ j / (2 ^ m : ℕ))
        ⟨k, by simpa only [dyadicLaw_map_div] using k.property⟩ := by
  ext j
  rw [dyadicLaw_apply, rawComponent_apply, conditionalPMF_apply]
  simp only [dyadicLaw_map_div, dyadicLaw_apply, dyadicCell_inter_finer]
  by_cases h : j / (2 ^ m : ℕ) = k
  · simp only [h, ite_true, div_eq_mul_inv, mul_comm]
  · simp only [h, ite_false, measure_empty, mul_zero]

lemma dyadicQuantize_componentRescale (i k : ℤ) (m : ℕ) (x : ℝ) :
    dyadicQuantize m (componentRescale i k x) =
      dyadicQuantize (i + m) x - (2 ^ m : ℤ) * k := by
  unfold dyadicQuantize componentRescale
  have h : (2 : ℝ) ^ (m : ℤ) * ((2 : ℝ) ^ i * x - k) =
      (2 : ℝ) ^ (i + (m : ℤ)) * x - (((2 ^ m : ℤ) * k : ℤ) : ℝ) := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    push_cast
    simp only [zpow_natCast]
    ring
  rw [h, Int.floor_sub_intCast]

lemma dyadicLaw_rescaledComponent (μ : ProbabilityMeasure ℝ) (i : ℤ)
    (k : (dyadicLaw μ i).support) (m : ℕ) :
    dyadicLaw (rescaledComponent μ i k) m =
      (dyadicLaw (rawComponent μ i k) (i + m)).map
        (fun j : ℤ ↦ j - (2 ^ m : ℤ) * k) := by
  apply PMF.toMeasure_injective
  rw [dyadicLaw_toMeasure, ← PMF.toMeasure_map _ _ (measurable_of_countable _),
    dyadicLaw_toMeasure]
  change ((rawComponent μ i k : Measure ℝ).map (componentRescale i k)).map
    (dyadicQuantize m) = _
  rw [Measure.map_map (measurable_dyadicQuantize m) (measurable_componentRescale i k),
    Measure.map_map (measurable_of_countable _) (measurable_dyadicQuantize (i + m))]
  congr 1
  funext x
  exact dyadicQuantize_componentRescale i k m x

/-- Rescaling a component shifts the entropy level and relabels its cells bijectively. -/
lemma dyadicEntropy_rescaledComponent (μ : ProbabilityMeasure ℝ) (i : ℤ)
    (k : (dyadicLaw μ i).support) (m : ℕ) :
    dyadicEntropy (rescaledComponent μ i k) (rescaledComponent_hasBoundedSupport μ i k) m =
      dyadicEntropy (rawComponent μ i k) (rawComponent_hasBoundedSupport μ i k) (i + m) := by
  have hinj : Function.Injective (fun j : ℤ ↦ j - (2 ^ m : ℤ) * k) := by
    intro a b hab
    exact (Int.sub_left_inj _).mp hab
  have h := finiteEntropy_map_of_injective
    (dyadicLaw (rawComponent μ i k) (i + m))
    (dyadicLaw_support_finite _ (rawComponent_hasBoundedSupport μ i k) _) hinj
  simpa only [← dyadicLaw_rescaledComponent, dyadicEntropy] using h

/-- Average entropy of the finer partition in the positive-mass coarse cells. -/
noncomputable def averageRawComponentEntropy (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) : ℝ :=
  letI : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  ∑ k : (dyadicLaw μ i).support, ((dyadicLaw μ i) k).toReal *
    dyadicEntropy (rawComponent μ i k) (rawComponent_hasBoundedSupport μ i k) (i + m)

lemma averageRawComponentEntropy_eq_conditionalEntropy (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) :
    averageRawComponentEntropy μ hμ i m =
      conditionalEntropy (dyadicLaw μ (i + m)) (dyadicLaw_support_finite μ hμ (i + m))
        (fun j : ℤ ↦ j / (2 ^ m : ℕ)) := by
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  let : Fintype ((dyadicLaw μ (i + m)).map (fun j : ℤ ↦ j / (2 ^ m : ℕ))).support :=
    (show ((dyadicLaw μ (i + m)).map (fun j : ℤ ↦ j / (2 ^ m : ℕ))).support.Finite
      from by simpa using ((dyadicLaw_support_finite μ hμ (i + m)).image
        (fun j : ℤ ↦ j / (2 ^ m : ℕ)))).fintype
  rw [conditionalEntropy_eq_average]
  unfold averageRawComponentEntropy averageConditionalEntropy
  symm
  let e : ((dyadicLaw μ (i + m)).map (fun j : ℤ ↦ j / (2 ^ m : ℕ))).support ≃
      (dyadicLaw μ i).support :=
    { toFun := fun k ↦ ⟨k, by simpa only [dyadicLaw_map_div] using k.property⟩
      invFun := fun k ↦ ⟨k, by simpa only [dyadicLaw_map_div] using k.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  apply Fintype.sum_equiv e
  intro k
  have he : (e k : ℤ) = k := rfl
  simp only [dyadicEntropy, dyadicLaw_rawComponent, he]
  congr 1
  simp only [dyadicLaw_map_div]

/-- The partition entropy increment is exactly the weighted entropy of its raw components. -/
theorem averageRawComponentEntropy_eq_sub (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) :
    averageRawComponentEntropy μ hμ i m =
      dyadicEntropy μ hμ (i + m) - dyadicEntropy μ hμ i := by
  have h := finiteEntropy_chain_rule (dyadicLaw μ (i + m))
    (dyadicLaw_support_finite μ hμ (i + m)) (fun j : ℤ ↦ j / (2 ^ m : ℕ))
  simp only [dyadicLaw_map_div] at h
  rw [averageRawComponentEntropy_eq_conditionalEntropy]
  change finiteEntropy _ _ = finiteEntropy _ _ + _ at h
  dsimp [dyadicEntropy]
  simp only [Nat.cast_pow, Nat.cast_ofNat] at h
  linarith

end ExactOverlaps.Entropy
