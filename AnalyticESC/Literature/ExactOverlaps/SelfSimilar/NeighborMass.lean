module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.InformationIntegral
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

set_option maxSynthPendingDepth 3

/-!
Neighboring-cell probability estimates. The probability of landing in a
cell whose mass is a small fraction of its three-cell neighborhood is at
most three times that fraction. This handles dyadic boundary effects using
mass, without a nonatomicity or geometric separation assumption.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.NeighborMass`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Classical

namespace ExactOverlaps.Entropy

noncomputable def neighborMass (p : PMF ℤ) (k : ℤ) : ℝ≥0∞ :=
  p (k - 1) + p k + p (k + 1)

theorem tsum_neighborMass (p : PMF ℤ) : ∑' k, neighborMass p k = 3 := by
  have hleft : ∑' k : ℤ, p (k - 1) = 1 := by
    have h := (Equiv.addRight (-1 : ℤ)).tsum_eq (fun k ↦ p k)
    change (∑' k : ℤ, p (k + -1)) = ∑' k : ℤ, p k at h
    simpa only [sub_eq_add_neg, p.tsum_coe] using h
  have hright : ∑' k : ℤ, p (k + 1) = 1 := by
    have h := (Equiv.addRight (1 : ℤ)).tsum_eq (fun k ↦ p k)
    change (∑' k : ℤ, p (k + 1)) = ∑' k : ℤ, p k at h
    simpa only [p.tsum_coe] using h
  simp only [neighborMass, ENNReal.tsum_add, hleft, hright, p.tsum_coe]
  norm_num

theorem neighborMass_bad_mass_le (p : PMF ℤ) (t : ℝ≥0∞) :
    p.toOuterMeasure {k | p k ≤ t * neighborMass p k} ≤ 3 * t := by
  rw [PMF.toOuterMeasure_apply]
  calc
    ∑' k, {k | p k ≤ t * neighborMass p k}.indicator p k ≤
        ∑' k, t * neighborMass p k := by
      apply ENNReal.tsum_le_tsum
      intro k
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      by_cases hk : p k ≤ t * neighborMass p k
      · simpa only [ite_eq_left hk] using hk
      · simp only [ite_eq_right hk]
        positivity
    _ = 3 * t := by rw [ENNReal.tsum_mul_left, tsum_neighborMass, mul_comm]

theorem dyadic_neighborMass_bad_mass_le (μ : ProbabilityMeasure ℝ) (i : ℤ) (t : ℝ≥0∞) :
    (μ : Measure ℝ) {x | dyadicLaw μ i (dyadicQuantize i x) ≤
      t * neighborMass (dyadicLaw μ i) (dyadicQuantize i x)} ≤ 3 * t := by
  let E : Set ℤ := {k | dyadicLaw μ i k ≤ t * neighborMass (dyadicLaw μ i) k}
  have hE : MeasurableSet E := (Set.to_countable E).measurableSet
  have he : (μ : Measure ℝ) {x | dyadicLaw μ i (dyadicQuantize i x) ≤
      t * neighborMass (dyadicLaw μ i) (dyadicQuantize i x)} = (dyadicLaw μ i).toMeasure E := by
    rw [dyadicLaw_toMeasure, Measure.map_apply (measurable_dyadicQuantize i) hE]
    rfl
  rw [he, PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hE]
  exact neighborMass_bad_mass_le _ t

/-- Summably small relative thresholds eventually exclude exceptional cells almost surely. -/
theorem ae_eventually_cell_mass_gt_neighbor_fraction (μ : ProbabilityMeasure ℝ)
    (t : ℕ → ℝ≥0∞) (ht : (∑' n, 3 * t n) ≠ ⊤) :
    ∀ᵐ x ∂(μ : Measure ℝ), ∀ᶠ n : ℕ in atTop,
      t n * neighborMass (dyadicLaw μ n) (dyadicQuantize n x) <
        dyadicLaw μ n (dyadicQuantize n x) := by
  have hs : (∑' n : ℕ, (μ : Measure ℝ) {x | dyadicLaw μ n (dyadicQuantize n x) ≤
      t n * neighborMass (dyadicLaw μ n) (dyadicQuantize n x)}) ≠ ⊤ :=
    ne_top_of_le_ne_top ht (ENNReal.tsum_le_tsum (fun n ↦ dyadic_neighborMass_bad_mass_le μ n (t n)))
  have h := ae_eventually_notMem hs
  filter_upwards [h] with x hx
  filter_upwards [hx] with n hn
  exact lt_of_not_ge hn

end ExactOverlaps.Entropy
