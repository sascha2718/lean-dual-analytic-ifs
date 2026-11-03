module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Components
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

set_option maxSynthPendingDepth 3

/-!
# Density bounds on dyadic cells

All bounds concern actual measure masses, with explicit positive cell width.
The ambient probability may have unbounded support.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.DensityBounds`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.Entropy

lemma volume_dyadicCell (i k : ℤ) :
    volume (dyadicCell i k) = ENNReal.ofReal ((2 : ℝ) ^ (-i)) := by
  rw [dyadicCell_eq_Ico, Real.volume_Ico]
  congr 1
  rw [add_div]
  simp [zpow_neg, one_div]

lemma measure_le_of_density_upper (μ : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (hμ : (μ : Measure ℝ) = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    {s : Set ℝ} (hs : MeasurableSet s) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ x ∈ s, f x ≤ b) (hvol : volume s ≠ ∞) :
    ((μ : Measure ℝ) s).toReal ≤ b * (volume s).toReal := by
  have h : (μ : Measure ℝ) s ≤ ENNReal.ofReal b * volume s := by
    rw [hμ, withDensity_apply _ hs]
    calc
      _ ≤ ∫⁻ _x in s, ENNReal.ofReal b := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hs] with x hx
        exact ENNReal.ofReal_le_ofReal (hbound x hx)
      _ = _ := by simp
  have ht : ENNReal.ofReal b * volume s ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvol
  have hr := ENNReal.toReal_mono ht h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hb] using hr

lemma measure_ge_of_density_lower (μ : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (hμ : (μ : Measure ℝ) = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    {s : Set ℝ} (hs : MeasurableSet s) {a : ℝ} (ha : 0 ≤ a)
    (hbound : ∀ x ∈ s, a ≤ f x) :
    a * (volume s).toReal ≤ ((μ : Measure ℝ) s).toReal := by
  have h : ENNReal.ofReal a * volume s ≤ (μ : Measure ℝ) s := by
    rw [hμ, withDensity_apply _ hs]
    calc
      _ = ∫⁻ _x in s, ENNReal.ofReal a := by simp
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hs] with x hx
        exact ENNReal.ofReal_le_ofReal (hbound x hx)
  have hr := ENNReal.toReal_mono (measure_ne_top _ _) h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha] using hr

lemma dyadicCell_inter_mass_le_of_density_upper (μ : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (hμ : (μ : Measure ℝ) = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (i k j ℓ : ℤ) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ x ∈ dyadicCell i k, f x ≤ b) :
    ((μ : Measure ℝ) (dyadicCell i k ∩ dyadicCell j ℓ)).toReal ≤ b * (2 : ℝ) ^ (-j) := by
  have hvol : volume (dyadicCell i k ∩ dyadicCell j ℓ) ≠ ∞ :=
    ne_top_of_le_ne_top (by rw [volume_dyadicCell]; exact ENNReal.ofReal_ne_top)
      (measure_mono inter_subset_right)
  have h := measure_le_of_density_upper μ f hμ
    ((measurableSet_dyadicCell i k).inter (measurableSet_dyadicCell j ℓ)) hb
    (fun x hx ↦ hbound x hx.1) hvol
  have hv := ENNReal.toReal_mono
    (show volume (dyadicCell j ℓ) ≠ ∞ by rw [volume_dyadicCell]; exact ENNReal.ofReal_ne_top)
    (measure_mono (show dyadicCell i k ∩ dyadicCell j ℓ ⊆ dyadicCell j ℓ from inter_subset_right))
  rw [volume_dyadicCell, ENNReal.toReal_ofReal (le_of_lt (zpow_pos (by norm_num) _))] at hv
  exact h.trans (mul_le_mul_of_nonneg_left hv hb)

end ExactOverlaps.Entropy
