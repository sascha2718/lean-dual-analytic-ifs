module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.DensityBounds
public import AnalyticESC.Literature.ExactOverlaps.Entropy.UniformMass

set_option maxSynthPendingDepth 3

/-!
# Density variation and component uniformity

If a density on a positive dyadic cell lies between a and b, then each
normalized m-cell has mass at most (b/a)/2^m. Its normalized entropy is at
least 1 - log(b/a)/(m log 2). No bounded-support condition is imposed on
the ambient law.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.DensityComponent`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.Entropy

theorem rawComponent_atom_le_density_ratio (μ : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (hμ : (μ : Measure ℝ) = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (i : ℤ) (k : (dyadicLaw μ i).support) (m : ℕ) (j : ℤ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ x ∈ dyadicCell i k, a ≤ f x)
    (hupper : ∀ x ∈ dyadicCell i k, f x ≤ b) :
    ((dyadicLaw (rawComponent μ i k) (i + m)) j).toReal ≤ (b / a) / (2 : ℝ) ^ m := by
  have hlo := measure_ge_of_density_lower μ f hμ (measurableSet_dyadicCell i k) ha.le hlower
  rw [volume_dyadicCell, ENNReal.toReal_ofReal (le_of_lt (zpow_pos (by norm_num) _))] at hlo
  have hup := dyadicCell_inter_mass_le_of_density_upper μ f hμ i k (i + m) j hb.le hupper
  have hc : 0 < ((μ : Measure ℝ) (dyadicCell i k)).toReal :=
    ENNReal.toReal_pos (dyadicCell_measure_ne_zero μ i k) (measure_ne_top _ _)
  have had : 0 < a * (2 : ℝ) ^ (-i) := mul_pos ha (zpow_pos (by norm_num) _)
  rw [dyadicLaw_apply, rawComponent_apply, ENNReal.toReal_mul, ENNReal.toReal_inv]
  calc
    _ = ((μ : Measure ℝ) (dyadicCell i k ∩ dyadicCell (i + m) j)).toReal /
        ((μ : Measure ℝ) (dyadicCell i k)).toReal := by ring
    _ ≤ (b * (2 : ℝ) ^ (-(i + (m : ℤ)))) /
        ((μ : Measure ℝ) (dyadicCell i k)).toReal := div_le_div_of_nonneg_right hup hc.le
    _ ≤ (b * (2 : ℝ) ^ (-(i + (m : ℤ)))) / (a * (2 : ℝ) ^ (-i)) :=
      div_le_div_of_nonneg_left (by positivity) had hlo
    _ = (b / a) / (2 : ℝ) ^ m := by
      rw [zpow_neg, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, zpow_neg]
      field_simp

theorem dyadicEntropy_component_ge_density_ratio (μ : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (hμ : (μ : Measure ℝ) = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (i : ℤ) (k : (dyadicLaw μ i).support) (m : ℕ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ x ∈ dyadicCell i k, a ≤ f x)
    (hupper : ∀ x ∈ dyadicCell i k, f x ≤ b) :
    (m : ℝ) * Real.log 2 - Real.log (b / a) ≤
      dyadicEntropy (rescaledComponent μ i k) (rescaledComponent_hasBoundedSupport μ i k) m := by
  rw [dyadicEntropy_rescaledComponent]
  have h := log_card_sub_log_factor_le_finiteEntropy
    (dyadicLaw (rawComponent μ i k) (i + m))
    (dyadicLaw_support_finite _ (rawComponent_hasBoundedSupport μ i k) _)
    (div_pos hb ha) (pow_pos (by norm_num) m)
    (fun j _ ↦ rawComponent_atom_le_density_ratio μ f hμ i k m j ha hb hlower hupper)
  simpa only [Real.log_pow, dyadicEntropy] using h

theorem normalizedEntropy_component_ge_density_ratio (μ : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (hμ : (μ : Measure ℝ) = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (i : ℤ) (k : (dyadicLaw μ i).support) {m : ℕ} (hm : 0 < m)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ x ∈ dyadicCell i k, a ≤ f x)
    (hupper : ∀ x ∈ dyadicCell i k, f x ≤ b) :
    1 - Real.log (b / a) / ((m : ℝ) * Real.log 2) ≤
      normalizedDyadicEntropy (rescaledComponent μ i k)
        (rescaledComponent_hasBoundedSupport μ i k) m := by
  have hd : 0 < (m : ℝ) * Real.log 2 :=
    mul_pos (Nat.cast_pos.mpr hm) (Real.log_pos (by norm_num))
  have h := div_le_div_of_nonneg_right
    (dyadicEntropy_component_ge_density_ratio μ f hμ i k m ha hb hlower hupper) hd.le
  simpa only [sub_div, div_self hd.ne', normalizedDyadicEntropy] using h

end ExactOverlaps.Entropy
