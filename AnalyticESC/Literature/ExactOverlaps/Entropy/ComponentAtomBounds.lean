module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.UniformMass
public import AnalyticESC.Literature.ExactOverlaps.Entropy.Components

set_option maxSynthPendingDepth 3

/-!
# Component entropy from conditional atom bounds

Uniform bounds on the finer atoms of a positive coarse-cell restriction give
entropy bounds on its actual affine-normalized component.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.ComponentAtomBounds`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ExactOverlaps.Entropy

theorem normalizedEntropy_component_ge_of_raw_atom_bound (μ : ProbabilityMeasure ℝ)
    (i : ℤ) (k : (dyadicLaw μ i).support) {m : ℕ} (hm : 0 < m)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ j : ℤ,
      ((dyadicLaw (rawComponent μ i k) (i + m)) j).toReal ≤ C / (2 : ℝ) ^ m) :
    1 - Real.log C / ((m : ℝ) * Real.log 2) ≤
      normalizedDyadicEntropy (rescaledComponent μ i k)
        (rescaledComponent_hasBoundedSupport μ i k) m := by
  have h := log_card_sub_log_factor_le_finiteEntropy
    (dyadicLaw (rawComponent μ i k) (i + m))
    (dyadicLaw_support_finite _ (rawComponent_hasBoundedSupport μ i k) _)
    hC (pow_pos (by norm_num) m) (fun j _ ↦ hbound j)
  have h' : (m : ℝ) * Real.log 2 - Real.log C ≤
      dyadicEntropy (rescaledComponent μ i k)
        (rescaledComponent_hasBoundedSupport μ i k) m := by
    rw [dyadicEntropy_rescaledComponent]
    simpa only [Real.log_pow, dyadicEntropy] using h
  have hd : 0 < (m : ℝ) * Real.log 2 :=
    mul_pos (Nat.cast_pos.mpr hm) (Real.log_pos (by norm_num))
  have h'' := div_le_div_of_nonneg_right h' hd.le
  simpa only [sub_div, div_self hd.ne', normalizedDyadicEntropy] using h''

end ExactOverlaps.Entropy
