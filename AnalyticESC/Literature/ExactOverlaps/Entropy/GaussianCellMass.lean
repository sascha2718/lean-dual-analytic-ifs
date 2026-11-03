module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.GaussianComponents

set_option maxSynthPendingDepth 3

/-!
# A uniform lower bound for central Gaussian cell masses

The positive lower bound depends on the variance interval and the central
radius, and is independent of the mean. It prevents division by arbitrarily
small cell masses when transferring local uniformity to nearby laws.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.GaussianCellMass`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ExactOverlaps.Entropy

noncomputable def gaussianDensityFloor (σ V R : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * V))⁻¹ * Real.exp (-R ^ 2 / (2 * σ))

lemma gaussianDensityFloor_pos {σ V R : ℝ} (hV : 0 < V) :
    0 < gaussianDensityFloor σ V R := by
  unfold gaussianDensityFloor
  positivity

theorem gaussianDensityFloor_le_pdf (b : ℝ) (v : ℝ≥0) {σ V R x : ℝ}
    (hσ : 0 < σ) (hvσ : σ ≤ (v : ℝ)) (hvV : (v : ℝ) ≤ V)
    (hR : 0 ≤ R) (hx : |x - b| ≤ R) :
    gaussianDensityFloor σ V R ≤ gaussianPDFReal b v x := by
  have hv : 0 < (v : ℝ) := hσ.trans_le hvσ
  have hsquare : (x - b) ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).2 hx
  have hdiv : (x - b) ^ 2 / (2 * (v : ℝ)) ≤ R ^ 2 / (2 * σ) := by
    calc
      _ ≤ R ^ 2 / (2 * (v : ℝ)) := div_le_div_of_nonneg_right hsquare (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (by linarith)
  have hexp : Real.exp (-R ^ 2 / (2 * σ)) ≤ Real.exp (-(x - b) ^ 2 / (2 * v)) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg hdiv
  have hsqrt : Real.sqrt (2 * Real.pi * (v : ℝ)) ≤ Real.sqrt (2 * Real.pi * V) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hvV (by positivity))
  have hpref : (Real.sqrt (2 * Real.pi * V))⁻¹ ≤
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le
      (Real.sqrt_pos.mpr (by positivity)) hsqrt
  exact mul_le_mul hpref hexp (Real.exp_pos _).le (by positivity)

theorem gaussian_central_cell_mass_ge (b : ℝ) (v : ℝ≥0) {σ V R : ℝ}
    (hσ : 0 < σ) (hvσ : σ ≤ (v : ℝ)) (hvV : (v : ℝ) ≤ V)
    (hR : 0 ≤ R) (i : ℕ) (k : ℤ)
    (hk : k ∈ Icc (dyadicQuantize i (b - R)) (dyadicQuantize i (b + R))) :
    gaussianDensityFloor σ V (R + 1) * (2 : ℝ) ^ (-(i : ℤ)) ≤
      ((dyadicLaw (gaussianProbability b v) i) k).toReal := by
  have hvpos : 0 < (v : ℝ) := hσ.trans_le hvσ
  have hv0 : v ≠ 0 := by exact_mod_cast hvpos.ne'
  have hV : 0 < V := hvpos.trans_le hvV
  have hdensity : (gaussianProbability b v : Measure ℝ) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (gaussianPDFReal b v x)) :=
    gaussianReal_of_var_ne_zero b hv0
  have hb := measure_ge_of_density_lower (gaussianProbability b v) (gaussianPDFReal b v)
    hdensity (measurableSet_dyadicCell i k) (gaussianDensityFloor_pos hV).le
    (fun x hx ↦ gaussianDensityFloor_le_pdf b v hσ hvσ hvV (by linarith)
      (abs_sub_center_le_add_one_of_label_bounds b R i k hk hx))
  rw [volume_dyadicCell, ENNReal.toReal_ofReal (le_of_lt (zpow_pos (by norm_num) _))] at hb
  simpa only [dyadicLaw_apply] using hb

end ExactOverlaps.Entropy
