module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.GaussianCellMass

set_option maxSynthPendingDepth 3

/-!
# Fine-cell mass bounds for Gaussian components

These quantitative atom bounds retain more information than their entropy
consequence and can be transferred under uniform interval-mass errors.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.GaussianComponentMass`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ExactOverlaps.Entropy

theorem gaussian_rawComponent_atom_le (b : ℝ) (v : ℝ≥0)
    {σ R : ℝ} (hσ : 0 < σ) (hv : σ ≤ (v : ℝ))
    (i : ℤ) (k : (dyadicLaw (gaussianProbability b v) i).support) (m : ℕ) (j : ℤ)
    (hcell : ∀ x ∈ dyadicCell i k, |x - b| ≤ R) :
    ((dyadicLaw (rawComponent (gaussianProbability b v) i k) (i + m)) j).toReal ≤
      Real.exp (2 * R * (2 : ℝ) ^ (-i) / σ) / (2 : ℝ) ^ m := by
  have hvpos : 0 < (v : ℝ) := hσ.trans_le hv
  have hv0 : v ≠ 0 := by exact_mod_cast hvpos.ne'
  let y : ℝ := (k : ℝ) / (2 : ℝ) ^ i
  have hycell : y ∈ dyadicCell i k := dyadicCell_left_endpoint_mem i k
  have hy := hcell y hycell
  let T : ℝ := R * (2 : ℝ) ^ (-i) / σ
  let A : ℝ := Real.exp (-T) * gaussianPDFReal b v y
  let B : ℝ := Real.exp T * gaussianPDFReal b v y
  have hpdf := gaussianPDFReal_pos b v y hv0
  have hA : 0 < A := mul_pos (Real.exp_pos _) hpdf
  have hB : 0 < B := mul_pos (Real.exp_pos _) hpdf
  have hdensity : (gaussianProbability b v : Measure ℝ) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (gaussianPDFReal b v x)) :=
    gaussianReal_of_var_ne_zero b hv0
  have hlower (x : ℝ) (hx : x ∈ dyadicCell i k) : A ≤ gaussianPDFReal b v x :=
    gaussianPDFReal_exp_neg_mul_le b v hσ hv (hcell x hx) hy
      (abs_sub_le_of_mem_dyadicCell hx hycell)
  have hupper (x : ℝ) (hx : x ∈ dyadicCell i k) : gaussianPDFReal b v x ≤ B :=
    gaussianPDFReal_le_exp_mul b v hσ hv (hcell x hx) hy
      (abs_sub_le_of_mem_dyadicCell hx hycell)
  have hquot : B / A = Real.exp (2 * R * (2 : ℝ) ^ (-i) / σ) := by
    dsimp only [A, B]
    rw [mul_div_mul_right _ _ hpdf.ne', ← Real.exp_sub]
    congr 1
    dsimp only [T]
    ring
  have h := rawComponent_atom_le_density_ratio (gaussianProbability b v) (gaussianPDFReal b v)
    hdensity i k m j hA hB hlower hupper
  rwa [hquot] at h

theorem gaussian_central_inter_mass_le (b : ℝ) (v : ℝ≥0)
    {σ R : ℝ} (hσ : 0 < σ) (hv : σ ≤ (v : ℝ)) (i : ℕ) (k : ℤ) (m : ℕ) (j : ℤ)
    (hk : k ∈ Icc (dyadicQuantize i (b - R)) (dyadicQuantize i (b + R))) :
    (gaussianReal b v (dyadicCell i k ∩ dyadicCell (i + m) j)).toReal ≤
      (Real.exp (2 * (R + 1) * (2 : ℝ) ^ (-(i : ℤ)) / σ) / (2 : ℝ) ^ m) *
        (gaussianReal b v (dyadicCell i k)).toReal := by
  have hvpos : 0 < (v : ℝ) := hσ.trans_le hv
  have hv0 : v ≠ 0 := by exact_mod_cast hvpos.ne'
  let k' : (dyadicLaw (gaussianProbability b v) i).support :=
    ⟨k, gaussian_dyadicCell_positive b v hv0 i k⟩
  have h := gaussian_rawComponent_atom_le b v hσ hv i k' m j
    (fun x hx ↦ abs_sub_center_le_add_one_of_label_bounds b R i k hk hx)
  rw [dyadicLaw_apply, rawComponent_apply, ENNReal.toReal_mul, ENNReal.toReal_inv,
    mul_comm, ← div_eq_mul_inv] at h
  have hmass : 0 < (gaussianReal b v (dyadicCell i k)).toReal :=
    ENNReal.toReal_pos (dyadicCell_measure_ne_zero (gaussianProbability b v) i k')
      (measure_ne_top _ _)
  exact (div_le_iff₀ hmass).1 h

end ExactOverlaps.Entropy
