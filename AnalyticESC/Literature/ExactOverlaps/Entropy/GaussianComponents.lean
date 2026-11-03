module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.GaussianDensity
public import AnalyticESC.Literature.ExactOverlaps.Entropy.DensityComponent
public import AnalyticESC.Literature.ExactOverlaps.Entropy.CentralCells

set_option maxSynthPendingDepth 3

/-!
# Quantitative entropy of Gaussian components

The Gaussian is used as its actual probability measure, with every dyadic
cell of positive mass when its variance is positive. The entropy estimate
is uniform over arbitrary means and a positive lower variance bound.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.GaussianComponents`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ExactOverlaps.Entropy

noncomputable def gaussianProbability (b : ℝ) (v : ℝ≥0) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal b v, inferInstance⟩

lemma gaussian_dyadicCell_positive (b : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (i k : ℤ) :
    k ∈ (dyadicLaw (gaussianProbability b v) i).support := by
  change (dyadicLaw (gaussianProbability b v) i) k ≠ 0
  rw [dyadicLaw_apply]
  intro h
  have hz := gaussianReal_absolutelyContinuous' b hv h
  rw [volume_dyadicCell, ENNReal.ofReal_eq_zero] at hz
  exact (not_le_of_gt (zpow_pos (by norm_num : (0 : ℝ) < 2) _)) hz

theorem gaussian_component_entropy_ge (b : ℝ) (v : ℝ≥0)
    {σ R : ℝ} (hσ : 0 < σ) (hv : σ ≤ (v : ℝ))
    (i : ℤ) (k : (dyadicLaw (gaussianProbability b v) i).support)
    {m : ℕ} (hm : 0 < m)
    (hcell : ∀ x ∈ dyadicCell i k, |x - b| ≤ R) :
    1 - (2 * R * (2 : ℝ) ^ (-i) / σ) / ((m : ℝ) * Real.log 2) ≤
      normalizedDyadicEntropy (rescaledComponent (gaussianProbability b v) i k)
        (rescaledComponent_hasBoundedSupport (gaussianProbability b v) i k) m := by
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
  have hlog : Real.log (B / A) = 2 * T := by
    rw [Real.log_div hB.ne' hA.ne']
    dsimp only [A, B]
    rw [Real.log_mul (Real.exp_pos _).ne' hpdf.ne',
      Real.log_mul (Real.exp_pos _).ne' hpdf.ne', Real.log_exp, Real.log_exp]
    ring
  have h := normalizedEntropy_component_ge_density_ratio (gaussianProbability b v)
    (gaussianPDFReal b v) hdensity i k hm hA hB hlower hupper
  rw [hlog] at h
  have he : 2 * T = 2 * R * (2 : ℝ) ^ (-i) / σ := by dsimp only [T]; ring
  rwa [he] at h

theorem gaussian_central_component_entropy_ge (b : ℝ) (v : ℝ≥0)
    {σ R : ℝ} (hσ : 0 < σ) (hv : σ ≤ (v : ℝ)) (i : ℕ)
    (k : (dyadicLaw (gaussianProbability b v) i).support) {m : ℕ} (hm : 0 < m)
    (hk : k.val ∈ Icc (dyadicQuantize i (b - R)) (dyadicQuantize i (b + R))) :
    1 - (2 * (R + 1) * (2 : ℝ) ^ (-(i : ℤ)) / σ) / ((m : ℝ) * Real.log 2) ≤
      normalizedDyadicEntropy (rescaledComponent (gaussianProbability b v) i k)
        (rescaledComponent_hasBoundedSupport (gaussianProbability b v) i k) m :=
  gaussian_component_entropy_ge b v hσ hv i k hm
    (fun _ hx ↦ abs_sub_center_le_add_one_of_label_bounds b R i k hk hx)

end ExactOverlaps.Entropy
