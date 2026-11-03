module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.GaussianComponents
public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.HalfOpenCDF

set_option maxSynthPendingDepth 3

/-!
# Uniform Lipschitz constants for Gaussian distribution functions

The density bound depends only on a positive lower variance bound and is
independent of the mean. It supplies the regularity needed to turn a genuine
dual Wasserstein bound into half-open interval probability estimates.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.GaussianCDF`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ExactOverlaps.Entropy

lemma lipschitz_cdf_of_density_upper (μ : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (hμ : (μ : Measure ℝ) = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    {L : ℝ≥0} (hbound : ∀ x, f x ≤ L) :
    LipschitzWith L (cdf (μ : Measure ℝ)) := by
  have hinc (a b : ℝ) (hab : a ≤ b) :
      cdf (μ : Measure ℝ) b - cdf (μ : Measure ℝ) a ≤ (L : ℝ) * (b - a) := by
    have hs : Ioc a b = Iic b \ Iic a := by
      ext x
      simp only [mem_Ioc, mem_sdiff, mem_Iic, not_le]
      tauto
    have hm : ((μ : Measure ℝ) (Ioc a b)).toReal =
        cdf (μ : Measure ℝ) b - cdf (μ : Measure ℝ) a := by
      rw [cdf_eq_real, cdf_eq_real, hs]
      exact measureReal_sdiff (Iic_subset_Iic.mpr hab) measurableSet_Iic
    have hu := measure_le_of_density_upper μ f hμ (s := Ioc a b) measurableSet_Ioc L.coe_nonneg
      (fun x _ ↦ hbound x) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    rw [hm, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] at hu
    exact hu
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [Real.dist_eq]
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr ((monotone_cdf _) hab)),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    have h := hinc a b hab
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr ((monotone_cdf _) hba)),
      abs_of_nonneg (sub_nonneg.mpr hba)]
    exact hinc b a hba

lemma gaussianPDFReal_le_variance_bound (b : ℝ) (v : ℝ≥0) {σ : ℝ}
    (hσ : 0 < σ) (hv : σ ≤ (v : ℝ)) (x : ℝ) :
    gaussianPDFReal b v x ≤ (Real.sqrt (2 * Real.pi * σ))⁻¹ := by
  have hexp : Real.exp (-(x - b) ^ 2 / (2 * v)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
      (by positivity))
  have hpref : (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ ≤
      (Real.sqrt (2 * Real.pi * σ))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le
      (Real.sqrt_pos.mpr (by positivity))
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hv (by positivity)))
  unfold gaussianPDFReal
  exact (mul_le_of_le_one_right (by positivity) hexp).trans hpref

theorem gaussian_cdf_lipschitz (b : ℝ) (v : ℝ≥0) {σ : ℝ}
    (hσ : 0 < σ) (hv : σ ≤ (v : ℝ)) :
    LipschitzWith ⟨(Real.sqrt (2 * Real.pi * σ))⁻¹, by positivity⟩ (cdf (gaussianReal b v)) := by
  have hvpos : 0 < (v : ℝ) := hσ.trans_le hv
  have hv0 : v ≠ 0 := by exact_mod_cast hvpos.ne'
  exact lipschitz_cdf_of_density_upper (gaussianProbability b v) (gaussianPDFReal b v)
    (gaussianReal_of_var_ne_zero b hv0) (gaussianPDFReal_le_variance_bound b v hσ hv)

lemma gaussianProbability_integrable_id (b : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ ↦ x) (gaussianProbability b v : Measure ℝ) :=
  (memLp_id_gaussianReal (μ := b) (v := v) 1).integrable (by norm_num)

end ExactOverlaps.Entropy
