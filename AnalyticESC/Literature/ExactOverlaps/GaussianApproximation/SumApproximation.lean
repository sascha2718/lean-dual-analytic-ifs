module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.NormalizedWasserstein
public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.NormalizationMoments
public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.GaussianScaling

set_option maxSynthPendingDepth 3

/-!
# Gaussian approximation at every positive total variance

The normalized non-identical independent-sum theorem is transported through
the actual scalar maps. The result has the third-moment sum divided by the
total variance, with one universal constant.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.SumApproximation`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace ExactOverlaps.GaussianApproximation

theorem wasserstein1_sum_le_of_secondMoment_sq {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 3 μ) (hind : iIndepFun X μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0) {s : ℝ} (hs : 0 < s)
    (hvariance : (∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) = s ^ 2)
    (ν : ProbabilityMeasure ℝ)
    (hν : (ν : Measure ℝ) = μ.map (fun ω ↦ ∑ i, X i ω)) :
    wasserstein1 ν (centeredGaussian ⟨s ^ 2, sq_nonneg s⟩)
      (integrable_id_sum_law X hX ν hν) (integrable_id_centeredGaussian _) ≤
        gaussianApproximationConstant * (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) / s ^ 2 := by
  let Y := fun i ω ↦ X i ω / s
  have hY (i : ι) : MemLp (Y i) 3 μ := memLp_three_div_const (hX i) s
  have hiY : iIndepFun Y μ := independent_div_const X hind s
  have hmY (i : ι) : (∫ ω, Y i ω ∂μ) = 0 := integral_div_const_eq_zero (hmean i) s
  have hvY : (∑ i, ∫ ω, (Y i ω) ^ 2 ∂μ) = 1 :=
    sum_secondMoment_div_eq_one X hs.ne' hvariance
  have hSY : Integrable (fun ω ↦ ∑ i, Y i ω) μ :=
    integrable_finsetSum _ (fun i _ ↦ integrable_of_memLp_three (hY i))
  let ρ : ProbabilityMeasure ℝ := ⟨μ.map (fun ω ↦ ∑ i, Y i ω), inferInstance⟩
  have hρ : (ρ : Measure ℝ) = μ.map (fun ω ↦ ∑ i, Y i ω) := rfl
  have hclt := wasserstein1_normalized_sum_le Y hY hiY hmY hvY ρ hρ
  have htransport := wasserstein1_map_mul_le ρ standardGaussian
    (integrable_id_sum_law Y hY ρ hρ) integrable_id_standardGaussian hs
  have hreconstruct : ρ.map (fun x ↦ s * x) = ν := by
    apply ProbabilityMeasure.toMeasure_injective
    change (μ.map (fun ω ↦ ∑ i, Y i ω)).map (fun x ↦ s * x) = (ν : Measure ℝ)
    rw [hν]
    have hm : Measurable (fun x : ℝ ↦ s * x) := measurable_const.mul measurable_id
    rw [hm.aemeasurable.map_map_of_aemeasurable hSY.aemeasurable]
    congr 1
    funext ω
    change s * (∑ i, X i ω / s) = ∑ i, X i ω
    rw [← Finset.sum_div]
    field_simp [hs.ne']
  have ht : (∑ i, ∫ ω, |Y i ω| ^ 3 ∂μ) =
      (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) / s ^ 3 := sum_thirdMoment_div X hs
  have hresult := htransport.trans (mul_le_mul_of_nonneg_left hclt hs.le)
  unfold wasserstein1 at hresult
  rw [hreconstruct, standardGaussian_map_mul, ht] at hresult
  calc
    _ ≤ s * (gaussianApproximationConstant *
        ((∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) / s ^ 3)) := hresult
    _ = _ := by field_simp [hs.ne']

theorem wasserstein1_sum_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 3 μ) (hind : iIndepFun X μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0) (v : ℝ≥0) (hv : 0 < (v : ℝ))
    (hvariance : (∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) = (v : ℝ))
    (ν : ProbabilityMeasure ℝ)
    (hν : (ν : Measure ℝ) = μ.map (fun ω ↦ ∑ i, X i ω)) :
    wasserstein1 ν (centeredGaussian v)
      (integrable_id_sum_law X hX ν hν) (integrable_id_centeredGaussian v) ≤
        gaussianApproximationConstant * (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) / (v : ℝ) := by
  have hs := Real.sqrt_pos.mpr hv
  have hs2 := Real.sq_sqrt v.coe_nonneg
  have h := wasserstein1_sum_le_of_secondMoment_sq X hX hind hmean hs
    (hvariance.trans hs2.symm) ν hν
  have he : (⟨(Real.sqrt (v : ℝ)) ^ 2, sq_nonneg _⟩ : ℝ≥0) = v := NNReal.eq hs2
  unfold wasserstein1 at h ⊢
  rw [he, hs2] at h
  exact h

end ExactOverlaps.GaussianApproximation
