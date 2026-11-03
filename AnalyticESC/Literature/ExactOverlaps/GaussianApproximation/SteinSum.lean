module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.SteinShift

set_option maxSynthPendingDepth 3

/-!
# The Stein discrepancy of a finite independent sum

Every summand is centered and has a finite third absolute moment. No common
distribution, common sign or nonzero individual variance is required. The
normalization uses the sum of the actual second moments.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.SteinSum`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace ExactOverlaps.GaussianApproximation

lemma abs_sum_stein_error_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 3 μ) (hind : iIndepFun X μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    {g g' : ℝ → ℝ} {K : ℝ≥0} {A B : ℝ}
    (hd : ∀ x, HasDerivAt g (g' x) x) (hLip : LipschitzWith K g')
    (hg : ∀ x, |g x| ≤ A) (hg' : ∀ x, |g' x| ≤ B) :
    |(∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) * (∫ ω, g' (∑ i, X i ω) ∂μ) -
      (∫ ω, (∑ i, X i ω) * g (∑ i, X i ω) ∂μ)| ≤
      2 * (K : ℝ) * ∑ i, ∫ ω, |X i ω| ^ 3 ∂μ := by
  classical
  let S : Ω → ℝ := fun ω ↦ ∑ i, X i ω
  let Y : ι → Ω → ℝ := fun i ω ↦ ∑ j ∈ Finset.univ.erase i, X j ω
  have hXm (i : ι) : AEMeasurable (X i) μ := (hX i).aestronglyMeasurable.aemeasurable
  have hSm : AEMeasurable S μ := Finset.univ.aemeasurable_fun_sum (fun i _ ↦ hXm i)
  have hYm (i : ι) : AEMeasurable (Y i) μ :=
    (Finset.univ.erase i).aemeasurable_fun_sum (fun j _ ↦ hXm j)
  have hYS (i : ι) (ω : Ω) : Y i ω + X i ω = S ω :=
    Finset.sum_erase_add Finset.univ (fun j ↦ X j ω) (Finset.mem_univ i)
  have hiY (i : ι) : IndepFun (X i) (Y i) μ := by
    have h := (hind.indepFun_finsetSum_of_notMem₀ hXm
      (s := Finset.univ.erase i) (Finset.notMem_erase i Finset.univ)).symm
    have heq : (∑ j ∈ Finset.univ.erase i, X j) = Y i := by
      funext ω
      exact Finset.sum_apply ω (Finset.univ.erase i) X
    rwa [heq] at h
  have hgm : Measurable g :=
    (continuous_iff_continuousAt.mpr (fun x ↦ (hd x).continuousAt)).measurable
  have hgS : AEStronglyMeasurable (fun ω ↦ g (S ω)) μ :=
    (hgm.comp_aemeasurable hSm).aestronglyMeasurable
  have hi (i : ι) : Integrable (fun ω ↦ X i ω * g (S ω)) μ :=
    (integrable_of_memLp_three (hX i)).mul_bdd hgS
      (Filter.Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs] using hg (S ω)))
  have he (i : ι) : |(∫ ω, (X i ω) ^ 2 ∂μ) * (∫ ω, g' (S ω) ∂μ) -
      (∫ ω, X i ω * g (S ω) ∂μ)| ≤ 2 * (K : ℝ) * ∫ ω, |X i ω| ^ 3 ∂μ := by
    simpa only [hYS] using
      abs_summand_stein_error_le (hX i) (hYm i) (hiY i) (hmean i) hd hLip hg hg'
  have hsum : (∫ ω, S ω * g (S ω) ∂μ) = ∑ i, ∫ ω, X i ω * g (S ω) ∂μ := by
    calc
      _ = ∫ ω, ∑ i, X i ω * g (S ω) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω ↦ Finset.sum_mul _ _ _)
      _ = _ := integral_finsetSum _ (fun i _ ↦ hi i)
  change |(∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) * (∫ ω, g' (S ω) ∂μ) -
    (∫ ω, S ω * g (S ω) ∂μ)| ≤ _
  rw [hsum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(∫ ω, (X i ω) ^ 2 ∂μ) * (∫ ω, g' (S ω) ∂μ) -
        (∫ ω, X i ω * g (S ω) ∂μ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 2 * (K : ℝ) * ∫ ω, |X i ω| ^ 3 ∂μ :=
      Finset.sum_le_sum (fun i _ ↦ he i)
    _ = _ := (Finset.mul_sum _ _ _).symm

lemma abs_normalized_sum_stein_error_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 3 μ) (hind : iIndepFun X μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hnorm : (∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) = 1)
    {g g' : ℝ → ℝ} {K : ℝ≥0} {A B : ℝ}
    (hd : ∀ x, HasDerivAt g (g' x) x) (hLip : LipschitzWith K g')
    (hg : ∀ x, |g x| ≤ A) (hg' : ∀ x, |g' x| ≤ B) :
    |(∫ ω, g' (∑ i, X i ω) ∂μ) -
      (∫ ω, (∑ i, X i ω) * g (∑ i, X i ω) ∂μ)| ≤
      2 * (K : ℝ) * ∑ i, ∫ ω, |X i ω| ^ 3 ∂μ := by
  simpa only [hnorm, one_mul] using abs_sum_stein_error_le X hX hind hmean hd hLip hg hg'

end ExactOverlaps.GaussianApproximation
