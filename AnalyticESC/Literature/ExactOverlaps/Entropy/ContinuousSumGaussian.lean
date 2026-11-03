module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.ContinuousSumMoments
public import AnalyticESC.Literature.ExactOverlaps.Entropy.WassersteinUniformity
public import AnalyticESC.Literature.ExactOverlaps.Entropy.WassersteinTranslation
public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.BoundedSumApproximation

set_option maxSynthPendingDepth 3

/-!
# Gaussian approximation of actual convolutions on bounded intervals

Each marginal may occupy a different interval. Only the common interval
length enters the error. The comparison mean and variance are the actual
sums of marginal means and variances, and the sum law is the genuine product
pushforward. No Gaussian approximation is left as a premise.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.ContinuousSumGaussian`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace ExactOverlaps.Entropy

open GaussianApproximation

theorem wasserstein1_continuousSumLaw_le {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) (a b : ι → ℝ)
    (hab : ∀ i, ∀ᵐ x ∂(ν i : Measure ℝ), x ∈ Icc (a i) (b i))
    {R : ℝ} (hR : ∀ i, b i - a i ≤ R) (v : ℝ≥0) (hv : 0 < (v : ℝ))
    (hvariance : (∑ i, variance (id : ℝ → ℝ) (ν i : Measure ℝ)) = (v : ℝ)) :
    wasserstein1 (continuousSumLaw ν)
      (gaussianProbability (∑ i, realLawMean (ν i)) v)
      (integrable_id_of_hasBoundedSupport _
        (continuousSumLaw_hasBoundedSupport ν (fun i ↦ ⟨a i, b i, hab i⟩)))
      (gaussianProbability_integrable_id _ v) ≤ gaussianApproximationConstant * R := by
  have hb (i : ι) : HasBoundedSupport (ν i) := ⟨a i, b i, hab i⟩
  have hX (i : ι) : MemLp (centeredProductCoordinate ν i) 3
      (continuousProductLaw ν : Measure (ι → ℝ)) := centeredProductCoordinate_memLp ν hb 3 i
  have hmean := integral_centeredProductCoordinate ν hb
  have hsecond : (∑ i, ∫ w, (centeredProductCoordinate ν i w) ^ 2
      ∂(continuousProductLaw ν : Measure (ι → ℝ))) = (v : ℝ) := by
    simp_rw [integral_sq_centeredProductCoordinate]
    exact hvariance
  have hbound (i : ι) : ∀ᵐ w ∂(continuousProductLaw ν : Measure (ι → ℝ)),
      |centeredProductCoordinate ν i w| ≤ R :=
    (abs_centeredProductCoordinate_le ν i (hab i)).mono (fun _ h ↦ h.trans (hR i))
  let ρ := (continuousSumLaw ν).map (fun x ↦ x - ∑ i, realLawMean (ν i))
  have hρ : (ρ : Measure ℝ) = (continuousProductLaw ν : Measure (ι → ℝ)).map
      (fun w ↦ ∑ i, centeredProductCoordinate ν i w) := continuousSumLaw_map_center ν
  have hclt := wasserstein1_sum_le_of_bounded (centeredProductCoordinate ν) hX
    (centeredProductCoordinate_independent ν) hmean v hv hsecond ρ hρ hbound
  exact (wasserstein1_le_centered_comparison (continuousSumLaw ν)
    (integrable_id_of_hasBoundedSupport _ (continuousSumLaw_hasBoundedSupport ν hb))
    (∑ i, realLawMean (ν i)) v
    (integrable_id_sum_law (centeredProductCoordinate ν) hX ρ hρ)).trans hclt

end ExactOverlaps.Entropy
