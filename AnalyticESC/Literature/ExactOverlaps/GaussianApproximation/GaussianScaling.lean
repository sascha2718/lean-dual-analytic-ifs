module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.GaussianCentering
public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.ScalarTransport

set_option maxSynthPendingDepth 3

/-!
# Scaling the actual standard Gaussian

The comparison laws are Mathlib's Gaussian probability measures. Multiplying
the standard Gaussian by s gives exactly the centered Gaussian of variance
s squared, including the degenerate case s=0.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.GaussianScaling`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ExactOverlaps.GaussianApproximation

def centeredGaussian (v : ℝ≥0) : ProbabilityMeasure ℝ := ⟨gaussianReal 0 v, inferInstance⟩

lemma integrable_id_centeredGaussian (v : ℝ≥0) :
    Integrable (fun x : ℝ ↦ x) (centeredGaussian v : Measure ℝ) :=
  (memLp_id_gaussianReal (μ := 0) (v := v) 1).integrable (by norm_num)

lemma standardGaussian_map_mul (s : ℝ) :
    standardGaussian.map (fun x ↦ s * x) = centeredGaussian ⟨s ^ 2, sq_nonneg s⟩ := by
  apply ProbabilityMeasure.toMeasure_injective
  change (gaussianReal 0 1).map (fun x ↦ s * x) = gaussianReal 0 ⟨s ^ 2, sq_nonneg s⟩
  rw [gaussianReal_map_const_mul, mul_zero, mul_one]
  congr 1

lemma standardGaussian_map_sqrt (v : ℝ≥0) :
    standardGaussian.map (fun x ↦ Real.sqrt (v : ℝ) * x) = centeredGaussian v := by
  rw [standardGaussian_map_mul]
  congr 1
  apply NNReal.eq
  exact Real.sq_sqrt v.coe_nonneg

end ExactOverlaps.GaussianApproximation
