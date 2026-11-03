module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.RealConvolutionVariance
public import AnalyticESC.Literature.ExactOverlaps.Entropy.FiniteProductConcentration

set_option maxSynthPendingDepth 3

/-!
# Uniform concentration of sampled component variances

The sampling law is the actual dyadic cell-mass law restricted to its
positive labels. Each observable is the genuine variance of the normalized
component. The explicit deviation estimate is uniform in the ambient law
and in its dyadic level.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.ComponentVarianceSampling`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory
open ExactOverlaps.FiniteProbability
open scoped ENNReal

namespace ExactOverlaps.Entropy

lemma componentIndexLaw_support_finite (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) : (supportLaw (dyadicLaw μ i)).support.Finite := by
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  exact Set.toFinite _

noncomputable def averageComponentVariance (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) : ℝ :=
  expectation (supportLaw (dyadicLaw μ i)) (componentIndexLaw_support_finite μ hμ i)
    (componentVariance μ i)

lemma averageComponentVariance_nonneg (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) : 0 ≤ averageComponentVariance μ hμ i :=
  expectation_nonneg _ _ (fun k _ ↦ componentVariance_nonneg μ i k)

lemma averageComponentVariance_le_quarter (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) : averageComponentVariance μ hμ i ≤ 1 / 4 := by
  unfold averageComponentVariance
  rw [← expectation_const (supportLaw (dyadicLaw μ i))
    (componentIndexLaw_support_finite μ hμ i) (1 / 4)]
  exact expectation_mono _ _ (fun k _ ↦ componentVariance_le_quarter μ i k)

noncomputable def sampledComponentVarianceDeviationMass (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (n : ℕ) (ε : ℝ) : ℝ :=
  finiteDeviationMass (iidTupleLaw (supportLaw (dyadicLaw μ i)) n)
    (iidTupleLaw_support_finite _ (componentIndexLaw_support_finite μ hμ i) n)
    (tupleSum (componentVariance μ i) n) ((n : ℝ) * averageComponentVariance μ hμ i)
    ((n : ℝ) * ε)

theorem sampledComponentVarianceDeviationMass_le (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    sampledComponentVarianceDeviationMass μ hμ i n ε ≤ 1 / ((n : ℝ) * ε ^ 2) := by
  apply iidTupleSum_deviation_le_of_unit_bounds _ _ _ _ hn hε
  intro k _
  exact ⟨componentVariance_nonneg μ i k,
    (componentVariance_le_quarter μ i k).trans (by norm_num)⟩

end ExactOverlaps.Entropy
