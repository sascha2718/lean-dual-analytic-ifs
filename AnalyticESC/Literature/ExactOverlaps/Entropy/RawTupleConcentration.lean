module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.RawTupleConvolution

set_option maxSynthPendingDepth 3

/-!
# The small-variance exceptional weight of raw component tuples

When the mean normalized component variance exceeds sigma, the actual iid
weight of tuples with normalized convolution variance at most n*sigma/2
is bounded by 4/(n*sigma^2), uniformly in the ambient law and level.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.RawTupleConcentration`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

lemma finiteDeviationMass_eq_sum_univ {α : Type*} [Fintype α] (p : PMF α)
    (hp : p.support.Finite) (f : α → ℝ) (c r : ℝ) :
    finiteDeviationMass p hp f c r =
      ∑ a, if r ≤ |f a - c| then (p a).toReal else 0 := by
  classical
  unfold finiteDeviationMass
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha
  have hz : p a = 0 := by simpa using ha
  simp [hz]

theorem scaledRawTuple_lowVariance_mass_le (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) {n : ℕ} (hn : 0 < n) {σ : ℝ}
    (hσ : 0 < σ) (hmean : σ < averageComponentVariance μ hμ i) :
    (letI : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
    ∑ w : FiniteTuple (dyadicLaw μ i).support n,
      if (n : ℝ) * (σ / 2) < variance (id : ℝ → ℝ)
          ((tupleConvolution (rawComponent μ i) n w).map (componentRescale i 0) : Measure ℝ)
      then 0 else ((iidTupleLaw (supportLaw (dyadicLaw μ i)) n) w).toReal) ≤
        4 / ((n : ℝ) * σ ^ 2) := by
  classical
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  have hbound := sampledComponentVarianceDeviationMass_le μ hμ i hn
    (show 0 < σ / 2 by positivity)
  unfold sampledComponentVarianceDeviationMass at hbound
  rw [finiteDeviationMass_eq_sum_univ] at hbound
  have hsum : (∑ w : FiniteTuple (dyadicLaw μ i).support n,
      if (n : ℝ) * (σ / 2) < variance (id : ℝ → ℝ)
          ((tupleConvolution (rawComponent μ i) n w).map (componentRescale i 0) : Measure ℝ)
      then 0 else ((iidTupleLaw (supportLaw (dyadicLaw μ i)) n) w).toReal) ≤
      ∑ w : FiniteTuple (dyadicLaw μ i).support n,
        if (n : ℝ) * (σ / 2) ≤ |tupleSum (componentVariance μ i) n w -
          (n : ℝ) * averageComponentVariance μ hμ i|
        then ((iidTupleLaw (supportLaw (dyadicLaw μ i)) n) w).toReal else 0 := by
    apply Finset.sum_le_sum
    intro w _
    by_cases hv : (n : ℝ) * (σ / 2) < variance (id : ℝ → ℝ)
        ((tupleConvolution (rawComponent μ i) n w).map (componentRescale i 0) : Measure ℝ)
    · simp only [hv, ite_true]
      split_ifs <;> positivity
    · have hdev : (n : ℝ) * (σ / 2) ≤ |tupleSum (componentVariance μ i) n w -
          (n : ℝ) * averageComponentVariance μ hμ i| := by
        by_contra h
        exact hv (scaled_rawTuple_variance_large_of_small_deviation μ hμ i hn w hmean
          (lt_of_not_ge h))
      simp only [hv, ite_false, hdev, ite_true, le_refl]
  have he : 1 / ((n : ℝ) * (σ / 2) ^ 2) = 4 / ((n : ℝ) * σ ^ 2) := by
    ring
  exact hsum.trans (he ▸ hbound)

end ExactOverlaps.Entropy
