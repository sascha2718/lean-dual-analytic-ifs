module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.TupleConvolution
public import AnalyticESC.Literature.ExactOverlaps.Entropy.ComponentMixture
public import AnalyticESC.Literature.ExactOverlaps.Entropy.ComponentVarianceSampling

set_option maxSynthPendingDepth 3

/-!
# Raw component tuples reconstruct the repeated convolution

The original convolution power is an exact mixture over the independent
cell labels. Multiplication by the coarse dyadic scale makes its tuple
variance precisely the sum of the normalized component variances.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.RawTupleConvolution`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

theorem realConvolutionPower_eq_rawTuple_mixture (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (n : ℕ) :
    (realConvolutionPower μ n : Measure ℝ) =
      (letI : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
      ∑ w : FiniteTuple (dyadicLaw μ i).support n,
        (iidTupleLaw (supportLaw (dyadicLaw μ i)) n) w •
          (tupleConvolution (rawComponent μ i) n w : Measure ℝ)) := by
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  exact realConvolutionPower_eq_tuple_mixture (supportLaw (dyadicLaw μ i))
    (rawComponent μ i) μ (measure_eq_rawComponent_mixture μ hμ i) n

lemma rawTupleVariance_scaled_eq_sum (μ : ProbabilityMeasure ℝ) (i : ℤ)
    (n : ℕ) (w : FiniteTuple (dyadicLaw μ i).support n) :
    ((2 : ℝ) ^ i) ^ 2 * variance (id : ℝ → ℝ)
      (tupleConvolution (rawComponent μ i) n w : Measure ℝ) =
        tupleSum (componentVariance μ i) n w := by
  induction n with
  | zero =>
    change ((2 : ℝ) ^ i) ^ 2 * variance (id : ℝ → ℝ) (Measure.dirac 0) = 0
    rw [variance_dirac, mul_zero]
  | succ n ih =>
    change ((2 : ℝ) ^ i) ^ 2 * variance (id : ℝ → ℝ)
      (realConvolution (rawComponent μ i w.1) (tupleConvolution (rawComponent μ i) n w.2) :
        Measure ℝ) = componentVariance μ i w.1 + tupleSum (componentVariance μ i) n w.2
    rw [variance_realConvolution _ _ (rawComponent_hasBoundedSupport μ i w.1)
      (tupleConvolution_hasBoundedSupport _ (rawComponent_hasBoundedSupport μ i) n w.2),
      mul_add, ih w.2]
    have h := variance_map_componentRescale (rawComponent μ i w.1) i w.1
    exact congrArg (fun t ↦ t + tupleSum (componentVariance μ i) n w.2) h.symm

theorem variance_scaled_rawTupleConvolution (μ : ProbabilityMeasure ℝ) (i : ℤ)
    (n : ℕ) (w : FiniteTuple (dyadicLaw μ i).support n) :
    variance (id : ℝ → ℝ)
      ((tupleConvolution (rawComponent μ i) n w).map (componentRescale i 0) : Measure ℝ) =
        tupleSum (componentVariance μ i) n w := by
  rw [variance_map_componentRescale, rawTupleVariance_scaled_eq_sum]

theorem scaled_rawTuple_variance_large_of_small_deviation (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) {n : ℕ} (hn : 0 < n)
    (w : FiniteTuple (dyadicLaw μ i).support n) {σ : ℝ}
    (hmean : σ < averageComponentVariance μ hμ i)
    (hgood : |tupleSum (componentVariance μ i) n w -
      (n : ℝ) * averageComponentVariance μ hμ i| < (n : ℝ) * (σ / 2)) :
    (n : ℝ) * (σ / 2) < variance (id : ℝ → ℝ)
      ((tupleConvolution (rawComponent μ i) n w).map (componentRescale i 0) : Measure ℝ) := by
  rw [variance_scaled_rawTupleConvolution]
  have hmean' := mul_lt_mul_of_pos_left hmean (Nat.cast_pos.mpr hn)
  have hdev := (abs_lt.mp hgood).1
  nlinarith

end ExactOverlaps.Entropy
