module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.RawTupleConcentration
public import AnalyticESC.Literature.ExactOverlaps.Entropy.MixtureGoodComponents

set_option maxSynthPendingDepth 3

/-!
# Combining tuple uniformity with component-variance concentration

This is the finite-mixture step in repeated-convolution uniformization.
It leaves the uniformity of each sufficiently variable tuple as an explicit
hypothesis, to be supplied by the separate Gaussian approximation theorem.
All decomposition, variance sampling and exceptional-weight estimates are
proved here for the actual measures and sampling laws.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.RepeatedComponentUniformity`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

theorem convolutionPower_lowerTail_le_of_tuple_uniformity (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i j : ℤ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {σ δ η : ℝ} (hσ : 0 < σ) (hmean : σ < averageComponentVariance μ hμ i)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hgood : ∀ w : FiniteTuple (dyadicLaw μ i).support n,
      (n : ℝ) * (σ / 2) < variance (id : ℝ → ℝ)
        ((tupleConvolution (rawComponent μ i) n w).map (componentRescale i 0) : Measure ℝ) →
      componentEntropyLowerTailMass (tupleConvolution (rawComponent μ i) n w)
        (tupleConvolution_hasBoundedSupport _ (rawComponent_hasBoundedSupport μ i) n w)
        j m δ ≤ η) (a : ℝ) :
    a * componentEntropyLowerTailMass (realConvolutionPower μ n)
      (realConvolutionPower_hasBoundedSupport μ hμ n) j m a ≤
        δ + η + 4 / ((n : ℝ) * σ ^ 2) := by
  classical
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  have h := mixture_component_lowerTail_le_with_exception
    (iidTupleLaw (supportLaw (dyadicLaw μ i)) n)
    (tupleConvolution (rawComponent μ i) n)
    (tupleConvolution_hasBoundedSupport _ (rawComponent_hasBoundedSupport μ i) n)
    (realConvolutionPower μ n) (realConvolutionPower_hasBoundedSupport μ hμ n)
    (realConvolutionPower_eq_rawTuple_mixture μ hμ i n) j hm hδ hη
    (fun w ↦ (n : ℝ) * (σ / 2) < variance (id : ℝ → ℝ)
      ((tupleConvolution (rawComponent μ i) n w).map (componentRescale i 0) : Measure ℝ))
    hgood a
  have hmass := scaledRawTuple_lowVariance_mass_le μ hμ i hn hσ hmean
  linarith

theorem convolutionPower_uniformity_of_tuple_uniformity (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i j : ℤ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) (hmean : σ < averageComponentVariance μ hμ i)
    (hsize : 16 < (n : ℝ) * σ ^ 2 * ε ^ 2)
    (hgood : ∀ w : FiniteTuple (dyadicLaw μ i).support n,
      (n : ℝ) * (σ / 2) < variance (id : ℝ → ℝ)
        ((tupleConvolution (rawComponent μ i) n w).map (componentRescale i 0) : Measure ℝ) →
      componentEntropyLowerTailMass (tupleConvolution (rawComponent μ i) n w)
        (tupleConvolution_hasBoundedSupport _ (rawComponent_hasBoundedSupport μ i) n w)
        j m (ε ^ 2 / 4) ≤ ε ^ 2 / 4) :
    componentEntropyLowerTailMass (realConvolutionPower μ n)
      (realConvolutionPower_hasBoundedSupport μ hμ n) j m ε < ε := by
  have h := convolutionPower_lowerTail_le_of_tuple_uniformity μ hμ i j hn hm
    hσ hmean (show 0 ≤ ε ^ 2 / 4 by positivity) (show 0 ≤ ε ^ 2 / 4 by positivity) hgood ε
  have hden : 0 < (n : ℝ) * σ ^ 2 := mul_pos (Nat.cast_pos.mpr hn) (sq_pos_of_pos hσ)
  have hsmall : 4 / ((n : ℝ) * σ ^ 2) < ε ^ 2 / 4 := by
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hprod : ε * componentEntropyLowerTailMass (realConvolutionPower μ n)
      (realConvolutionPower_hasBoundedSupport μ hμ n) j m ε < ε * ε := by
    nlinarith [sq_pos_of_pos hε]
  exact (mul_lt_mul_iff_right₀ hε).1 hprod

end ExactOverlaps.Entropy
