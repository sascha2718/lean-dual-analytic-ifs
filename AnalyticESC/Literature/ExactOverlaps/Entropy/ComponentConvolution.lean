module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.ComponentMixture
public import AnalyticESC.Literature.ExactOverlaps.Entropy.ConvolutionMixture
public import AnalyticESC.Literature.ExactOverlaps.Entropy.RescaleConvolution
public import AnalyticESC.Literature.ExactOverlaps.Entropy.ConvolutionBounds
public import AnalyticESC.Literature.ExactOverlaps.Entropy.Atomicity

set_option maxSynthPendingDepth 3

/-!
# The local convolution entropy bound

The original convolution is a finite mixture of convolutions of raw dyadic
components. Conditional entropy concavity compares their fine-scale entropy
increments. Each raw component convolution has coarse entropy at most log 2,
and affine normalization preserves its fine entropy exactly.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.ComponentConvolution`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace ExactOverlaps.Entropy

lemma dyadicEntropy_rawComponent_convolution_coarse_le (μ ν : ProbabilityMeasure ℝ) (i : ℤ)
    (j : (dyadicLaw μ i).support) (k : (dyadicLaw ν i).support) :
    dyadicEntropy (realConvolution (rawComponent μ i j) (rawComponent ν i k))
      (realConvolution_hasBoundedSupport _ _ (rawComponent_hasBoundedSupport μ i j)
        (rawComponent_hasBoundedSupport ν i k)) i ≤ Real.log 2 := by
  have h := dyadicEntropy_convolution_le_add_log_two
    (rescaledComponent μ i j) (rescaledComponent ν i k)
    (rescaledComponent_hasBoundedSupport μ i j) (rescaledComponent_hasBoundedSupport ν i k) 0
  rw [dyadicEntropy_zero_of_unit_support _ _ (ae_rescaledComponent_mem_Ico μ i j),
    dyadicEntropy_zero_of_unit_support _ _ (ae_rescaledComponent_mem_Ico ν i k)] at h
  have he := dyadicEntropy_convolution_rescaledComponents μ ν i j k 0
  simp only [Nat.cast_zero, add_zero] at he
  rw [he] at h
  simpa only [zero_add] using h

noncomputable def averageRawConvolutionComponentEntropy (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν) (i : ℤ) (m : ℕ) : ℝ := by
  classical
  letI : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  letI : Fintype (dyadicLaw ν i).support := (dyadicLaw_support_finite ν hν i).fintype
  exact ∑ z : (dyadicLaw μ i).support × (dyadicLaw ν i).support,
    ((independentPair (supportLaw (dyadicLaw μ i)) (supportLaw (dyadicLaw ν i))) z).toReal *
      dyadicEntropy (realConvolution (rawComponent μ i z.1) (rawComponent ν i z.2))
        (realConvolution_hasBoundedSupport _ _ (rawComponent_hasBoundedSupport μ i z.1)
          (rawComponent_hasBoundedSupport ν i z.2)) (i + m)

theorem averageRawConvolutionComponentEntropy_le (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν) (i : ℤ) (m : ℕ) :
    averageRawConvolutionComponentEntropy μ ν hμ hν i m ≤
      dyadicEntropy (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν) (i + m) -
        dyadicEntropy (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν) i +
          Real.log 2 := by
  classical
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  let : Fintype (dyadicLaw ν i).support := (dyadicLaw_support_finite ν hν i).fintype
  let p := supportLaw (dyadicLaw μ i)
  let q := supportLaw (dyadicLaw ν i)
  let H (z : (dyadicLaw μ i).support × (dyadicLaw ν i).support) (l : ℤ) :=
    dyadicEntropy (realConvolution (rawComponent μ i z.1) (rawComponent ν i z.2))
      (realConvolution_hasBoundedSupport _ _ (rawComponent_hasBoundedSupport μ i z.1)
        (rawComponent_hasBoundedSupport ν i z.2)) l
  have h := average_convolution_dyadicEntropy_increment_le p q (rawComponent μ i) (rawComponent ν i)
    (rawComponent_hasBoundedSupport μ i) (rawComponent_hasBoundedSupport ν i) μ ν hμ hν
    (measure_eq_rawComponent_mixture μ hμ i) (measure_eq_rawComponent_mixture ν hν i) i m
  change (∑ z, ((independentPair p q) z).toReal * (H z (i + m) - H z i)) ≤ _ at h
  have hcoarse : (∑ z, ((independentPair p q) z).toReal * H z i) ≤ Real.log 2 := by
    calc
      _ ≤ ∑ z, ((independentPair p q) z).toReal * Real.log 2 := by
        apply Finset.sum_le_sum
        intro z _
        exact mul_le_mul_of_nonneg_left
          (dyadicEntropy_rawComponent_convolution_coarse_le μ ν i z.1 z.2) ENNReal.toReal_nonneg
      _ = _ := by rw [← Finset.sum_mul, sum_pmf_toReal, one_mul]
  simp only [mul_sub, Finset.sum_sub_distrib] at h
  change (∑ z, ((independentPair p q) z).toReal * H z (i + m)) ≤ _
  linarith

/-- Mean normalized entropy of the convolution of independently selected normalized components. -/
noncomputable def averageConvolutionComponentEntropy (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν) (i : ℤ) (m : ℕ) : ℝ := by
  classical
  letI : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  letI : Fintype (dyadicLaw ν i).support := (dyadicLaw_support_finite ν hν i).fintype
  exact ∑ z : (dyadicLaw μ i).support × (dyadicLaw ν i).support,
    ((independentPair (supportLaw (dyadicLaw μ i)) (supportLaw (dyadicLaw ν i))) z).toReal *
      normalizedDyadicEntropy (realConvolution (rescaledComponent μ i z.1) (rescaledComponent ν i z.2))
        (realConvolution_hasBoundedSupport _ _ (rescaledComponent_hasBoundedSupport μ i z.1)
          (rescaledComponent_hasBoundedSupport ν i z.2)) m

lemma averageConvolutionComponentEntropy_eq_div (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν) (i : ℤ) (m : ℕ) :
    averageConvolutionComponentEntropy μ ν hμ hν i m =
      averageRawConvolutionComponentEntropy μ ν hμ hν i m / ((m : ℝ) * Real.log 2) := by
  unfold averageConvolutionComponentEntropy averageRawConvolutionComponentEntropy
  simp only [normalizedDyadicEntropy, dyadicEntropy_convolution_rescaledComponents,
    ← mul_div_assoc, Finset.sum_div]

theorem averageConvolutionComponentEntropy_le (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν) (i : ℤ) {m : ℕ} (hm : 0 < m) :
    averageConvolutionComponentEntropy μ ν hμ hν i m ≤
      averageComponentEntropy (realConvolution μ ν)
        (realConvolution_hasBoundedSupport μ ν hμ hν) i m + 1 / (m : ℝ) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := div_le_div_of_nonneg_right (averageRawConvolutionComponentEntropy_le μ ν hμ hν i m)
    (mul_pos hm' hlog).le
  have he : Real.log 2 / ((m : ℝ) * Real.log 2) = 1 / (m : ℝ) := by field_simp
  simpa only [averageConvolutionComponentEntropy_eq_div, averageComponentEntropy_eq_increment,
    add_div, he] using h

end ExactOverlaps.Entropy
