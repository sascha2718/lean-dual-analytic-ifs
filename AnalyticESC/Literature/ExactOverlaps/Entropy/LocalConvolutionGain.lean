module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.ConvolutionAveraging
public import AnalyticESC.Literature.ExactOverlaps.Entropy.MixtureUniformity

set_option maxSynthPendingDepth 3

/-!
# Local convolution gain from component entropy separation

Independent component sampling preserves each marginal mean entropy. Local
convolution entropy is therefore at least either marginal mean, up to the
explicit dyadic carry error. A nearly uniform second law yields a gain over
an entropy-deficient first law with exact exceptional-mass terms.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.LocalConvolutionGain`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

lemma sum_independentPair_fst {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : PMF β) (f : α → ℝ) :
    (∑ z : α × β, ((independentPair p q) z).toReal * f z.1) =
      ∑ a, (p a).toReal * f a := by
  simp only [Fintype.sum_prod_type, independentPair_apply, ENNReal.toReal_mul]
  have he (a : α) (b : β) : (p a).toReal * (q b).toReal * f a =
      ((p a).toReal * f a) * (q b).toReal := by ring
  simp_rw [he, ← Finset.mul_sum, sum_pmf_toReal, mul_one]

lemma sum_independentPair_snd {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : PMF β) (f : β → ℝ) :
    (∑ z : α × β, ((independentPair p q) z).toReal * f z.2) =
      ∑ b, (q b).toReal * f b := by
  simp only [Fintype.sum_prod_type, independentPair_apply, ENNReal.toReal_mul,
    mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, sum_pmf_toReal, one_mul]

theorem averageComponentEntropy_left_le_convolution_add_inv
    (μ ν : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν)
    (i : ℤ) {m : ℕ} (hm : 0 < m) :
    averageComponentEntropy μ hμ i m ≤
      averageConvolutionComponentEntropy μ ν hμ hν i m + 1 / (m : ℝ) := by
  classical
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  let : Fintype (dyadicLaw ν i).support := (dyadicLaw_support_finite ν hν i).fintype
  let p := independentPair (supportLaw (dyadicLaw μ i)) (supportLaw (dyadicLaw ν i))
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun (z : (dyadicLaw μ i).support × (dyadicLaw ν i).support) _ ↦
    mul_le_mul_of_nonneg_left
      (normalizedDyadicEntropy_left_le_convolution_add_inv
        (rescaledComponent μ i z.1) (rescaledComponent ν i z.2)
        (rescaledComponent_hasBoundedSupport μ i z.1)
        (rescaledComponent_hasBoundedSupport ν i z.2) hm)
      (show 0 ≤ (p z).toReal from ENNReal.toReal_nonneg))
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_pmf_toReal, one_mul] at h
  dsimp only [p] at h
  rw [sum_independentPair_fst (supportLaw (dyadicLaw μ i)) (supportLaw (dyadicLaw ν i))
    (fun k ↦ normalizedDyadicEntropy (rescaledComponent μ i k)
      (rescaledComponent_hasBoundedSupport μ i k) m)] at h
  simpa only [supportLaw_apply, averageComponentEntropy, averageConvolutionComponentEntropy, p] using h

theorem averageComponentEntropy_right_le_convolution_add_inv
    (μ ν : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν)
    (i : ℤ) {m : ℕ} (hm : 0 < m) :
    averageComponentEntropy ν hν i m ≤
      averageConvolutionComponentEntropy μ ν hμ hν i m + 1 / (m : ℝ) := by
  classical
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  let : Fintype (dyadicLaw ν i).support := (dyadicLaw_support_finite ν hν i).fintype
  let p := independentPair (supportLaw (dyadicLaw μ i)) (supportLaw (dyadicLaw ν i))
  have hp (z : (dyadicLaw μ i).support × (dyadicLaw ν i).support) :
      normalizedDyadicEntropy (rescaledComponent ν i z.2)
        (rescaledComponent_hasBoundedSupport ν i z.2) m ≤
      normalizedDyadicEntropy (realConvolution (rescaledComponent μ i z.1) (rescaledComponent ν i z.2))
        (realConvolution_hasBoundedSupport _ _ (rescaledComponent_hasBoundedSupport μ i z.1)
          (rescaledComponent_hasBoundedSupport ν i z.2)) m + 1 / (m : ℝ) := by
    simpa only [realConvolution_comm] using normalizedDyadicEntropy_left_le_convolution_add_inv
      (rescaledComponent ν i z.2) (rescaledComponent μ i z.1)
      (rescaledComponent_hasBoundedSupport ν i z.2) (rescaledComponent_hasBoundedSupport μ i z.1) hm
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun (z : (dyadicLaw μ i).support × (dyadicLaw ν i).support) _ ↦
    mul_le_mul_of_nonneg_left (hp z) (show 0 ≤ (p z).toReal from ENNReal.toReal_nonneg))
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_pmf_toReal, one_mul] at h
  dsimp only [p] at h
  rw [sum_independentPair_snd (supportLaw (dyadicLaw μ i)) (supportLaw (dyadicLaw ν i))
    (fun k ↦ normalizedDyadicEntropy (rescaledComponent ν i k)
      (rescaledComponent_hasBoundedSupport ν i k) m)] at h
  simpa only [supportLaw_apply, averageComponentEntropy, averageConvolutionComponentEntropy, p] using h

theorem localConvolutionEntropy_gain (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν) (i : ℤ)
    {m : ℕ} (hm : 0 < m) (a : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    averageComponentEntropy μ hμ i m + a * componentEntropyLowerTailMass μ hμ i m a -
      δ - componentEntropyLowerTailMass ν hν i m δ - 1 / (m : ℝ) ≤
        averageConvolutionComponentEntropy μ ν hμ hν i m := by
  have hleft := mul_componentEntropyLowerTailMass_le μ hμ i hm a
  have hright := component_entropy_deficiency_le_lowerTail ν hν i m hδ
  have hconv := averageComponentEntropy_right_le_convolution_add_inv μ ν hμ hν i hm
  linarith

end ExactOverlaps.Entropy
