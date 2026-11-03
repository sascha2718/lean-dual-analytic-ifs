module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.DyadicMixture
public import AnalyticESC.Literature.ExactOverlaps.Entropy.Uniformity

set_option maxSynthPendingDepth 3

/-!
# Component uniformity of actual finite mixtures

Conditional entropy is concave under measure mixtures. Combining this with
the exact component entropy identity and two elementary probability bounds
transfers local uniformity from the constituent laws to their mixture.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.MixtureUniformity`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

lemma component_entropy_deficiency_le_lowerTail (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    1 - averageComponentEntropy μ hμ i m ≤
      δ + componentEntropyLowerTailMass μ hμ i m δ := by
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  classical
  have h : (∑ k : (dyadicLaw μ i).support, ((dyadicLaw μ i) k).toReal) ≤
      ∑ k : (dyadicLaw μ i).support,
        ((((dyadicLaw μ i) k).toReal * δ +
          (if normalizedDyadicEntropy (rescaledComponent μ i k)
            (rescaledComponent_hasBoundedSupport μ i k) m ≤ 1 - δ
            then ((dyadicLaw μ i) k).toReal else 0)) +
        ((dyadicLaw μ i) k).toReal * normalizedDyadicEntropy (rescaledComponent μ i k)
          (rescaledComponent_hasBoundedSupport μ i k) m) := by
    apply Finset.sum_le_sum
    intro k _
    have hw : 0 ≤ ((dyadicLaw μ i) k).toReal := ENNReal.toReal_nonneg
    have he := normalizedDyadicEntropy_nonneg (rescaledComponent μ i k)
      (rescaledComponent_hasBoundedSupport μ i k) m
    split_ifs with hk
    · nlinarith [mul_nonneg hw he, mul_nonneg hw hδ]
    · have hk' : 1 - δ < normalizedDyadicEntropy (rescaledComponent μ i k)
          (rescaledComponent_hasBoundedSupport μ i k) m := lt_of_not_ge hk
      have hmul := mul_le_mul_of_nonneg_left hk'.le hw
      nlinarith
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_dyadic_cell_mass μ hμ i, one_mul] at h
  change 1 ≤ δ + componentEntropyLowerTailMass μ hμ i m δ +
    averageComponentEntropy μ hμ i m at h
  linarith

theorem average_componentEntropy_le_of_measure_eq {ι : Type*} [Fintype ι]
    (p : PMF ι) (ν : ι → ProbabilityMeasure ℝ) (hν : ∀ j, HasBoundedSupport (ν j))
    (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (hmix : (μ : Measure ℝ) = ∑ j, p j • (ν j : Measure ℝ)) (i : ℤ) (m : ℕ) :
    (∑ j, (p j).toReal * averageComponentEntropy (ν j) (hν j) i m) ≤
      averageComponentEntropy μ hμ i m := by
  simp_rw [averageComponentEntropy_eq_increment, ← mul_div_assoc]
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right
    (average_dyadicEntropy_increment_le_of_measure_eq p ν hν μ hμ hmix i m)
    (mul_nonneg (Nat.cast_nonneg m) (Real.log_nonneg (by norm_num)))

theorem mixture_component_lowerTail_le {ι : Type*} [Fintype ι]
    (p : PMF ι) (ν : ι → ProbabilityMeasure ℝ) (hν : ∀ j, HasBoundedSupport (ν j))
    (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (hmix : (μ : Measure ℝ) = ∑ j, p j • (ν j : Measure ℝ)) (i : ℤ)
    {m : ℕ} (hm : 0 < m) {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) :
    a * componentEntropyLowerTailMass μ hμ i m a ≤
      δ + ∑ j, (p j).toReal * componentEntropyLowerTailMass (ν j) (hν j) i m δ := by
  have hmass : ∑ j, (p j).toReal = 1 := sum_pmf_toReal p
  have hsum : 1 - ∑ j, (p j).toReal * averageComponentEntropy (ν j) (hν j) i m ≤
      δ + ∑ j, (p j).toReal * componentEntropyLowerTailMass (ν j) (hν j) i m δ := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦
      mul_le_mul_of_nonneg_left
        (component_entropy_deficiency_le_lowerTail (ν j) (hν j) i m hδ)
        (show 0 ≤ (p j).toReal from ENNReal.toReal_nonneg))
    simpa only [mul_sub, mul_one, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, hmass, one_mul] using h
  have hconc := average_componentEntropy_le_of_measure_eq p ν hν μ hμ hmix i m
  have htail := mul_componentEntropyLowerTailMass_le μ hμ i hm a
  linarith

end ExactOverlaps.Entropy
