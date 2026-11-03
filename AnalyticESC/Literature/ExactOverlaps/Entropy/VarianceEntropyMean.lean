module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.ComponentVarianceSampling
public import AnalyticESC.Literature.ExactOverlaps.Entropy.SmallVarianceEntropy
public import AnalyticESC.Literature.ExactOverlaps.Entropy.Averaging

set_option maxSynthPendingDepth 3

/-!
# Mean component entropy controlled by mean component variance

Small variance gives entropy at most 2/m; the remaining components are
controlled by their actual variance through a uniform threshold. This is the
first density estimate in the sufficient inverse entropy theorem.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.VarianceEntropyMean`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

lemma averageComponentVariance_eq_sum (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) [Fintype (dyadicLaw μ i).support] :
    averageComponentVariance μ hμ i =
      ∑ k : (dyadicLaw μ i).support, ((dyadicLaw μ i) k).toReal * componentVariance μ i k := by
  classical
  unfold averageComponentVariance FiniteProbability.expectation
  calc
    _ = ∑ k : (dyadicLaw μ i).support,
        ((supportLaw (dyadicLaw μ i)) k).toReal * componentVariance μ i k := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk
      have hz : supportLaw (dyadicLaw μ i) k = 0 := by simpa using hk
      simp only [hz, ENNReal.toReal_zero, zero_mul]
    _ = _ := by simp only [supportLaw_apply]

theorem exists_component_entropy_variance_bound {m : ℕ} (hm : 0 < m) :
    ∃ η > 0, ∀ (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (i : ℤ),
      averageComponentEntropy μ hμ i m ≤ 2 / (m : ℝ) + averageComponentVariance μ hμ i / η := by
  obtain ⟨η, hη, hsmall⟩ := exists_variance_threshold_normalizedEntropy hm
  refine ⟨η, hη, ?_⟩
  intro μ hμ i
  classical
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  have hp (k : (dyadicLaw μ i).support) :
      normalizedDyadicEntropy (rescaledComponent μ i k)
        (rescaledComponent_hasBoundedSupport μ i k) m ≤ 2 / (m : ℝ) + componentVariance μ i k / η := by
    by_cases hk : componentVariance μ i k < η
    · have he := hsmall (rescaledComponent μ i k) (rescaledComponent_hasBoundedSupport μ i k)
        ((ae_rescaledComponent_mem_Ico μ i k).mono (fun _ hx ↦ ⟨hx.1, hx.2.le⟩)) hk
      exact he.le.trans (le_add_of_nonneg_right (div_nonneg (componentVariance_nonneg μ i k) hη.le))
    · have he := normalizedDyadicEntropy_le_one (rescaledComponent μ i k)
        (rescaledComponent_hasBoundedSupport μ i k) hm (ae_rescaledComponent_mem_Ico μ i k)
      have hv : 1 ≤ componentVariance μ i k / η := (one_le_div hη).2 (le_of_not_gt hk)
      have hpos : 0 ≤ 2 / (m : ℝ) := by positivity
      linarith
  unfold averageComponentEntropy
  calc
    _ ≤ ∑ k : (dyadicLaw μ i).support,
        ((dyadicLaw μ i) k).toReal * (2 / (m : ℝ) + componentVariance μ i k / η) :=
      Finset.sum_le_sum (fun k _ ↦ mul_le_mul_of_nonneg_left (hp k) ENNReal.toReal_nonneg)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← mul_div_assoc, ← Finset.sum_div,
        ← Finset.sum_mul, sum_dyadic_cell_mass μ hμ i, one_mul,
        ← averageComponentVariance_eq_sum μ hμ i]

end ExactOverlaps.Entropy
