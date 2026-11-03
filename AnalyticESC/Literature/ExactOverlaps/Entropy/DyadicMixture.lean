module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Dyadic
public import AnalyticESC.Literature.ExactOverlaps.Entropy.ConditionalMixture

set_option maxSynthPendingDepth 3

/-!
# Concavity of dyadic entropy and its increments

The finite mixture is identified by an equality of actual Borel measures.
Dyadic quantization commutes with that mixture, and the nested-grid entropy
increment is a genuine conditional entropy.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.DyadicMixture`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

lemma dyadicLaw_eq_bind_of_measure_eq {ι : Type*} [Fintype ι] (p : PMF ι)
    (ν : ι → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hmix : (μ : Measure ℝ) = ∑ j, p j • (ν j : Measure ℝ)) (i : ℤ) :
    dyadicLaw μ i = p.bind (fun j ↦ dyadicLaw (ν j) i) := by
  ext k
  simp only [dyadicLaw_apply, hmix, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, PMF.bind_apply, tsum_fintype]

theorem average_dyadicEntropy_le_of_measure_eq {ι : Type*} [Fintype ι] (p : PMF ι)
    (ν : ι → ProbabilityMeasure ℝ) (hν : ∀ j, HasBoundedSupport (ν j))
    (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (hmix : (μ : Measure ℝ) = ∑ j, p j • (ν j : Measure ℝ)) (i : ℤ) :
    (∑ j, (p j).toReal * dyadicEntropy (ν j) (hν j) i) ≤ dyadicEntropy μ hμ i := by
  have h := average_finiteEntropy_le_bind p (fun j ↦ dyadicLaw (ν j) i)
    (fun j ↦ dyadicLaw_support_finite (ν j) (hν j) i)
  simpa only [← dyadicLaw_eq_bind_of_measure_eq p ν μ hmix i, dyadicEntropy] using h

lemma dyadicEntropy_increment_eq_conditional (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) :
    dyadicEntropy μ hμ (i + m) - dyadicEntropy μ hμ i =
      conditionalEntropy (dyadicLaw μ (i + m)) (dyadicLaw_support_finite μ hμ (i + m))
        (fun k : ℤ ↦ k / (2 ^ m : ℕ)) := by
  simpa only [dyadicEntropy, dyadicLaw_map_div] using
    (conditionalEntropy_eq_entropy_sub (dyadicLaw μ (i + m))
      (dyadicLaw_support_finite μ hμ (i + m)) (fun k : ℤ ↦ k / (2 ^ m : ℕ))).symm

theorem average_dyadicEntropy_increment_le_of_measure_eq {ι : Type*} [Fintype ι] (p : PMF ι)
    (ν : ι → ProbabilityMeasure ℝ) (hν : ∀ j, HasBoundedSupport (ν j))
    (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (hmix : (μ : Measure ℝ) = ∑ j, p j • (ν j : Measure ℝ)) (i : ℤ) (m : ℕ) :
    (∑ j, (p j).toReal * (dyadicEntropy (ν j) (hν j) (i + m) - dyadicEntropy (ν j) (hν j) i)) ≤
      dyadicEntropy μ hμ (i + m) - dyadicEntropy μ hμ i := by
  have h := average_conditionalEntropy_le_bind p (fun j ↦ dyadicLaw (ν j) (i + m))
    (fun j ↦ dyadicLaw_support_finite (ν j) (hν j) (i + m)) (fun k : ℤ ↦ k / (2 ^ m : ℕ))
  simp_rw [dyadicEntropy_increment_eq_conditional]
  simpa only [← dyadicLaw_eq_bind_of_measure_eq p ν μ hmix (i + m)] using h

end ExactOverlaps.Entropy
