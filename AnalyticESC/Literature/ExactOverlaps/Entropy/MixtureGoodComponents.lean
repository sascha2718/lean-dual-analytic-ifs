module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.MixtureUniformity

set_option maxSynthPendingDepth 3

/-!
# Uniform components from a large set of good mixture laws

The exceptional weight is the actual mass assigned by the mixing PMF to
the complement of the stated predicate. The estimate allows arbitrary
zero weights and arbitrary bounded Borel constituent laws.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.MixtureGoodComponents`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

theorem mixture_component_lowerTail_le_with_exception {ι : Type*} [Fintype ι]
    (p : PMF ι) (ν : ι → ProbabilityMeasure ℝ) (hν : ∀ j, HasBoundedSupport (ν j))
    (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (hmix : (μ : Measure ℝ) = ∑ j, p j • (ν j : Measure ℝ)) (i : ℤ)
    {m : ℕ} (hm : 0 < m) {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (Q : ι → Prop) [DecidablePred Q]
    (hQ : ∀ j, Q j → componentEntropyLowerTailMass (ν j) (hν j) i m δ ≤ η)
    (a : ℝ) :
    a * componentEntropyLowerTailMass μ hμ i m a ≤
      δ + η + ∑ j, if Q j then 0 else (p j).toReal := by
  have hsum : (∑ j, (p j).toReal * componentEntropyLowerTailMass (ν j) (hν j) i m δ) ≤
      η + ∑ j, if Q j then 0 else (p j).toReal := by
    have h : (∑ j, (p j).toReal * componentEntropyLowerTailMass (ν j) (hν j) i m δ) ≤
        ∑ j, ((p j).toReal * η + if Q j then 0 else (p j).toReal) := by
      apply Finset.sum_le_sum
      intro j _
      have hw : 0 ≤ (p j).toReal := ENNReal.toReal_nonneg
      by_cases hj : Q j
      · simp only [hj, ite_true, add_zero]
        exact mul_le_mul_of_nonneg_left (hQ j hj) hw
      · simp only [hj, ite_false]
        have hle := mul_le_mul_of_nonneg_left
          (componentEntropyLowerTailMass_le_one (ν j) (hν j) i m δ) hw
        nlinarith [mul_nonneg hw hη]
    simpa only [Finset.sum_add_distrib, ← Finset.sum_mul, sum_pmf_toReal, one_mul] using h
  have h := mixture_component_lowerTail_le p ν hν μ hμ hmix i hm hδ a
  linarith

end ExactOverlaps.Entropy
