module

public import AnalyticESC.Literature.ExactOverlaps.Entropy.DyadicMixture

set_option maxSynthPendingDepth 3

/-!
Retaining the finite mixture label costs at most its Shannon entropy.
The same bound holds for entropy increments between nested dyadic grids.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.MixtureEntropyBounds`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

theorem finiteEntropy_bind_le {ι α : Type*} [Fintype ι]
    (p : PMF ι) (q : ι → PMF α) (hq : ∀ i, (q i).support.Finite) :
    finiteEntropy (p.bind q) (bind_support_finite p q hq) ≤
      finiteEntropy p (Set.toFinite _) + ∑ i, (p i).toReal * finiteEntropy (q i) (hq i) := by
  have h := finiteEntropy_map_le (jointMixture p q)
    (jointMixture_support_finite p q hq) Prod.snd
  simpa only [jointMixture_map_snd, finiteEntropy_jointMixture p q hq] using h

theorem conditionalEntropy_bind_le {ι α β : Type*} [Fintype ι]
    (p : PMF ι) (q : ι → PMF α) (hq : ∀ i, (q i).support.Finite) (f : α → β) :
    conditionalEntropy (p.bind q) (bind_support_finite p q hq) f ≤
      finiteEntropy p (Set.toFinite _) +
        ∑ i, (p i).toReal * conditionalEntropy (q i) (hq i) f := by
  have hupper := finiteEntropy_bind_le p q hq
  have hlower := average_finiteEntropy_le_bind p (fun i ↦ (q i).map f)
    (fun i ↦ by simpa using (hq i).image f)
  simp only [← PMF.map_bind] at hlower
  simp_rw [conditionalEntropy_eq_entropy_sub, mul_sub, Finset.sum_sub_distrib]
  linarith

theorem dyadicEntropy_le_label_add_average_of_measure_eq {ι : Type*} [Fintype ι]
    (p : PMF ι) (ν : ι → ProbabilityMeasure ℝ) (hν : ∀ j, HasBoundedSupport (ν j))
    (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (hmix : (μ : Measure ℝ) = ∑ j, p j • (ν j : Measure ℝ)) (i : ℤ) :
    dyadicEntropy μ hμ i ≤ finiteEntropy p (Set.toFinite _) +
      ∑ j, (p j).toReal * dyadicEntropy (ν j) (hν j) i := by
  have h := finiteEntropy_bind_le p (fun j ↦ dyadicLaw (ν j) i)
    (fun j ↦ dyadicLaw_support_finite (ν j) (hν j) i)
  simpa only [← dyadicLaw_eq_bind_of_measure_eq p ν μ hmix i, dyadicEntropy] using h

theorem dyadicEntropy_increment_le_label_add_average_of_measure_eq
    {ι : Type*} [Fintype ι]
    (p : PMF ι) (ν : ι → ProbabilityMeasure ℝ) (hν : ∀ j, HasBoundedSupport (ν j))
    (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (hmix : (μ : Measure ℝ) = ∑ j, p j • (ν j : Measure ℝ)) (i : ℤ) (m : ℕ) :
    dyadicEntropy μ hμ (i + m) - dyadicEntropy μ hμ i ≤
      finiteEntropy p (Set.toFinite _) +
      ∑ j, (p j).toReal * (dyadicEntropy (ν j) (hν j) (i + m) -
        dyadicEntropy (ν j) (hν j) i) := by
  have h := conditionalEntropy_bind_le p (fun j ↦ dyadicLaw (ν j) (i + m))
    (fun j ↦ dyadicLaw_support_finite (ν j) (hν j) (i + m))
    (fun k : ℤ ↦ k / (2 ^ m : ℕ))
  simp_rw [dyadicEntropy_increment_eq_conditional]
  simpa only [← dyadicLaw_eq_bind_of_measure_eq p ν μ hmix (i + m)] using h

end ExactOverlaps.Entropy
