module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.RealConvolution
public import AnalyticESC.Literature.ExactOverlaps.Entropy.DyadicMixture
public import Mathlib.MeasureTheory.Measure.WithDensity

set_option maxSynthPendingDepth 3

/-!
# Finite mixtures commute with real convolution

The component index pair carries its actual independent product PMF.
The mixture equality is an equality of Borel measures, so conditional
entropy concavity applies to every nested dyadic partition.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.ConvolutionMixture`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace ExactOverlaps.Entropy

lemma sFinite_finset_sum {ι : Type*} (μ : ι → Measure ℝ) [∀ i, SFinite (μ i)]
    (s : Finset ι) : SFinite (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; infer_instance
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    let : SFinite (∑ i ∈ s, μ i) := ih
    infer_instance

lemma measure_finset_sum_conv {ι : Type*} (μ : ι → Measure ℝ) [∀ i, SFinite (μ i)]
    (ν : Measure ℝ) [SFinite ν] (s : Finset ι) :
    (∑ i ∈ s, μ i) ∗ ν = ∑ i ∈ s, (μ i) ∗ ν := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    let : SFinite (∑ i ∈ s, μ i) := sFinite_finset_sum μ s
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.add_conv, ih]

lemma measure_conv_finset_sum {ι : Type*} (μ : Measure ℝ) [SFinite μ]
    (ν : ι → Measure ℝ) [∀ i, SFinite (ν i)] (s : Finset ι) :
    μ ∗ (∑ i ∈ s, ν i) = ∑ i ∈ s, μ ∗ (ν i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    let : SFinite (∑ i ∈ s, ν i) := sFinite_finset_sum ν s
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.conv_add, ih]

theorem realConvolution_eq_pair_mixture {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : PMF ι) (q : PMF κ) (μs : ι → ProbabilityMeasure ℝ) (νs : κ → ProbabilityMeasure ℝ)
    (μ ν : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) = ∑ j, p j • (μs j : Measure ℝ))
    (hν : (ν : Measure ℝ) = ∑ k, q k • (νs k : Measure ℝ)) :
    (realConvolution μ ν : Measure ℝ) =
      ∑ z : ι × κ, (independentPair p q) z • (realConvolution (μs z.1) (νs z.2) : Measure ℝ) := by
  let : SFinite (∑ k, q k • (νs k : Measure ℝ)) :=
    sFinite_finset_sum (fun k ↦ q k • (νs k : Measure ℝ)) Finset.univ
  simp only [realConvolution_toMeasure, Fintype.sum_prod_type, independentPair_apply]
  rw [hμ, hν, measure_finset_sum_conv]
  simp_rw [measure_conv_finset_sum, Measure.conv_smul_left, Measure.conv_smul_right, smul_smul]

/-- Conditional dyadic entropy of a convolution dominates its component-mixture average. -/
theorem average_convolution_dyadicEntropy_increment_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : PMF ι) (q : PMF κ) (μs : ι → ProbabilityMeasure ℝ) (νs : κ → ProbabilityMeasure ℝ)
    (hμs : ∀ j, HasBoundedSupport (μs j)) (hνs : ∀ k, HasBoundedSupport (νs k))
    (μ ν : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν)
    (hμmix : (μ : Measure ℝ) = ∑ j, p j • (μs j : Measure ℝ))
    (hνmix : (ν : Measure ℝ) = ∑ k, q k • (νs k : Measure ℝ)) (i : ℤ) (m : ℕ) :
    (∑ z : ι × κ, ((independentPair p q) z).toReal *
      (dyadicEntropy (realConvolution (μs z.1) (νs z.2))
          (realConvolution_hasBoundedSupport _ _ (hμs z.1) (hνs z.2)) (i + m) -
        dyadicEntropy (realConvolution (μs z.1) (νs z.2))
          (realConvolution_hasBoundedSupport _ _ (hμs z.1) (hνs z.2)) i)) ≤
    dyadicEntropy (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν) (i + m) -
      dyadicEntropy (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν) i :=
  average_dyadicEntropy_increment_le_of_measure_eq (independentPair p q)
    (fun z ↦ realConvolution (μs z.1) (νs z.2))
    (fun z ↦ realConvolution_hasBoundedSupport _ _ (hμs z.1) (hνs z.2))
    (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν)
    (realConvolution_eq_pair_mixture p q μs νs μ ν hμmix hνmix) i m

end ExactOverlaps.Entropy
