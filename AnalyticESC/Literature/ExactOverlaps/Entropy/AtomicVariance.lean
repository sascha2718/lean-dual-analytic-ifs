module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.ComponentVariance

set_option maxSynthPendingDepth 3

/-!
# Most components of a small-variance law are atomic

Both the entropy and the variance of a component are small with high
probability when a level is chosen uniformly from a sufficiently long range.
The variance threshold may depend on the length of that range.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.AtomicVariance`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Classical

namespace ExactOverlaps.Entropy

lemma exists_positive_dyadic_depth {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ (2 : ℝ) ^ (-(m : ℤ)) < ε := by
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨j + 1, by omega, ?_⟩
  have hpow : (1 / 2 : ℝ) ^ (j + 1) < ε := by
    rw [pow_succ]
    have hnonneg : 0 ≤ (1 / 2 : ℝ) ^ j := pow_nonneg (by norm_num) _
    nlinarith
  simpa only [zpow_neg, zpow_natCast, one_div, inv_pow] using hpow

theorem exists_variance_threshold_most_components {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N < n →
      ∃ η > 0, ∀ (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ),
        (∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1) →
        ProbabilityTheory.variance id (μ : Measure ℝ) < η →
        levelVarianceEntropyBadMass μ hμ n m ε < ε := by
  obtain ⟨m₀, hm₀, hmesh⟩ := exists_positive_dyadic_depth hε
  obtain ⟨a, ha, haV⟩ := exists_entropy_threshold_variance hm₀
  have hbridge : ∀ (θ : ProbabilityMeasure ℝ) (hθ : HasBoundedSupport θ),
      (∀ᵐ x ∂(θ : Measure ℝ), x ∈ Icc (0 : ℝ) 1) →
      normalizedDyadicEntropy θ hθ m₀ < a →
      ProbabilityTheory.variance id (θ : Measure ℝ) < ε :=
    fun θ hθ hunit hsmall ↦ (haV θ hθ hunit hsmall).trans hmesh
  let C : ℝ := ((m : ℝ) + 3) / ε + ((m₀ : ℝ) + 3) / a
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  refine ⟨N, ?_⟩
  intro n hn
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
  obtain ⟨η, hη, hηE⟩ := exists_variance_threshold_normalizedEntropy hnpos
  refine ⟨η, hη, ?_⟩
  intro μ hμ hunit hvar
  have hE := (hηE μ hμ hunit hvar).le
  have hb := levelVarianceEntropyBadMass_le_tails μ hμ n m m₀ ε a hbridge
  have h₁ := levelEntropyTailMass_le_of_small_variance μ hμ hunit hnpos hm hε hE
  have h₂ := levelEntropyTailMass_le_of_small_variance μ hμ hunit hnpos hm₀ ha hE
  have hc : ((m : ℝ) + 3) / ((n : ℝ) * ε) + ((m₀ : ℝ) + 3) / ((n : ℝ) * a) = C / n := by
    dsimp only [C]
    ring
  have hCn : C / ε < (n : ℝ) := hN.trans (by exact_mod_cast hn)
  have hC : C / (n : ℝ) < ε := (div_lt_iff₀ hn').2 (by
    have h := (div_lt_iff₀ hε).1 hCn
    linarith)
  linarith

noncomputable def componentVarianceEntropyGoodMass (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) (ε : ℝ) : ℝ := by
  letI : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  exact ∑ k : (dyadicLaw μ i).support,
    if ProbabilityTheory.variance id (rescaledComponent μ i k : Measure ℝ) < ε ∧
      normalizedDyadicEntropy (rescaledComponent μ i k)
        (rescaledComponent_hasBoundedSupport μ i k) m < ε
    then ((dyadicLaw μ i) k).toReal else 0

noncomputable def levelVarianceEntropyGoodMass (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n m : ℕ) (ε : ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, componentVarianceEntropyGoodMass μ hμ i m ε) / n

lemma componentVarianceEntropyGoodMass_add_bad (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) (ε : ℝ) :
    componentVarianceEntropyGoodMass μ hμ i m ε +
      componentVarianceEntropyBadMass μ hμ i m ε = 1 := by
  let : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  rw [← sum_dyadic_cell_mass μ hμ i]
  unfold componentVarianceEntropyGoodMass componentVarianceEntropyBadMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hV : ProbabilityTheory.variance id (rescaledComponent μ i k : Measure ℝ) < ε <;>
    by_cases hE : normalizedDyadicEntropy (rescaledComponent μ i k)
      (rescaledComponent_hasBoundedSupport μ i k) m < ε <;>
    simp [← not_lt, hV, hE]


lemma levelVarianceEntropyGoodMass_add_bad (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) {n : ℕ} (hn : 0 < n) (m : ℕ) (ε : ℝ) :
    levelVarianceEntropyGoodMass μ hμ n m ε + levelVarianceEntropyBadMass μ hμ n m ε = 1 := by
  unfold levelVarianceEntropyGoodMass levelVarianceEntropyBadMass
  rw [← add_div, ← Finset.sum_add_distrib]
  simp only [componentVarianceEntropyGoodMass_add_bad, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one, div_self (show (n : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hn.ne')]

/-- Uniformly choose a level in 0,...,N and then choose the component with its actual mass. -/
theorem small_variance_most_components_atomic {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∃ η > 0, ∀ (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ),
        (∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1) →
        ProbabilityTheory.variance id (μ : Measure ℝ) < η →
        1 - ε < levelVarianceEntropyGoodMass μ hμ (N + 1) m ε := by
  obtain ⟨N₀, hN₀⟩ := exists_variance_threshold_most_components hm hε
  refine ⟨N₀, ?_⟩
  intro N hN
  obtain ⟨η, hη, hηG⟩ := hN₀ (N + 1) (by omega)
  refine ⟨η, hη, ?_⟩
  intro μ hμ hunit hvar
  have hb := hηG μ hμ hunit hvar
  have hsum := levelVarianceEntropyGoodMass_add_bad μ hμ (by omega : 0 < N + 1) m ε
  linarith

end ExactOverlaps.Entropy
