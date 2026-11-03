module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.SmallVarianceEntropy
public import AnalyticESC.Literature.ExactOverlaps.Entropy.ConvolutionAveraging

set_option maxSynthPendingDepth 3

/-!
# Components with large variance or entropy

The bad-event probabilities below use the actual component weights.
An entropy threshold controlling variance reduces the union of the two bad
events to two entropy tails, at possibly different observation depths.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.ComponentVariance`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Classical

namespace ExactOverlaps.Entropy

noncomputable def componentVarianceEntropyBadMass (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m : ℕ) (ε : ℝ) : ℝ := by
  letI : Fintype (dyadicLaw μ i).support := (dyadicLaw_support_finite μ hμ i).fintype
  exact ∑ k : (dyadicLaw μ i).support,
    if ε ≤ ProbabilityTheory.variance id (rescaledComponent μ i k : Measure ℝ) ∨
      ε ≤ normalizedDyadicEntropy (rescaledComponent μ i k)
        (rescaledComponent_hasBoundedSupport μ i k) m
    then ((dyadicLaw μ i) k).toReal else 0

noncomputable def levelVarianceEntropyBadMass (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n m : ℕ) (ε : ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, componentVarianceEntropyBadMass μ hμ i m ε) / n

lemma componentVarianceEntropyBadMass_le_tails (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (i : ℤ) (m m₀ : ℕ) (ε a : ℝ)
    (hbridge : ∀ (θ : ProbabilityMeasure ℝ) (hθ : HasBoundedSupport θ),
      (∀ᵐ x ∂(θ : Measure ℝ), x ∈ Icc (0 : ℝ) 1) →
      normalizedDyadicEntropy θ hθ m₀ < a →
      ProbabilityTheory.variance id (θ : Measure ℝ) < ε) :
    componentVarianceEntropyBadMass μ hμ i m ε ≤
      componentEntropyTailMass μ hμ i m ε + componentEntropyTailMass μ hμ i m₀ a := by
  unfold componentVarianceEntropyBadMass componentEntropyTailMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  have hv : ε ≤ ProbabilityTheory.variance id (rescaledComponent μ i k : Measure ℝ) →
      a ≤ normalizedDyadicEntropy (rescaledComponent μ i k)
        (rescaledComponent_hasBoundedSupport μ i k) m₀ := by
    intro hV
    by_contra hnot
    have hunit : ∀ᵐ x ∂(rescaledComponent μ i k : Measure ℝ), x ∈ Icc (0 : ℝ) 1 :=
      (ae_rescaledComponent_mem_Ico μ i k).mono (fun _ h ↦ ⟨h.1, h.2.le⟩)
    exact (not_lt_of_ge hV) (hbridge _ _ hunit (lt_of_not_ge hnot))
  have hw : 0 ≤ ((dyadicLaw μ i) k).toReal := ENNReal.toReal_nonneg
  have hind (P Q R : Prop) (hPR : P → R) :
      (if P ∨ Q then ((dyadicLaw μ i) k).toReal else 0) ≤
        (if Q then ((dyadicLaw μ i) k).toReal else 0) +
          (if R then ((dyadicLaw μ i) k).toReal else 0) := by
    by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp_all
  exact hind _ _ _ hv


lemma levelVarianceEntropyBadMass_le_tails (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n m m₀ : ℕ) (ε a : ℝ)
    (hbridge : ∀ (θ : ProbabilityMeasure ℝ) (hθ : HasBoundedSupport θ),
      (∀ᵐ x ∂(θ : Measure ℝ), x ∈ Icc (0 : ℝ) 1) →
      normalizedDyadicEntropy θ hθ m₀ < a →
      ProbabilityTheory.variance id (θ : Measure ℝ) < ε) :
    levelVarianceEntropyBadMass μ hμ n m ε ≤
      levelEntropyTailMass μ hμ n m ε + levelEntropyTailMass μ hμ n m₀ a := by
  unfold levelVarianceEntropyBadMass levelEntropyTailMass
  rw [← add_div, ← Finset.sum_add_distrib]
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun i _ ↦ componentVarianceEntropyBadMass_le_tails μ hμ i m m₀ ε a hbridge))
    (Nat.cast_nonneg n)

lemma levelEntropyTailMass_le_of_small_variance (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ)
    (hunit : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {a : ℝ} (ha : 0 < a)
    (hentropy : normalizedDyadicEntropy μ hμ n ≤ 2 / (n : ℝ)) :
    levelEntropyTailMass μ hμ n m a ≤ ((m : ℝ) + 3) / ((n : ℝ) * a) := by
  have hzero := dyadicEntropy_zero_le_log_two_of_closed_unit_support μ hμ hunit
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hz := div_le_div_of_nonneg_right hzero (mul_pos hn' hl).le
  have he : Real.log 2 / ((n : ℝ) * Real.log 2) = 1 / (n : ℝ) := by field_simp
  rw [he] at hz
  have h := levelEntropyTailMass_le μ hμ hn hm ha
  have hb : normalizedDyadicEntropy μ hμ n + (m : ℝ) / n +
      dyadicEntropy μ hμ 0 / ((n : ℝ) * Real.log 2) ≤ ((m : ℝ) + 3) / n := by
    calc
      _ ≤ 2 / (n : ℝ) + (m : ℝ) / n + 1 / (n : ℝ) :=
        add_le_add (add_le_add hentropy le_rfl) hz
      _ = _ := by ring
  have hdiv := div_le_div_of_nonneg_right hb ha.le
  have he' : (((m : ℝ) + 3) / n) / a = ((m : ℝ) + 3) / ((n : ℝ) * a) := by ring
  rw [he'] at hdiv
  exact h.trans hdiv

end ExactOverlaps.Entropy
