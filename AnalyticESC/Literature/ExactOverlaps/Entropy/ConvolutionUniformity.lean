module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.SmallSummandUniformity
public import AnalyticESC.Literature.ExactOverlaps.Entropy.DyadicSqrtScale

set_option maxSynthPendingDepth 3

/-!
# Uniform components of long convolutions

This proves Hochman's Proposition 4.2, with the stronger allowance that the
unit support intervals may have different locations. The level is exactly
p minus the integer part of log base two of the square root of the number
of factors. The original unit interval case is an immediate specialization.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.ConvolutionUniformity`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace ExactOverlaps.Entropy

lemma variance_continuousSumLaw_le_of_unit_intervals {n : ℕ}
    (ν : Fin n → ProbabilityMeasure ℝ) (a : Fin n → ℝ)
    (hab : ∀ i, ∀ᵐ x ∂(ν i : Measure ℝ), x ∈ Icc (a i) (a i + 1)) :
    variance (id : ℝ → ℝ) (continuousSumLaw ν : Measure ℝ) ≤ (n : ℝ) := by
  rw [variance_continuousSumLaw ν (fun i ↦ ⟨a i, a i + 1, hab i⟩)]
  have hbound (i : Fin n) : variance (id : ℝ → ℝ) (ν i : Measure ℝ) ≤ 1 := by
    have h := variance_le_sq_of_bounded (hab i) measurable_id.aemeasurable
    norm_num only [add_sub_cancel_left] at h
    change variance (id : ℝ → ℝ) (ν i : Measure ℝ) ≤ 1 / 4 at h
    linarith
  calc
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ ↦ hbound i)
    _ = n := by simp

theorem exists_convolution_component_uniformity {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) {m : ℕ} (hm : 0 < m) :
    ∃ p K : ℕ, 0 < K ∧ ∀ n : ℕ, K ≤ n →
      ∀ (ν : Fin n → ProbabilityMeasure ℝ) (a : Fin n → ℝ)
      (hab : ∀ i, ∀ᵐ x ∂(ν i : Measure ℝ), x ∈ Icc (a i) (a i + 1)),
      σ * n ≤ variance (id : ℝ → ℝ) (continuousSumLaw ν : Measure ℝ) →
      componentEntropyLowerTailMass (continuousSumLaw ν)
        (continuousSumLaw_hasBoundedSupport ν (fun i ↦ ⟨a i, a i + 1, hab i⟩))
        ((p : ℤ) - dyadicSqrtScale n) m δ < δ := by
  obtain ⟨p, ε, hε, hp⟩ := exists_small_summand_component_uniformity hσ
    (by norm_num : (0 : ℝ) < 4) hδ hm
  obtain ⟨K, hK, hscale⟩ := exists_dyadicSqrtScale_factor_lt hε
  refine ⟨p, K, hK, ?_⟩
  intro n hn ν a hab hvar
  have hnpos : 0 < n := lt_of_lt_of_le hK hn
  have hupper := variance_continuousSumLaw_le_of_unit_intervals ν a hab
  have hrange := dyadicSqrtScale_variance_bounds hnpos hσ.le (by norm_num : (0 : ℝ) ≤ 1)
    hvar (by simpa using hupper)
  let v : ℝ≥0 := ⟨((2 : ℝ) ^ (-(dyadicSqrtScale n : ℤ))) ^ 2 *
    variance (id : ℝ → ℝ) (continuousSumLaw ν : Measure ℝ),
    mul_nonneg (sq_nonneg _) (variance_nonneg _ _)⟩
  have hsmall : (2 : ℝ) ^ (-(dyadicSqrtScale n : ℤ)) * 1 ≤ ε := by
    simpa only [mul_one] using (hscale n hn).le
  have h := hp ν a (fun i ↦ a i + 1) hab (-(dyadicSqrtScale n : ℤ)) 1
    (fun _ ↦ by linarith) hsmall v hrange.1 (hrange.2.trans_eq (mul_one 4)) rfl
  convert h using 1
  congr 1
  omega

end ExactOverlaps.Entropy
