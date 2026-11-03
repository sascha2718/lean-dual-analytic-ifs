module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.VarianceConcentration
public import AnalyticESC.Literature.ExactOverlaps.Entropy.DyadicConcentration
public import AnalyticESC.Literature.ExactOverlaps.Entropy.RareConcentration

set_option maxSynthPendingDepth 3

/-!
# Small variance and small entropy

Uniform estimates for all Borel probabilities on the closed unit interval.
Chebyshev concentration, the two-cell bound, and the actual binary entropy
give the constant two in the normalized small-variance estimate.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.SmallVarianceEntropy`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

namespace ExactOverlaps.Entropy

theorem exists_variance_threshold_dyadicEntropy (m : ℕ) :
    ∃ η > 0, ∀ (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ),
      (∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1) →
      ProbabilityTheory.variance id (μ : Measure ℝ) < η →
      dyadicEntropy μ hμ m < 2 * Real.log 2 := by
  obtain ⟨δ, hδ, hd⟩ := exists_rare_mass_entropy_bound 2 (2 ^ m + 1)
    (by norm_num) (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  let r : ℝ := 1 / (2 * (2 : ℝ) ^ (m : ℤ))
  have hr : 0 < r := by positivity
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  refine ⟨δ * r ^ 2, mul_pos hδ hr2, ?_⟩
  intro μ hμ hunit hvar
  let c : ℝ := ∫ x : ℝ, x ∂(μ : Measure ℝ)
  let k : ℤ := dyadicQuantize m (c - r)
  let f : ℤ → Bool := fun z ↦ decide (z ∉ Icc k (k + 1))
  have hgood : ((dyadicLaw_support_finite μ hμ m).toFinset.filter
      (fun a ↦ f a = false)).card ≤ 2 := by
    have hs : (dyadicLaw_support_finite μ hμ m).toFinset.filter (fun a ↦ f a = false) ⊆
        Finset.Icc k (k + 1) := by
      intro a ha
      have h := (Finset.mem_filter.mp ha).2
      simpa only [f, decide_eq_false_iff_not, not_not, Finset.mem_Icc, Set.mem_Icc] using h
    exact (Finset.card_le_card hs).trans_eq (by rw [Int.card_Icc]; omega)
  have hrare : (((dyadicLaw μ m).map f) true).toReal ≤ δ := by
    rw [dyadicLaw_map_bool_apply]
    have hsub : {x | f (dyadicQuantize m x) = true} ⊆
        {x : ℝ | r ≤ |x - c|} := by
      intro x hx
      have hbad : dyadicQuantize m x ∉ Icc k (k + 1) := by simpa only [f, decide_eq_true_eq, Set.mem_ofPred_eq] using hx
      by_contra hnot
      have hnear : |x - c| < r := lt_of_not_ge hnot
      exact hbad (dyadicQuantize_near_center m c x hnear)
    have hmem : MemLp (id : ℝ → ℝ) 2 (μ : Measure ℝ) :=
      memLp_of_bounded hunit measurable_id.aestronglyMeasurable 2
    have hcheb := meas_ge_le_variance_div_sq hmem hr
    have hcheb' : ((μ : Measure ℝ) {x : ℝ | r ≤ |x - c|}).toReal ≤
        ProbabilityTheory.variance id (μ : Measure ℝ) / r ^ 2 := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
      simpa only [c, id_eq, ENNReal.toReal_ofReal (div_nonneg
        (ProbabilityTheory.variance_nonneg _ _) (sq_nonneg _))] using h
    have hv : ProbabilityTheory.variance id (μ : Measure ℝ) / r ^ 2 < δ :=
      (div_lt_iff₀ hr2).2 hvar
    exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)).trans
      (hcheb'.trans hv.le)
  have h := hd (dyadicLaw μ m) (dyadicLaw_support_finite μ hμ m) f hgood
    (dyadicLaw_card_le_pow_two_add_one μ hμ m hunit) hrare
  change dyadicEntropy μ hμ m < Real.log 2 + Real.log 2 at h
  linarith

/-- The first implication of the variance/entropy comparison, with its stated constant. -/
theorem exists_variance_threshold_normalizedEntropy {m : ℕ} (hm : 0 < m) :
    ∃ η > 0, ∀ (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ),
      (∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1) →
      ProbabilityTheory.variance id (μ : Measure ℝ) < η →
      normalizedDyadicEntropy μ hμ m < 2 / (m : ℝ) := by
  obtain ⟨η, hη, h⟩ := exists_variance_threshold_dyadicEntropy m
  refine ⟨η, hη, ?_⟩
  intro μ hμ hunit hvar
  have hden : 0 < (m : ℝ) * Real.log 2 :=
    mul_pos (Nat.cast_pos.mpr hm) (Real.log_pos (by norm_num))
  have hb := (div_lt_div_iff_of_pos_right hden).2 (h μ hμ hunit hvar)
  have he : 2 * Real.log 2 / ((m : ℝ) * Real.log 2) = 2 / (m : ℝ) := by field_simp
  simpa only [he, normalizedDyadicEntropy] using hb

/-- The converse implication: sufficiently small m-scale entropy forces variance below 2^-m. -/
theorem exists_entropy_threshold_variance {m : ℕ} (hm : 0 < m) :
    ∃ η > 0, ∀ (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ),
      (∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1) →
      normalizedDyadicEntropy μ hμ m < η →
      ProbabilityTheory.variance id (μ : Measure ℝ) < (2 : ℝ) ^ (-(m : ℤ)) := by
  let r : ℝ := (2 : ℝ) ^ (-(m : ℤ))
  have hr : 0 < r := zpow_pos (by norm_num) _
  have hr1 : r < 1 := zpow_lt_one_of_neg₀ (by norm_num) (by omega)
  have hgap : 0 < r - r ^ 2 := by nlinarith
  have hden : 0 < (m : ℝ) * Real.log 2 :=
    mul_pos (Nat.cast_pos.mpr hm) (Real.log_pos (by norm_num))
  refine ⟨(r - r ^ 2) / ((m : ℝ) * Real.log 2), div_pos hgap hden, ?_⟩
  intro μ hμ hunit hsmall
  have he : dyadicEntropy μ hμ m < r - r ^ 2 :=
    (div_lt_div_iff_of_pos_right hden).1 hsmall
  have hv := variance_le_dyadicEntropy_add_mesh_sq μ hμ hunit m
  change ProbabilityTheory.variance id (μ : Measure ℝ) ≤ dyadicEntropy μ hμ m + r ^ 2 at hv
  linarith

end ExactOverlaps.Entropy
