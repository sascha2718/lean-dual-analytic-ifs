module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.GaussianComponents

set_option maxSynthPendingDepth 3

/-!
# Gaussian mass in finitely many central cells

Chebyshev's inequality gives a finite central set of labels of large actual
Gaussian mass. No finite-support hypothesis is imposed on the Gaussian law.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.GaussianCentralMass`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace ExactOverlaps.Entropy

lemma dyadicLaw_finset_mass (μ : ProbabilityMeasure ℝ) (i : ℤ) (J : Finset ℤ) :
    (∑ k ∈ J, ((dyadicLaw μ i) k).toReal) =
      ((μ : Measure ℝ) {x | dyadicQuantize i x ∈ J}).toReal := by
  rw [← ENNReal.toReal_sum (fun k _ ↦ (dyadicLaw μ i).apply_ne_top k),
    ← PMF.toMeasure_apply_finset, dyadicLaw_toMeasure,
    Measure.map_apply (measurable_dyadicQuantize i) J.measurableSet]
  rfl

theorem gaussian_central_labels_mass_ge (b : ℝ) (v : ℝ≥0) (i : ℤ)
    {R : ℝ} (hR : 0 < R) :
    1 - (v : ℝ) / R ^ 2 ≤
      ∑ k ∈ Finset.Icc (dyadicQuantize i (b - R)) (dyadicQuantize i (b + R)),
        ((dyadicLaw (gaussianProbability b v) i) k).toReal := by
  let J := Finset.Icc (dyadicQuantize i (b - R)) (dyadicQuantize i (b + R))
  let S : Set ℝ := {x | dyadicQuantize i x ∈ J}
  have hS : MeasurableSet S := (measurable_dyadicQuantize i) J.measurableSet
  have hsub : Sᶜ ⊆ {x : ℝ | R ≤ |x - b|} := by
    intro x hx
    change dyadicQuantize i x ∉ J at hx
    change R ≤ |x - b|
    by_contra hnot
    have hnear := abs_lt.mp (lt_of_not_ge hnot)
    have hxlo : b - R ≤ x := by linarith [hnear.1]
    have hxhi : x ≤ b + R := by linarith [hnear.2]
    apply hx
    exact Finset.mem_Icc.mpr
      ⟨Int.floor_mono (mul_le_mul_of_nonneg_left hxlo (dyadic_scale_pos i).le),
        Int.floor_mono (mul_le_mul_of_nonneg_left hxhi (dyadic_scale_pos i).le)⟩
  have hmem : MemLp (id : ℝ → ℝ) 2 (gaussianReal b v) := memLp_id_gaussianReal 2
  have hcheb := meas_ge_le_variance_div_sq hmem hR
  have htail : (gaussianReal b v {x : ℝ | R ≤ |x - b|}).toReal ≤ (v : ℝ) / R ^ 2 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
    simpa only [integral_id_gaussianReal, variance_id_gaussianReal, id_eq,
      ENNReal.toReal_ofReal (div_nonneg v.coe_nonneg (sq_nonneg _))] using h
  have hbad : (gaussianReal b v Sᶜ).toReal ≤ (v : ℝ) / R ^ 2 :=
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)).trans htail
  have hsum := measureReal_add_measureReal_compl (μ := gaussianReal b v) hS
  simp only [Measure.real, measure_univ, ENNReal.toReal_one] at hsum
  rw [dyadicLaw_finset_mass]
  change 1 - (v : ℝ) / R ^ 2 ≤ (gaussianReal b v S).toReal
  linarith

end ExactOverlaps.Entropy
