module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.CDFDistance

set_option maxSynthPendingDepth 3

/-!
# Half-open interval control without excluding atoms

A uniform CDF error transfers to left half-lines when the comparison CDF is
Lipschitz. Subtracting two left half-lines controls the actual half-open cells
used by the entropy quantizers, even when the approximating law has atoms.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.HalfOpenCDF`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace ExactOverlaps.GaussianApproximation

lemma abs_real_Iio_sub_cdf_le (μ ν : ProbabilityMeasure ℝ) {δ : ℝ}
    (hδ : ∀ a, |cdf (μ : Measure ℝ) a - cdf (ν : Measure ℝ) a| ≤ δ)
    {L : ℝ≥0} (hL : LipschitzWith L (cdf (ν : Measure ℝ))) (a : ℝ) :
    |(μ : Measure ℝ).real (Iio a) - cdf (ν : Measure ℝ) a| ≤ δ := by
  have hu : (μ : Measure ℝ).real (Iio a) ≤ cdf (μ : Measure ℝ) a := by
    rw [cdf_eq_real]
    exact measureReal_mono Iio_subset_Iic_self
  have hl : cdf (ν : Measure ℝ) a ≤ (μ : Measure ℝ).real (Iio a) + δ := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let d := ε / ((L : ℝ) + 1)
    have hLp : 0 < (L : ℝ) + 1 := by positivity
    have hd : 0 < d := div_pos hε hLp
    have hmass : cdf (μ : Measure ℝ) (a - d) ≤ (μ : Measure ℝ).real (Iio a) := by
      rw [cdf_eq_real]
      exact measureReal_mono (fun _ hx ↦ lt_of_le_of_lt hx (sub_lt_self a hd))
    have hlip := hL.dist_le_mul a (a - d)
    simp only [Real.dist_eq, sub_sub_cancel, abs_of_pos hd] at hlip
    have hdiff := (le_abs_self _).trans hlip
    have hclose := (abs_le.mp (hδ (a - d))).1
    have hsmall : (L : ℝ) * d ≤ ε := by
      dsimp [d]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hLp).mpr
      nlinarith
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith [(abs_le.mp (hδ a)).2]⟩

lemma real_Iio_eq_cdf_of_lipschitz (ν : ProbabilityMeasure ℝ) {L : ℝ≥0}
    (hL : LipschitzWith L (cdf (ν : Measure ℝ))) (a : ℝ) :
    (ν : Measure ℝ).real (Iio a) = cdf (ν : Measure ℝ) a := by
  have h := abs_real_Iio_sub_cdf_le ν ν (δ := 0) (fun _ ↦ by simp) hL a
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

lemma real_Ico_eq_sub_Iio (μ : ProbabilityMeasure ℝ) {a b : ℝ} (hab : a ≤ b) :
    (μ : Measure ℝ).real (Ico a b) =
      (μ : Measure ℝ).real (Iio b) - (μ : Measure ℝ).real (Iio a) := by
  have hs : Ico a b = Iio b \ Iio a := by ext x; simp only [mem_Ico, mem_sdiff, mem_Iio, not_lt]; tauto
  rw [hs, measureReal_sdiff (Iio_subset_Iio hab) measurableSet_Iio]

theorem abs_real_Ico_sub_le_of_cdf (μ ν : ProbabilityMeasure ℝ) {δ : ℝ}
    (hδ : ∀ a, |cdf (μ : Measure ℝ) a - cdf (ν : Measure ℝ) a| ≤ δ)
    {L : ℝ≥0} (hL : LipschitzWith L (cdf (ν : Measure ℝ))) (a b : ℝ) :
    |(μ : Measure ℝ).real (Ico a b) - (ν : Measure ℝ).real (Ico a b)| ≤ 2 * δ := by
  have hd : 0 ≤ δ := (abs_nonneg _).trans (hδ 0)
  by_cases hab : a ≤ b
  · rw [real_Ico_eq_sub_Iio μ hab, real_Ico_eq_sub_Iio ν hab,
      real_Iio_eq_cdf_of_lipschitz ν hL a, real_Iio_eq_cdf_of_lipschitz ν hL b]
    have ha := abs_le.mp (abs_real_Iio_sub_cdf_le μ ν hδ hL a)
    have hb := abs_le.mp (abs_real_Iio_sub_cdf_le μ ν hδ hL b)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have he : Ico a b = ∅ := Ico_eq_empty_of_le (le_of_not_ge hab)
    simp only [he, measureReal_empty, sub_self, abs_zero]
    positivity

theorem abs_real_Ico_sub_le_wasserstein1 (μ ν : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    (hν : Integrable (fun x : ℝ ↦ x) (ν : Measure ℝ))
    {L : ℝ≥0} (hL : LipschitzWith L (cdf (ν : Measure ℝ)))
    (a b : ℝ) {e : ℝ} (he : 0 < e) :
    |(μ : Measure ℝ).real (Ico a b) - (ν : Measure ℝ).real (Ico a b)| ≤
      2 * (wasserstein1 μ ν hμ hν / e + (L : ℝ) * e) :=
  abs_real_Ico_sub_le_of_cdf μ ν (fun a ↦ abs_cdf_sub_le μ ν hμ hν hL a he) hL a b

end ExactOverlaps.GaussianApproximation
