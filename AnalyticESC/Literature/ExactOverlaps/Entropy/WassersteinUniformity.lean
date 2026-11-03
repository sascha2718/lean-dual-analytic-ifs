module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.NearGaussianUniformity
public import AnalyticESC.Literature.ExactOverlaps.Entropy.GaussianCDF

set_option maxSynthPendingDepth 3

/-!
# Wasserstein approximation implies local component uniformity

This uses the actual Kantorovich dual distance, finite first moments, and
the half-open interval approximation theorem. The tolerance and component
level are uniform in the Gaussian mean and in a fixed positive variance
interval. No quantitative central limit estimate is assumed or asserted.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.WassersteinUniformity`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ExactOverlaps.Entropy

lemma integrable_id_of_hasBoundedSupport (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ) := by
  obtain ⟨a, b, hab⟩ := hμ
  apply memLp_one_iff_integrable.mp
  apply MemLp.of_bound measurable_id.aestronglyMeasurable (max |a| |b|)
  filter_upwards [hab] with x hx
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have ha : - |a| ≤ a := neg_abs_le a
    exact (neg_le_neg (le_max_left _ _)).trans (ha.trans hx.1)
  · exact hx.2.trans ((le_abs_self b).trans (le_max_right _ _))

theorem exists_wasserstein_component_uniformity {σ V δ : ℝ}
    (hσ : 0 < σ) (hV : 0 < V) (hδ : 0 < δ) {m : ℕ} (hm : 0 < m) :
    ∃ p : ℕ, ∃ η > 0, ∀ (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
      (b : ℝ) (v : ℝ≥0), σ ≤ (v : ℝ) → (v : ℝ) ≤ V →
      GaussianApproximation.wasserstein1 μ (gaussianProbability b v)
        (integrable_id_of_hasBoundedSupport μ hμ) (gaussianProbability_integrable_id b v) ≤ η →
      componentEntropyLowerTailMass μ hμ p m δ < δ := by
  obtain ⟨p, ε, hε, hp⟩ := exists_near_gaussian_component_uniformity hσ hV hδ hm
  let L : ℝ := (Real.sqrt (2 * Real.pi * σ))⁻¹
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  let e : ℝ := ε / (4 * (L + 1))
  have he : 0 < e := by dsimp only [e]; positivity
  let η : ℝ := ε * e / 4
  have hη : 0 < η := by dsimp only [η]; positivity
  have hLe : L * e ≤ ε / 4 := by
    dsimp only [e]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 4 * (L + 1) by positivity)).2
    nlinarith
  refine ⟨p, η, hη, ?_⟩
  intro μ hμ b v hvσ hvV hW
  apply hp μ hμ b v hvσ hvV
  intro a c
  have h := GaussianApproximation.abs_real_Ico_sub_le_wasserstein1
    μ (gaussianProbability b v) (integrable_id_of_hasBoundedSupport μ hμ)
    (gaussianProbability_integrable_id b v) (gaussian_cdf_lipschitz b v hσ hvσ) a c he
  have hWe := div_le_div_of_nonneg_right hW he.le
  have hcancel : η / e = ε / 4 := by dsimp only [η]; field_simp
  rw [hcancel] at hWe
  change |((μ : Measure ℝ) (Ico a c)).toReal - (gaussianReal b v (Ico a c)).toReal| ≤ _ at h
  change _ ≤ 2 * (_ / e + L * e) at h
  linarith

end ExactOverlaps.Entropy
