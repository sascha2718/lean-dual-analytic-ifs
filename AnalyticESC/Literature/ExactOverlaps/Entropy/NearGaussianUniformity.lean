module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.NearGaussian
public import AnalyticESC.Literature.ExactOverlaps.Entropy.AtomicVariance

set_option maxSynthPendingDepth 3

/-!
# Uniform component parameters for laws close to Gaussians

A single dyadic level and positive interval-error tolerance work for every
Gaussian mean and every variance in a fixed positive interval. Closeness
then forces the actual component entropy to exceed 1-delta with probability
greater than 1-delta. No regularity is required of the approximating law.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.NearGaussianUniformity`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ExactOverlaps.Entropy

theorem exists_near_gaussian_component_uniformity {σ V δ : ℝ}
    (hσ : 0 < σ) (hV : 0 < V) (hδ : 0 < δ) {m : ℕ} (hm : 0 < m) :
    ∃ p : ℕ, ∃ ε > 0, ∀ (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
      (b : ℝ) (v : ℝ≥0), σ ≤ (v : ℝ) → (v : ℝ) ≤ V →
      (∀ a c : ℝ, |((μ : Measure ℝ) (Ico a c)).toReal -
        (gaussianReal b v (Ico a c)).toReal| ≤ ε) →
      componentEntropyLowerTailMass μ hμ p m δ < δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (V / (δ / 2)))
  let R : ℝ := N
  have hR1 : 1 < R := (le_max_left _ _).trans_lt hN
  have hR : 0 < R := lt_trans zero_lt_one hR1
  have htail : V / R ^ 2 < δ / 2 := by
    have hVR : V / (δ / 2) < R := (le_max_right _ _).trans_lt hN
    have hVmul := (div_lt_iff₀ (show 0 < δ / 2 by positivity)).1 hVR
    apply (div_lt_iff₀ (sq_pos_of_pos hR)).2
    nlinarith [mul_pos hδ (sub_pos.mpr hR1)]
  let d : ℝ := (m : ℝ) * Real.log 2
  have hd : 0 < d := mul_pos (Nat.cast_pos.mpr hm) (Real.log_pos (by norm_num))
  let η : ℝ := δ * σ * d / (4 * (R + 1))
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨p, _hp, hpη⟩ := exists_positive_dyadic_depth hη
  let T : ℝ := 2 * (R + 1) * (2 : ℝ) ^ (-(p : ℤ)) / σ
  have hT : T < δ * d / 2 := by
    apply (div_lt_iff₀ hσ).2
    have hp' := (lt_div_iff₀ (show 0 < 4 * (R + 1) by positivity)).1 hpη
    nlinarith
  let A : ℝ := Real.exp T / (2 : ℝ) ^ m
  let B : ℝ := Real.exp (δ * d / 2) / (2 : ℝ) ^ m
  have hAB : A < B := div_lt_div_of_pos_right (Real.exp_lt_exp.mpr hT) (by positivity)
  have hB : 0 < B := by dsimp only [B]; positivity
  let c : ℝ := gaussianDensityFloor σ V (R + 1) * (2 : ℝ) ^ (-(p : ℤ))
  have hc : 0 < c := mul_pos (gaussianDensityFloor_pos hV) (by positivity)
  let ε : ℝ := min (δ / 4) ((B - A) * c / (2 * (B + 1)))
  have hε : 0 < ε := by
    apply lt_min (by positivity)
    exact div_pos (mul_pos (sub_pos.mpr hAB) hc) (by positivity)
  have hεsmall : ε ≤ δ / 4 := min_le_left _ _
  have hεbound : (B + 1) * ε ≤ (B - A) * c := by
    have hle := min_le_right (δ / 4) ((B - A) * c / (2 * (B + 1)))
    have hprod := (le_div_iff₀ (show 0 < 2 * (B + 1) by positivity)).1 hle
    have hnonneg := mul_nonneg (sub_nonneg.mpr hAB.le) hc.le
    change ε * (2 * (B + 1)) ≤ (B - A) * c at hprod
    nlinarith
  refine ⟨p, ε, hε, ?_⟩
  intro μ hμ b v hvσ hvV hclose
  have h := component_lowerTail_le_of_gaussian_interval_error μ hμ b v
    hσ hvσ hvV hR hδ p hm hT.le hεbound hclose
  have hvar := div_le_div_of_nonneg_right hvV (sq_nonneg R)
  linarith

end ExactOverlaps.Entropy
