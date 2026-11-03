module

public import AnalyticESC.Dimension.Defs
public import AnalyticESC.Literature.GeometricMeasureTheory.Hausdorff.Computing

@[expose] public section

/-!
# The mass distribution principle for local dimensions

If a probability measure `μ` on `ℝ` is carried by a set `K` and has local dimension `d` at
`μ`-almost every point, in the form `log μ(B̄(x, r)) / log r → d` of
`AnalyticESC.RapaportMeasureStatement`, then `dim_H K ≥ d`. This is the inequality
`dim μ_n ≤ dim_H K_Φ` in the proof of Corollary 1.3 of A. Rapaport, *Dimension of self-conformal
measures associated to an exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2. The
proof uses the mass distribution principle `GeometricMeasureTheory.mass_distribution` (Lemma 2.16
of the `GeometricMeasureTheory` notes).

Main declaration:

* `ofReal_le_dimH_of_ae_tendsto`: `ENNReal.ofReal d ≤ dimH K`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Attractor.MassDistribution`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Attractor

open Set Filter Topology MeasureTheory Metric AnalyticESC
open scoped ENNReal NNReal

/-- A local dimension `> t > 0` at `x` gives `μ(B(x, r)) ≤ r^t` for all small `r`. -/
theorem exists_ball_le_rpow {μ : Measure ℝ} [IsFiniteMeasure μ] {x d t : ℝ} (ht0 : 0 < t)
    (htd : t < d)
    (h : Tendsto (fun r : Scale => logRatio (μ.real (closedBall x r)) r) scaleZero (𝓝 d)) :
    ∃ k : ℕ, ∀ r : ℝ, 0 < r → r < 1 / ((k : ℝ) + 1) →
      μ (ball x r) ≤ ENNReal.ofReal (r ^ t) := by
  have h' : Tendsto (fun ρ : ℝ => Real.log (μ.real (closedBall x ρ)) / Real.log ρ) (𝓝[>] 0)
      (𝓝 d) := (scale_tendsto_iff _ _).1 h
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (h'.eventually (lt_mem_nhds htd))
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (lt_min (show (0 : ℝ) < u from hu) one_pos)
  refine ⟨k, fun r hr hrk => ?_⟩
  have hr1 : r < 1 := hrk.trans (hk.trans_le (min_le_right _ _))
  have hru : r < u := hrk.trans (hk.trans_le (min_le_left _ _))
  have hlt : t < Real.log (μ.real (closedBall x r)) / Real.log r := hsub ⟨hr, hru⟩
  have hlogr : Real.log r < 0 := Real.log_neg hr hr1
  rw [lt_div_iff_of_neg hlogr] at hlt
  have ha0 : 0 < μ.real (closedBall x r) := by
    rcases (measureReal_nonneg (μ := μ) (s := closedBall x r)).eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero] at hlt
      nlinarith
    · exact h0
  have hle : μ.real (closedBall x r) ≤ r ^ t := by
    rw [Real.rpow_def_of_pos hr]
    calc μ.real (closedBall x r) = Real.exp (Real.log (μ.real (closedBall x r))) :=
          (Real.exp_log ha0).symm
      _ ≤ Real.exp (Real.log r * t) := Real.exp_le_exp.2 (by linarith)
  calc μ (ball x r) ≤ μ (closedBall x r) := measure_mono ball_subset_closedBall
    _ = ENNReal.ofReal (μ.real (closedBall x r)) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (r ^ t) := ENNReal.ofReal_le_ofReal hle

/-- The mass distribution principle for local dimensions: if a probability measure `μ` on `ℝ`
gives no mass to `Kᶜ` and `log μ(B̄(x, r)) / log r → d` as `r → 0⁺` for `μ`-a.e. `x`, then
`dim_H K ≥ d`. -/
theorem ofReal_le_dimH_of_ae_tendsto {μ : Measure ℝ} [IsProbabilityMeasure μ] {K : Set ℝ}
    (hK : μ Kᶜ = 0) {d : ℝ}
    (h : ∀ᵐ x ∂μ, Tendsto (fun r : Scale => logRatio (μ.real (closedBall x r)) r) scaleZero
      (𝓝 d)) :
    ENNReal.ofReal d ≤ dimH K := by
  have key : ∀ t, 0 < t → t < d → ENNReal.ofReal t ≤ dimH K := by
    intro t ht0 htd
    set F : ℕ → Set ℝ := fun k => {x | ∀ r : ℝ, 0 < r → r < 1 / ((k : ℝ) + 1) →
      μ (ball x r) ≤ ENNReal.ofReal (r ^ t)} with hF
    have hcover : ∀ᵐ x ∂μ, ∃ k, x ∈ F k := by
      filter_upwards [h] with x hx
      exact exists_ball_le_rpow ht0 htd hx
    -- some `F k ∩ K` has positive mass
    obtain ⟨k, hk⟩ : ∃ k, 0 < μ (F k ∩ K) := by
      by_contra hcon
      simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
      have h0 : ∀ k, μ (F k) = 0 := fun k => by
        refine le_antisymm ?_ bot_le
        calc μ (F k) ≤ μ (F k ∩ K) + μ (F k \ K) := measure_le_inter_add_sdiff μ _ _
          _ ≤ 0 + μ Kᶜ := add_le_add (hcon k).le (measure_mono fun x hx => hx.2)
          _ = 0 := by rw [hK, add_zero]
      have hU : μ (⋃ k, F k) = 0 := measure_iUnion_null h0
      have hc : μ {x | ¬ ∃ k, x ∈ F k} = 0 := ae_iff.1 hcover
      have hle : μ univ ≤ μ (⋃ k, F k) + μ {x | ¬ ∃ k, x ∈ F k} := by
        refine (measure_mono ?_).trans (measure_union_le _ _)
        intro x _
        by_cases hx : ∃ k, x ∈ F k
        · exact Or.inl (mem_iUnion.2 hx)
        · exact Or.inr hx
      rw [hU, hc, measure_univ, add_zero] at hle
      exact one_ne_zero (le_zero_iff.1 hle)
    -- a uniform ball bound on `F k`, with a large constant for the radii above `1/(k+1)`
    set δ : ℝ := 1 / ((k : ℝ) + 1) with hδ
    have hδ0 : 0 < δ := by positivity
    set C : ℝ≥0 := Real.toNNReal (max 1 (δ ^ (-t))) with hC_def
    have hC : (C : ℝ≥0∞) = ENNReal.ofReal (max 1 (δ ^ (-t))) := rfl
    have hC0 : C ≠ 0 := (Real.toNNReal_pos.2 (lt_max_of_lt_left one_pos)).ne'
    have hC1 : (1 : ℝ≥0∞) ≤ C := by
      rw [hC, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
    have hball : ∀ x ∈ F k ∩ K, ∀ r : ℝ, 0 < r → μ (ball x r) ≤ C * ENNReal.ofReal r ^ t := by
      intro x hx r hr
      rcases lt_or_ge r δ with hlt | hge
      · calc μ (ball x r) ≤ ENNReal.ofReal (r ^ t) := hx.1 r hr hlt
          _ = ENNReal.ofReal r ^ t := (ENNReal.ofReal_rpow_of_pos hr).symm
          _ ≤ C * ENNReal.ofReal r ^ t := le_mul_of_one_le_left' hC1
      · calc μ (ball x r) ≤ μ univ := measure_mono (subset_univ _)
          _ = ENNReal.ofReal (δ ^ (-t) * δ ^ t) := by
              rw [← Real.rpow_add hδ0, neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one,
                measure_univ]
          _ ≤ C * ENNReal.ofReal r ^ t := by
              rw [ENNReal.ofReal_mul (Real.rpow_nonneg hδ0.le _), hC,
                ENNReal.ofReal_rpow_of_pos hr]
              exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _))
                (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hδ0.le hge ht0.le))
    exact ((GeometricMeasureTheory.mass_distribution μ ht0 hC0 hball).2 hk).trans
      (dimH_mono inter_subset_right)
  -- let `t ↑ d`
  rcases le_or_gt d 0 with hd | hd
  · rw [ENNReal.ofReal_of_nonpos hd]
    exact bot_le
  have h0 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Tendsto (fun j : ℕ => d - d / 2 * (1 / ((j : ℝ) + 1))) atTop (𝓝 (d - d / 2 * 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul h0)
  rw [mul_zero, sub_zero] at h1
  have htend : Tendsto (fun j : ℕ => ENNReal.ofReal (d - d / 2 * (1 / ((j : ℝ) + 1)))) atTop
      (𝓝 (ENNReal.ofReal d)) := ENNReal.tendsto_ofReal h1
  refine le_of_tendsto' htend fun j => key _ ?_ ?_
  · have : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
    nlinarith
  · have : 0 < 1 / ((j : ℝ) + 1) := by positivity
    nlinarith

end FractalGeometry.Rapaport.Attractor
