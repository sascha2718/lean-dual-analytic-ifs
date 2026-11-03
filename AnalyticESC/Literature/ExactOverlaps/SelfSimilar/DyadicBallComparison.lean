module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.NeighborMass

set_option maxSynthPendingDepth 3

/-!
Comparison of a point's dyadic cell with a ball of the same radius. The
ball meets at most three adjacent cells. The preceding mass estimate then
compares cell and ball masses almost surely up to any summable relative
error, including points lying on grid boundaries.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.DyadicBallComparison`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace ExactOverlaps.Entropy

theorem dyadic_scale_mul_radius (i : ℤ) : (2 : ℝ) ^ i * (2 : ℝ) ^ (-i) = 1 := by
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  simp

theorem dyadicCell_subset_closedBall (i : ℤ) (x : ℝ) :
    dyadicCell i (dyadicQuantize i x) ⊆ closedBall x ((2 : ℝ) ^ (-i)) := by
  intro y hy
  have hx : x ∈ dyadicCell i (dyadicQuantize i x) := rfl
  obtain ⟨hxlo, hxhi⟩ := (mem_dyadicCell_iff i _ x).mp hx
  obtain ⟨hylo, hyhi⟩ := (mem_dyadicCell_iff i _ y).mp hy
  have hscaled : |(2 : ℝ) ^ i * y - (2 : ℝ) ^ i * x| < 1 :=
    abs_lt.mpr ⟨by linarith, by linarith⟩
  rw [← mul_sub, abs_mul, abs_of_pos (dyadic_scale_pos i)] at hscaled
  rw [mem_closedBall, Real.dist_eq]
  apply (mul_le_mul_iff_right₀ (dyadic_scale_pos i)).mp
  rw [dyadic_scale_mul_radius]
  exact hscaled.le

theorem closedBall_subset_three_dyadicCells (i : ℤ) (x : ℝ) :
    closedBall x ((2 : ℝ) ^ (-i)) ⊆
      (dyadicCell i (dyadicQuantize i x - 1) ∪ dyadicCell i (dyadicQuantize i x)) ∪
        dyadicCell i (dyadicQuantize i x + 1) := by
  intro y hy
  have hd : |y - x| ≤ (2 : ℝ) ^ (-i) := by
    simpa only [mem_closedBall, Real.dist_eq] using hy
  have hs : |(2 : ℝ) ^ i * y - (2 : ℝ) ^ i * x| ≤ 1 := by
    rw [← mul_sub, abs_mul, abs_of_pos (dyadic_scale_pos i)]
    simpa only [dyadic_scale_mul_radius] using
      mul_le_mul_of_nonneg_left hd (dyadic_scale_pos i).le
  have hxlo := Int.floor_le ((2 : ℝ) ^ i * x)
  have hxhi := Int.lt_floor_add_one ((2 : ℝ) ^ i * x)
  have hylo := Int.floor_le ((2 : ℝ) ^ i * y)
  have hyhi := Int.lt_floor_add_one ((2 : ℝ) ^ i * y)
  obtain ⟨hlo, hhi⟩ := abs_le.mp hs
  have hlowReal : (dyadicQuantize i x : ℝ) - 2 < (dyadicQuantize i y : ℝ) := by
    dsimp [dyadicQuantize]
    linarith
  have huppReal : (dyadicQuantize i y : ℝ) < (dyadicQuantize i x : ℝ) + 2 := by
    dsimp [dyadicQuantize]
    linarith
  have hl : dyadicQuantize i x - 2 < dyadicQuantize i y := by exact_mod_cast hlowReal
  have hu : dyadicQuantize i y < dyadicQuantize i x + 2 := by exact_mod_cast huppReal
  have he : dyadicQuantize i y = dyadicQuantize i x - 1 ∨
      dyadicQuantize i y = dyadicQuantize i x ∨
      dyadicQuantize i y = dyadicQuantize i x + 1 := by omega
  simpa only [dyadicCell, mem_union, mem_ofPred_eq, or_assoc] using he

theorem closedBall_mass_le_neighborMass (μ : ProbabilityMeasure ℝ) (i : ℤ) (x : ℝ) :
    (μ : Measure ℝ) (closedBall x ((2 : ℝ) ^ (-i))) ≤
      neighborMass (dyadicLaw μ i) (dyadicQuantize i x) := by
  calc
    (μ : Measure ℝ) (closedBall x ((2 : ℝ) ^ (-i))) ≤
        (μ : Measure ℝ) ((dyadicCell i (dyadicQuantize i x - 1) ∪
          dyadicCell i (dyadicQuantize i x)) ∪ dyadicCell i (dyadicQuantize i x + 1)) :=
      measure_mono (closedBall_subset_three_dyadicCells i x)
    _ ≤ ((μ : Measure ℝ) (dyadicCell i (dyadicQuantize i x - 1)) +
          (μ : Measure ℝ) (dyadicCell i (dyadicQuantize i x))) +
          (μ : Measure ℝ) (dyadicCell i (dyadicQuantize i x + 1)) := by
      exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ = neighborMass (dyadicLaw μ i) (dyadicQuantize i x) := by
      simp only [neighborMass, dyadicLaw_apply]

theorem ae_eventually_cell_ball_mass_bounds (μ : ProbabilityMeasure ℝ)
    (t : ℕ → ℝ≥0∞) (ht : (∑' n, 3 * t n) ≠ ⊤) :
    ∀ᵐ x ∂(μ : Measure ℝ), ∀ᶠ n : ℕ in atTop,
      t n * (μ : Measure ℝ) (closedBall x ((2 : ℝ) ^ (-(n : ℤ)))) <
          dyadicLaw μ n (dyadicQuantize n x) ∧
        dyadicLaw μ n (dyadicQuantize n x) ≤
          (μ : Measure ℝ) (closedBall x ((2 : ℝ) ^ (-(n : ℤ)))) := by
  filter_upwards [ae_eventually_cell_mass_gt_neighbor_fraction μ t ht] with x hx
  filter_upwards [hx] with n hn
  constructor
  · apply lt_of_le_of_lt _ hn
    gcongr
    exact closedBall_mass_le_neighborMass μ n x
  · rw [dyadicLaw_apply]
    exact measure_mono (dyadicCell_subset_closedBall n x)

end ExactOverlaps.Entropy
