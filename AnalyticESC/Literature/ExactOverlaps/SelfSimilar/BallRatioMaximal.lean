module

public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

set_option maxSynthPendingDepth 3

/-!
A weak estimate for small likelihood ratios over all bounded positive
ball radii. The estimate is with respect to the numerator measure and
uses the actual finite-multiplicity Besicovitch covering theorem.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.BallRatioMaximal`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal

namespace ExactOverlaps

theorem measure_ballRatio_bad_le_of_no_satellite
    {N : ℕ} {τ : ℝ} (hτ : 1 < τ)
    (hN : IsEmpty (Besicovitch.SatelliteConfig ℝ N τ))
    (κ ν : Measure ℝ) (R : ℝ) (t : ℝ≥0∞) :
    κ {x | ∃ r, 0 < r ∧ r ≤ R ∧ κ (closedBall x r) ≤ t * ν (closedBall x r)} ≤
      (N : ℝ≥0∞) * (t * ν univ) := by
  classical
  let E := {x : ℝ | ∃ r, 0 < r ∧ r ≤ R ∧ κ (closedBall x r) ≤ t * ν (closedBall x r)}
  choose r hr using fun x : E ↦ x.property
  let q : Besicovitch.BallPackage E ℝ :=
    { c := fun x ↦ x
      r := r
      rpos := fun x ↦ (hr x).1
      r_bound := R
      r_le := fun x ↦ (hr x).2.1 }
  obtain ⟨A, hdisj, hcover⟩ := Besicovitch.exist_disjoint_covering_families hτ hN q
  have hcount : ∀ i, (A i).Countable := by
    intro i
    apply (hdisj i).countable_of_nonempty_interior
    intro j _
    exact (nonempty_ball.mpr (q.rpos j)).mono ball_subset_interior_closedBall
  have hone : ∀ i, κ (⋃ j ∈ A i, closedBall (q.c j) (q.r j)) ≤ t * ν univ := by
    intro i
    calc
      κ (⋃ j ∈ A i, closedBall (q.c j) (q.r j)) ≤
          ∑' j : A i, κ (closedBall (q.c j) (q.r j)) :=
        measure_biUnion_le κ (hcount i) _
      _ ≤ ∑' j : A i, t * ν (closedBall (q.c j) (q.r j)) := by
        exact ENNReal.tsum_le_tsum (fun j ↦ (hr j.1).2.2)
      _ = t * ∑' j : A i, ν (closedBall (q.c j) (q.r j)) := ENNReal.tsum_mul_left
      _ ≤ t * ν univ := by
        apply mul_le_mul le_rfl _ bot_le bot_le
        apply tsum_measure_le_measure_univ (fun _ ↦ measurableSet_closedBall.nullMeasurableSet)
        exact ((pairwise_subtype_iff_pairwise_set _ _).2 (hdisj i)).aedisjoint
  have hE : E ⊆ ⋃ i : Fin N, ⋃ j ∈ A i, closedBall (q.c j) (q.r j) := by
    intro x hx
    have hh := hcover (show x ∈ range q.c from ⟨⟨x, hx⟩, rfl⟩)
    simp only [mem_iUnion] at hh ⊢
    obtain ⟨i, j, hj, h⟩ := hh
    exact ⟨i, j, hj, ball_subset_closedBall h⟩
  calc
    κ E ≤ κ (⋃ i : Fin N, ⋃ j ∈ A i, closedBall (q.c j) (q.r j)) := measure_mono hE
    _ ≤ ∑' i : Fin N, κ (⋃ j ∈ A i, closedBall (q.c j) (q.r j)) := measure_iUnion_le _
    _ ≤ ∑' _i : Fin N, t * ν univ := ENNReal.tsum_le_tsum hone
    _ = (N : ℝ≥0∞) * (t * ν univ) := by simp

theorem exists_ballRatio_maximal_constant : ∃ N : ℕ, ∀ (κ ν : Measure ℝ) (R : ℝ) (t : ℝ≥0∞),
    κ {x | ∃ r, 0 < r ∧ r ≤ R ∧ κ (closedBall x r) ≤ t * ν (closedBall x r)} ≤
      (N : ℝ≥0∞) * (t * ν univ) := by
  obtain ⟨N, τ, hτ, hN⟩ := HasBesicovitchCovering.no_satelliteConfig (α := ℝ)
  exact ⟨N, measure_ballRatio_bad_le_of_no_satellite hτ hN⟩

end ExactOverlaps
