module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.BranchDifferentiation
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Support

set_option maxSynthPendingDepth 3

/-!
Measurability of variable-radius ball masses and exact pullback identities
for signed affine similarities. Both signs of a contraction are handled
by its positive absolute multiplier in the radius.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.BranchBalls`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal Topology

namespace ExactOverlaps

theorem measurable_closedBall_measure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure ℝ) [SFinite μ] {c r : Ω → ℝ} (hc : Measurable c) (hr : Measurable r) :
    Measurable (fun x ↦ μ (closedBall (c x) (r x))) := by
  have hs : MeasurableSet {z : Ω × ℝ | dist z.2 (c z.1) ≤ r z.1} :=
    measurableSet_le (measurable_snd.dist (hc.comp measurable_fst)) (hr.comp measurable_fst)
  exact measurable_measure_prodMk_left hs

theorem ae_closedBall_measure_pos (μ : Measure ℝ) :
    ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < μ (closedBall x r) := by
  filter_upwards [μ.support_mem_ae] with x hx
  intro r hr
  exact (μ.mem_support_iff_forall x).mp hx _ (closedBall_mem_nhds x hr)

theorem RealSimilarity.preimage_closedBall_scaled (g : RealSimilarity) (x r : ℝ) :
    g ⁻¹' closedBall (g x) (|g.ratio| * r) = closedBall x r := by
  ext y
  simp only [Set.mem_preimage, mem_closedBall, g.dist_eq]
  exact mul_le_mul_iff_right₀ g.abs_ratio_pos

namespace SelfSimilar.System

variable {ι : Type*} [Fintype ι]

theorem branchMeasure_closedBall_scaled (S : System ι) (ν : Measure ℝ)
    (i : ι) (x r : ℝ) :
    S.branchMeasure ν i (closedBall (S.map i x) (|(S.map i).ratio| * r)) =
      (S.weight i : ℝ≥0∞) * ν (closedBall x r) := by
  rw [branchMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (S.map i).measurable measurableSet_closedBall,
    (S.map i).preimage_closedBall_scaled]

theorem measurable_branchBallInformation (S : System ι) (ν : Measure ℝ)
    [IsFiniteMeasure ν] (i : ι) {Ω : Type*} [MeasurableSpace Ω]
    {r c : Ω → ℝ} (hr : Measurable r) (hc : Measurable c) :
    Measurable (fun x ↦ S.branchBallInformation ν i (r x) (c x)) :=
  (((measurable_closedBall_measure (S.branchMeasure ν i) hc hr).div
    (measurable_closedBall_measure ν hc hr)).ennreal_toReal.log).neg

theorem measurable_branchBallInformation_of_index [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι) (ν : Measure ℝ) [IsFiniteMeasure ν]
    {Ω : Type*} [MeasurableSpace Ω] {i : Ω → ι} {r c : Ω → ℝ}
    (hi : Measurable i) (hr : Measurable r) (hc : Measurable c) :
    Measurable (fun x ↦ S.branchBallInformation ν (i x) (r x) (c x)) := by
  classical
  have heq : (fun x ↦ S.branchBallInformation ν (i x) (r x) (c x)) =
      (fun x ↦ ∑ j : ι, if i x = j then S.branchBallInformation ν j (r x) (c x) else 0) := by
    funext x
    simp
  rw [heq]
  apply Finset.measurable_fun_sum
  intro j _
  exact Measurable.ite (hi (measurableSet_singleton j))
    (S.measurable_branchBallInformation ν j hr hc) measurable_const

end SelfSimilar.System
end ExactOverlaps
