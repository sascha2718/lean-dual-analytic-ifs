module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.Definitions
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

set_option maxSynthPendingDepth 3

/-!
The Radon--Nikodym probabilities of the branches conditioned on the image
point. Stationarity proves their absolute continuity and that the actual
densities sum to one almost everywhere, even for overlapping branches.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.BranchDensity`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ExactOverlaps

theorem rnDeriv_finsetSum {Ω ι : Type*} [MeasurableSpace Ω]
    (κ : ι → Measure Ω) (ν : Measure Ω) [∀ i, IsFiniteMeasure (κ i)] [IsFiniteMeasure ν]
    (s : Finset ι) :
    (∑ i ∈ s, κ i).rnDeriv ν =ᵐ[ν] fun x ↦ ∑ i ∈ s, (κ i).rnDeriv ν x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      filter_upwards [Measure.rnDeriv_zero ν] with x hx
      exact hx
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Measure.rnDeriv_add' (κ i) (∑ j ∈ s, κ j) ν, ih] with x hx hix
      simpa only [Pi.add_apply, hix] using hx

namespace SelfSimilar.System

variable {ι : Type*} [Fintype ι]

noncomputable def branchMeasure (S : System ι) (ν : Measure ℝ) (i : ι) : Measure ℝ :=
  (S.weight i : ℝ≥0∞) • ν.map (S.map i)

instance (S : System ι) (ν : Measure ℝ) [IsFiniteMeasure ν] (i : ι) :
    IsFiniteMeasure (S.branchMeasure ν i) := by
  unfold branchMeasure
  change IsFiniteMeasure (S.weight i • ν.map (S.map i))
  have := Measure.isFiniteMeasure_map ν (S.map i)
  infer_instance

theorem branchMeasure_le (S : System ι) {ν : Measure ℝ} (hν : S.IsStationary ν) (i : ι) :
    S.branchMeasure ν i ≤ ν := by
  calc
    S.branchMeasure ν i ≤ ∑ j, S.branchMeasure ν j :=
      Finset.single_le_sum (fun j _ ↦ bot_le) (Finset.mem_univ i)
    _ = ν := hν.symm

theorem branchMeasure_absolutelyContinuous (S : System ι) {ν : Measure ℝ}
    (hν : S.IsStationary ν) (i : ι) : S.branchMeasure ν i ≪ ν :=
  Measure.absolutelyContinuous_of_le (S.branchMeasure_le hν i)

noncomputable def branchDensity (S : System ι) (ν : Measure ℝ) (i : ι) : ℝ → ℝ≥0∞ :=
  (S.branchMeasure ν i).rnDeriv ν

theorem measurable_branchDensity (S : System ι) (ν : Measure ℝ) (i : ι) :
    Measurable (S.branchDensity ν i) := Measure.measurable_rnDeriv _ _

theorem branchDensity_le_one (S : System ι) {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : S.IsStationary ν) (i : ι) : ∀ᵐ x ∂ν, S.branchDensity ν i x ≤ 1 := by
  exact Measure.rnDeriv_le_one_of_le (S.branchMeasure_le hν i)

theorem withDensity_branchDensity (S : System ι) {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : S.IsStationary ν) (i : ι) : ν.withDensity (S.branchDensity ν i) = S.branchMeasure ν i :=
  Measure.withDensity_rnDeriv_eq _ _ (S.branchMeasure_absolutelyContinuous hν i)

theorem sum_branchDensity (S : System ι) {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : S.IsStationary ν) : ∀ᵐ x ∂ν, ∑ i, S.branchDensity ν i x = 1 := by
  have hsum : (∑ i, S.branchMeasure ν i) = ν := hν.symm
  have h := rnDeriv_finsetSum (S.branchMeasure ν) ν Finset.univ
  rw [hsum] at h
  exact h.symm.trans ν.rnDeriv_self

end SelfSimilar.System
end ExactOverlaps
