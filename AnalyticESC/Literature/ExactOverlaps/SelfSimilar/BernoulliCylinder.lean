module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.BernoulliBlocks
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.BlockAverages
public import Mathlib.Dynamics.BirkhoffSum.Average

set_option maxSynthPendingDepth 3

/-!
Almost-sure orbit averaging for finite-coordinate observables on a finite
alphabet Bernoulli space. Each residue class uses independent disjoint
blocks; the elementary completed-block estimate then gives all times.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.BernoulliCylinder`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace ExactOverlaps.Bernoulli

variable {A : Type*} [MeasurableSpace A]

omit [MeasurableSpace A] in
theorem block_zero_shift_iterate (m k : ℕ) (ω : ℕ → A) :
    block m 0 (shift^[k] ω) = block m k ω := by
  ext j
  simp only [block, zero_add, shift_iterate, Nat.add_comm]

theorem integral_block (p : Measure A) [IsProbabilityMeasure p]
    (m a : ℕ) (g : (Fin m → A) → ℝ)
    (hg : Integrable g (Measure.pi (fun _ : Fin m ↦ p))) :
    (∫ ω, g (block m a ω) ∂sequenceLaw p) =
      ∫ y, g y ∂Measure.pi (fun _ : Fin m ↦ p) := by
  have hmap : AEStronglyMeasurable g ((sequenceLaw p).map (block m a)) := by
    rw [block_map]
    exact hg.aestronglyMeasurable
  rw [← block_map p m a, integral_map (measurable_block _ _).aemeasurable hmap]

theorem ae_tendsto_cylinder_average (p : Measure A) [IsProbabilityMeasure p]
    {m : ℕ} (hm : 0 < m) (g : (Fin m → A) → ℝ)
    (hgm : Measurable g) (hg : Integrable g (Measure.pi (fun _ : Fin m ↦ p)))
    {C : ℝ} (hC : ∀ y, |g y| ≤ C) :
    ∀ᵐ ω ∂sequenceLaw p, Tendsto
      (fun n ↦ birkhoffAverage ℝ shift (fun v ↦ g (block m 0 v)) n ω)
      atTop (𝓝 (∫ v, g (block m 0 v) ∂sequenceLaw p)) := by
  have hall := ae_all_iff.2 (fun r : ℕ ↦ strongLaw_block p hm r g hgm hg)
  filter_upwards [hall] with ω hω
  have h := Ergodic.tendsto_cesaro_of_residue_classes
    (fun k ↦ g (block m k ω)) hm (fun k ↦ hC _) (fun r _ ↦ hω r)
  rw [integral_block p m 0 g hg]
  convert h using 1
  ext n
  simp only [birkhoffAverage, smul_eq_mul, birkhoffSum,
    block_zero_shift_iterate, div_eq_inv_mul]

theorem finite_alphabet_cylinder_average [Fintype A]
    (p : Measure A) [IsProbabilityMeasure p] {m : ℕ} (hm : 0 < m)
    (g : (Fin m → A) → ℝ) (hgm : Measurable g) :
    ∀ᵐ ω ∂sequenceLaw p, Tendsto
      (fun n ↦ birkhoffAverage ℝ shift (fun v ↦ g (block m 0 v)) n ω)
      atTop (𝓝 (∫ v, g (block m 0 v) ∂sequenceLaw p)) := by
  obtain ⟨C, hC⟩ := (Set.finite_range (fun y : Fin m → A ↦ |g y|)).bddAbove
  have hg : Integrable g (Measure.pi (fun _ : Fin m ↦ p)) := by
    apply Integrable.of_bound hgm.aestronglyMeasurable C
    exact ae_of_all _ (fun y ↦ by simpa only [Real.norm_eq_abs] using hC ⟨y, rfl⟩)
  exact ae_tendsto_cylinder_average p hm g hgm hg (fun y ↦ hC ⟨y, rfl⟩)

end ExactOverlaps.Bernoulli
