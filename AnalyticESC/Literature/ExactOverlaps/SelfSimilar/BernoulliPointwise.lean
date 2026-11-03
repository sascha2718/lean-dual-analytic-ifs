module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.BernoulliCylinder
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.BernoulliApproximation
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.AverageApproximation

set_option maxSynthPendingDepth 3

/-!
Pointwise averaging for every integrable measurable real observable on a
finite-alphabet Bernoulli space. Finite-prefix conditional expectations
give L1 approximation; independent-block strong laws and the proved Hopf
maximal inequality transfer the limit to the original observable.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.BernoulliPointwise`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace ExactOverlaps.Bernoulli

variable {A : Type*} [MeasurableSpace A] [Fintype A]

/-- The almost-sure pointwise averaging theorem for a finite Bernoulli shift. -/
theorem ae_tendsto_birkhoffAverage (p : Measure A) [IsProbabilityMeasure p]
    {f : (ℕ → A) → ℝ} (hfm : Measurable f) (hf : Integrable f (sequenceLaw p)) :
    ∀ᵐ ω ∂sequenceLaw p, Tendsto (fun n ↦ birkhoffAverage ℝ shift f n ω)
      atTop (𝓝 (∫ v, f v ∂sequenceLaw p)) := by
  let η : ℕ → ℝ := fun m ↦ (1 / 2 : ℝ) ^ m
  have hη : ∀ m, 0 < η m := fun m ↦ pow_pos (by norm_num) m
  have hηsum : (∑' m, ENNReal.ofReal (η m)) ≠ ⊤ :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).tsum_ofReal_ne_top
  have hηlim : Tendsto η atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have happ : ∀ m, ∃ k, (∫ ω, |f ω - ((sequenceLaw p)[f | prefixFiltration k]) ω|
      ∂sequenceLaw p) ≤ (η m) ^ 2 := by
    intro m
    obtain ⟨k, hk⟩ := ((prefix_condExp_error_tendsto p hfm hf).eventually
      (gt_mem_nhds (sq_pos_of_pos (hη m)))).exists
    exact ⟨k, hk.le⟩
  choose k hk using happ
  let g : ℕ → (ℕ → A) → ℝ := fun m ↦ (sequenceLaw p)[f | prefixFiltration (k m)]
  have hgm : ∀ m, Measurable (g m) := fun m ↦
    (stronglyMeasurable_condExp.mono (prefixFiltration.le (k m))).measurable
  have hg : ∀ m, Integrable (g m) (sequenceLaw p) := fun _ ↦ integrable_condExp
  have hconv : ∀ m, ∀ᵐ ω ∂sequenceLaw p, Tendsto
      (fun n ↦ birkhoffAverage ℝ shift (g m) n ω)
      atTop (𝓝 (∫ v, g m v ∂sequenceLaw p)) := by
    intro m
    obtain ⟨G, hG, heq⟩ := prefix_condExp_factors p f (k m)
    change ∀ᵐ ω ∂sequenceLaw p, Tendsto
      (fun n ↦ birkhoffAverage ℝ shift ((sequenceLaw p)[f | prefixFiltration (k m)]) n ω)
      atTop (𝓝 (∫ v, ((sequenceLaw p)[f | prefixFiltration (k m)]) v ∂sequenceLaw p))
    rw [heq]
    exact finite_alphabet_cylinder_average p (Nat.succ_pos _) G hG
  exact Ergodic.ae_tendsto_birkhoffAverage_of_fast_approximation
    (measurePreserving_shift p) hfm hf g hgm hg η hη hηsum hηlim hk hconv

end ExactOverlaps.Bernoulli
