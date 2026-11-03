module

public import AnalyticESC.Literature.SelfConformal.Coding

@[expose] public section

/-!
# Fibres of the coding map

The disintegration `x ↦ β_x = fibre φ p hp x` of the Bernoulli measure `β` along the coding map
`Π`, as in Section 2.6 of A. Rapaport, *Dimension of self-conformal measures associated to an
exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2 (where `β_ω` denotes
`β_{Π ω}`). The fibres are the conditional kernel of the graph measure
`graphMeasure φ p hp = (Π, id)_* β`. None of these statements needs hypotheses on `φ`: the
coding map is always measurable.

## Main declarations

* `fst_graphMeasure`, `snd_graphMeasure`: the marginals of the graph measure are `μ` and `β`.
* `isProbabilityMeasure_fibre`: every fibre is a probability measure.
* `graphMeasure_apply`, `bernoulli_eq_lintegral_fibre`: `β(s) = ∫ β_x(s) dμ(x)`.
* `ae_fibre_compl_eq_zero`, `ae_ae_fibre_coding_eq`: for `μ`-a.e. `x`, `β_x` is carried by
  `Π⁻¹{x}`.
* `ae_exists_mem_cylinder_coding_eq`: for `μ`-a.e. `x`, every cylinder of positive `β_x`-measure
  contains a point coded to `x`.

Copied from the library `FractalGeometry` (module `FractalGeometry.SelfConformal.Fibre`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.SelfConformal

open MeasureTheory ProbabilityTheory Set Filter Topology
open AnalyticESC (I realComp RapaportHyp IsProbVec)

variable {N : ℕ} {p : Fin N → ℝ}

/-- The graph map `ω ↦ (Π ω, ω)` is measurable. -/
theorem measurable_graph (φ : Fin N → ℝ → ℝ) :
    Measurable fun ω : ℕ → Fin N => (coding φ ω, ω) :=
  (measurable_coding φ).prodMk measurable_id

/-- The graph measure is a probability measure. -/
instance isProbabilityMeasure_graphMeasure' (φ : Fin N → ℝ → ℝ) (hp : IsProbVec p) :
    IsProbabilityMeasure (graphMeasure φ p hp) := by
  unfold graphMeasure
  infer_instance

/-- The first marginal of the graph measure is `μ`. -/
theorem fst_graphMeasure (φ : Fin N → ℝ → ℝ) (hp : IsProbVec p) :
    (graphMeasure φ p hp).fst = selfConformal φ p hp := by
  rw [graphMeasure, Measure.fst, Measure.map_map measurable_fst (measurable_graph φ)]
  rfl

/-- The second marginal of the graph measure is `β`. -/
theorem snd_graphMeasure (φ : Fin N → ℝ → ℝ) (hp : IsProbVec p) :
    (graphMeasure φ p hp).snd = bernoulli p hp := by
  rw [graphMeasure, Measure.snd, Measure.map_map measurable_snd (measurable_graph φ)]
  exact Measure.map_id

variable [NeZero N]

/-- Every fibre is a probability measure. -/
instance isProbabilityMeasure_fibre (φ : Fin N → ℝ → ℝ) (hp : IsProbVec p) (x : ℝ) :
    IsProbabilityMeasure (fibre φ p hp x) := by
  unfold fibre
  infer_instance

/-- The graph measure is `μ ⊗ (x ↦ β_x)`. -/
theorem compProd_fibre (φ : Fin N → ℝ → ℝ) (hp : IsProbVec p) :
    selfConformal φ p hp ⊗ₘ (graphMeasure φ p hp).condKernel = graphMeasure φ p hp := by
  conv_rhs => rw [← Measure.disintegrate (graphMeasure φ p hp) (graphMeasure φ p hp).condKernel]
  rw [fst_graphMeasure]

/-- `ρ(D) = ∫ β_x(D_x) dμ(x)` for the graph measure `ρ` and measurable `D`. -/
theorem graphMeasure_apply (φ : Fin N → ℝ → ℝ) (hp : IsProbVec p)
    {D : Set (ℝ × (ℕ → Fin N))} (hD : MeasurableSet D) :
    graphMeasure φ p hp D = ∫⁻ x, fibre φ p hp x (Prod.mk x ⁻¹' D) ∂selfConformal φ p hp := by
  conv_lhs => rw [← compProd_fibre φ hp]
  rw [Measure.compProd_apply hD]
  rfl

/-- The disintegration `β(s) = ∫ β_x(s) dμ(x)` for measurable `s`. -/
theorem bernoulli_eq_lintegral_fibre (φ : Fin N → ℝ → ℝ) (hp : IsProbVec p)
    {s : Set (ℕ → Fin N)} (hs : MeasurableSet s) :
    bernoulli p hp s = ∫⁻ x, fibre φ p hp x s ∂selfConformal φ p hp := by
  have h : bernoulli p hp s = graphMeasure φ p hp (univ ×ˢ s) := by
    rw [← snd_graphMeasure φ hp, Measure.snd_apply hs, ← Set.univ_prod]
  rw [h, graphMeasure_apply φ hp (MeasurableSet.univ.prod hs)]
  congr 1
  ext x
  congr 1
  ext ω
  simp

/-- For `μ`-a.e. `x`, the fibre `β_x` is carried by `Π⁻¹{x}`. -/
theorem ae_fibre_compl_eq_zero (φ : Fin N → ℝ → ℝ) (hp : IsProbVec p) :
    ∀ᵐ x ∂selfConformal φ p hp, fibre φ p hp x (coding φ ⁻¹' {x})ᶜ = 0 := by
  set D : Set (ℝ × (ℕ → Fin N)) := {q | coding φ q.2 = q.1}ᶜ with hD_def
  have hD : MeasurableSet D :=
    (measurableSet_eq_fun ((measurable_coding φ).comp measurable_snd) measurable_fst).compl
  have h0 : graphMeasure φ p hp D = 0 := by
    rw [graphMeasure, Measure.map_apply (measurable_graph φ) hD]
    exact measure_mono_null (fun ω hω => hω rfl) measure_empty
  have hmeas : Measurable fun x => fibre φ p hp x (Prod.mk x ⁻¹' D) :=
    Kernel.measurable_kernel_prodMk_left hD
  rw [graphMeasure_apply φ hp hD, lintegral_eq_zero_iff hmeas] at h0
  filter_upwards [h0] with x hx
  have hset : Prod.mk x ⁻¹' D = (coding φ ⁻¹' {x})ᶜ := by
    ext ω
    simp [hD_def]
  rw [← hset]
  exact hx

/-- For `μ`-a.e. `x`, `β_x`-a.e. `ω` satisfies `Π ω = x`. -/
theorem ae_ae_fibre_coding_eq (φ : Fin N → ℝ → ℝ) (hp : IsProbVec p) :
    ∀ᵐ x ∂selfConformal φ p hp, ∀ᵐ ω ∂fibre φ p hp x, coding φ ω = x := by
  filter_upwards [ae_fibre_compl_eq_zero φ hp] with x hx
  exact ae_iff.2 hx

/-- For `μ`-a.e. `x`, every cylinder `[u]` with `β_x[u] > 0` contains some `η` with
`Π η = x`. -/
theorem ae_exists_mem_cylinder_coding_eq (φ : Fin N → ℝ → ℝ) (hp : IsProbVec p) :
    ∀ᵐ x ∂selfConformal φ p hp, ∀ (n : ℕ) (u : Fin n → Fin N),
      0 < fibre φ p hp x (cylinder u) → ∃ η ∈ cylinder u, coding φ η = x := by
  filter_upwards [ae_fibre_compl_eq_zero φ hp] with x hx n u hpos
  by_contra hne
  push Not at hne
  have hsub : cylinder u ⊆ (coding φ ⁻¹' {x})ᶜ := fun η hη => hne η hη
  exact hpos.ne' (measure_mono_null hsub hx)

end FractalGeometry.SelfConformal
