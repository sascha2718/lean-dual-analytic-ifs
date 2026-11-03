module

/-
# Section 2.5: More general Hausdorff measures

The gauge versions `hausdorffDeltaGauge`, `hausdorffContentGauge` and `hausdorffMeasureGauge` of
Definitions 2.1–2.3 are defined in `GeometricMeasureTheory.Hausdorff.Basic`, and Proposition 2.4
(`hausdorff_outer_measures`) is proved there for every gauge. This module contains the mass
distribution principle for a gauge. Its proof uses only monotonicity and countable subadditivity,
so it is stated for an arbitrary outer measure, that is, for any `μ : F` with
`[FunLike F (Set X) ℝ≥0∞] [MeasureTheory.OuterMeasureClass F X]`; a `MeasureTheory.Measure X` and a
`MeasureTheory.OuterMeasure X` are both such an `F`.

| Notes | Lean declaration | Location |
|---|---|---|
| `𝓗^g_δ`, `𝓗^g`, `𝓗^g_∞` | `hausdorffDeltaGauge`, `hausdorffMeasureGauge`, `hausdorffContentGauge` | `GeometricMeasureTheory.Hausdorff.Basic` |
| A constant factor in the gauge | `hausdorffContentGauge_const_mul` | here |
| Mass distribution for a gauge | `mass_distribution_gauge` | here |
-/

public import AnalyticESC.Literature.GeometricMeasureTheory.Hausdorff.Basic

@[expose] public section

/-!
Copied from the library `FractalGeometry` (module `GeometricMeasureTheory.Hausdorff.GeneralGauges`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [EMetricSpace X]

/-- A constant factor in the gauge comes out of the content: `𝓗^{c g}_∞(E) = c 𝓗^g_∞(E)` whenever
`c ≠ 0` and `c ≠ ∞`. -/
theorem hausdorffContentGauge_const_mul (g : ℝ≥0∞ → ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ 0) (hctop : c ≠ ∞)
    (E : Set X) :
    hausdorffContentGauge (fun t => c * g t) E = c * hausdorffContentGauge g E := by
  have hweight : ∀ U : Set X, gaugeWeight (fun t => c * g t) U = c * gaugeWeight g U := fun U => by
    rw [gaugeWeight, gaugeWeight, ENNReal.mul_iSup]
  simp only [hausdorffContentGauge, hweight, ENNReal.tsum_mul_left,
    ENNReal.mul_iInf_of_ne hc hctop]

/-- The mass distribution principle for a gauge (Section 2.5), for an arbitrary outer measure `μ`:
if `μ(U) ≤ C g(|U|)` for every open set `U` meeting `E`, then `𝓗^g_∞(E) ≥ μ(E) / C`. -/
theorem mass_distribution_gauge {F : Type*} [FunLike F (Set X) ℝ≥0∞] [OuterMeasureClass F X]
    (μ : F) (g : ℝ≥0∞ → ℝ≥0∞) {C : ℝ≥0} (hC : C ≠ 0) {E : Set X}
    (hU : ∀ U : Set X, IsOpen U → (U ∩ E).Nonempty → μ U ≤ C * g (ediam U)) :
    μ E / C ≤ hausdorffContentGauge g E := by
  refine le_iInf fun U => le_iInf fun hUo => le_iInf fun hEU => ?_
  have hCtop : (C : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  rw [ENNReal.div_le_iff (ENNReal.coe_ne_zero.2 hC) hCtop, mul_comm, ← ENNReal.tsum_mul_left]
  have hE : E ⊆ ⋃ i, U i ∩ E := by
    rw [← iUnion_inter]
    exact subset_inter hEU subset_rfl
  refine (measure_mono hE).trans ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun i => ?_))
  rcases (U i ∩ E).eq_empty_or_nonempty with h | h
  · simp [h]
  · calc
      μ (U i ∩ E) ≤ μ (U i) := measure_mono inter_subset_left
      _ ≤ C * g (ediam (U i)) := hU (U i) (hUo i) h
      _ = C * gaugeWeight g (U i) := by rw [gaugeWeight, iSup_pos h.left]

end GeometricMeasureTheory
