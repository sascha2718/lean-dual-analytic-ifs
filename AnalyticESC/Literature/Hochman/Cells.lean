module

public import AnalyticESC.Literature.SelfConformal.Vocabulary

@[expose] public section

/-!
# Dyadic cells and components on the line

Elementary facts about the dyadic partitions `𝒟_n` of `ℝ` and the raw components `θ_{x,n}` of
the shared vocabulary `FractalGeometry.SelfConformal`, used in the formalisation of Hochman's
entropy growth theorem (Hochman, *On self-similar sets with overlaps and inverse theorems for
entropy*, Ann. of Math. 180 (2014), Section 2.2: components and the identity
`θ = 𝔼_{i=n}(θ_{x,i})`).

## Main declarations

* `measurable_cellIdx`, `mem_cell_iff`, `preimage_cellIdx_singleton`, `measurableSet_cell`,
  `mem_cellOf`, `cellOf_eq_of_mem`, `cellIdx_add`, `cellOf_subset_of_le`, `pairwise_disjoint_cell`:
  the dyadic cells.
* `componentAt`: the component on the cell with a given index, with `component_eq_componentAt`,
  `componentAt_apply`, `isProbabilityMeasure_componentAt`, `componentAt_eq_zero`,
  `componentAt_compl`.
* `component_component`: a component of a component is a component.
* `lintegral_component_apply`, `integral_component_real`: `θ = 𝔼_{i=n}(θ_{x,i})`.
* `measurable_comp_cellIdx`: functions of the cell index are measurable.

Copied from the library `FractalGeometry` (module `FractalGeometry.Hochman.Cells`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Hochman

open MeasureTheory Set FractalGeometry.SelfConformal
open scoped ENNReal

/-! ### Dyadic cells -/

/-- The cell index `x ↦ ⌊2^n x⌋` is measurable. -/
theorem measurable_cellIdx (n : ℕ) : Measurable (cellIdx n) := by
  unfold cellIdx
  fun_prop

/-- A function of the cell index is measurable. -/
theorem measurable_comp_cellIdx {β : Type*} [MeasurableSpace β] (n : ℕ) (F : ℤ → β) :
    Measurable fun x => F (cellIdx n x) :=
  measurable_from_top.comp (measurable_cellIdx n)

/-- `x` lies in the cell with index `k` if and only if its index is `k`. -/
theorem mem_cell_iff {n : ℕ} {k : ℤ} {x : ℝ} : x ∈ cell n k ↔ cellIdx n x = k := by
  have h : (0 : ℝ) < 2 ^ n := by positivity
  rw [cellIdx, Int.floor_eq_iff, cell, mem_Ico, div_le_iff₀ h, lt_div_iff₀ h, mul_comm x]

/-- The fibre of the cell index over `k` is the cell with index `k`. -/
theorem preimage_cellIdx_singleton (n : ℕ) (k : ℤ) : cellIdx n ⁻¹' {k} = cell n k := by
  ext x
  simp [mem_cell_iff]

/-- Dyadic cells are measurable. -/
theorem measurableSet_cell (n : ℕ) (k : ℤ) : MeasurableSet (cell n k) := measurableSet_Ico

/-- Distinct cells of the same level are disjoint. -/
theorem pairwise_disjoint_cell (n : ℕ) : Pairwise (Function.onFun Disjoint (cell n)) := by
  intro k l hkl
  refine Set.disjoint_left.2 fun x hk hl => hkl ?_
  rw [mem_cell_iff] at hk hl
  rw [← hk, ← hl]

/-- A point lies in its own cell. -/
theorem mem_cellOf (n : ℕ) (x : ℝ) : x ∈ cellOf n x := mem_cell_iff.2 rfl

/-- Two points of the same cell have the same cell index. -/
theorem cellIdx_eq_of_mem {n : ℕ} {x y : ℝ} (h : y ∈ cellOf n x) : cellIdx n y = cellIdx n x :=
  mem_cell_iff.1 h

/-- Two points of the same cell have the same cell. -/
theorem cellOf_eq_of_mem {n : ℕ} {x y : ℝ} (h : y ∈ cellOf n x) : cellOf n y = cellOf n x := by
  rw [cellOf, cellOf, cellIdx_eq_of_mem h]

/-- The coarser index is the integer quotient of the finer one:
`⌊2^n x⌋ = ⌊2^{n+p} x⌋ / 2^p`. -/
theorem cellIdx_add (n p : ℕ) (x : ℝ) : cellIdx n x = cellIdx (n + p) x / (2 ^ p : ℕ) := by
  unfold cellIdx
  rw [← Int.floor_div_natCast]
  congr 1
  push_cast
  rw [pow_add]
  field_simp

/-- Finer cells are nested in coarser cells. -/
theorem cellOf_subset_of_le {q j : ℕ} (h : q ≤ j) (x : ℝ) : cellOf j x ⊆ cellOf q x := by
  intro y hy
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [cellOf, mem_cell_iff, cellIdx_add q p y, cellIdx_add q p x, cellIdx_eq_of_mem hy]

/-! ### Components -/

/-- The component `θ_D = θ(D)⁻¹ θ|_D` of `θ` on the level-`n` cell `D` with index `k`. -/
noncomputable def componentAt (θ : Measure ℝ) (n : ℕ) (k : ℤ) : Measure ℝ :=
  (θ (cell n k))⁻¹ • θ.restrict (cell n k)

/-- The component at `x` is the component on the cell of `x`. -/
theorem component_eq_componentAt (θ : Measure ℝ) (n : ℕ) (x : ℝ) :
    component θ n x = componentAt θ n (cellIdx n x) := rfl

/-- The mass of a measurable set under a component. -/
theorem componentAt_apply (θ : Measure ℝ) (n : ℕ) (k : ℤ) {s : Set ℝ} (hs : MeasurableSet s) :
    componentAt θ n k s = (θ (cell n k))⁻¹ * θ (s ∩ cell n k) := by
  rw [componentAt, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]

/-- The component on a cell of positive mass of a finite measure is a probability measure. -/
theorem isProbabilityMeasure_componentAt (θ : Measure ℝ) [IsFiniteMeasure θ] {n : ℕ} {k : ℤ}
    (h : θ (cell n k) ≠ 0) : IsProbabilityMeasure (componentAt θ n k) := by
  refine ⟨?_⟩
  rw [componentAt_apply θ n k MeasurableSet.univ, univ_inter]
  exact ENNReal.inv_mul_cancel h (measure_ne_top θ _)

/-- The component on a null cell is the zero measure. -/
theorem componentAt_eq_zero (θ : Measure ℝ) {n : ℕ} {k : ℤ} (h : θ (cell n k) = 0) :
    componentAt θ n k = 0 := by
  rw [componentAt, Measure.restrict_eq_zero.2 h, smul_zero]

/-- A component is carried by its cell. -/
theorem componentAt_compl (θ : Measure ℝ) (n : ℕ) (k : ℤ) : componentAt θ n k (cell n k)ᶜ = 0 := by
  rw [componentAt_apply θ n k (measurableSet_cell n k).compl, compl_inter_self, measure_empty,
    mul_zero]

/-- A component of a finite measure has total mass at most one. -/
theorem componentAt_univ_le (θ : Measure ℝ) [IsFiniteMeasure θ] (n : ℕ) (k : ℤ) :
    componentAt θ n k univ ≤ 1 := by
  by_cases h : θ (cell n k) = 0
  · rw [componentAt_eq_zero θ h]
    simp
  · have := isProbabilityMeasure_componentAt θ h
    exact prob_le_one

/-- A component of a finite measure is a finite measure. -/
instance isFiniteMeasure_componentAt (θ : Measure ℝ) [IsFiniteMeasure θ] (n : ℕ) (k : ℤ) :
    IsFiniteMeasure (componentAt θ n k) :=
  ⟨(componentAt_univ_le θ n k).trans_lt ENNReal.one_lt_top⟩

/-- A component of a component is a component: for `q ≤ j` and `y` in the level-`q` cell of `x`,
`(θ_{x,q})_{y,j} = θ_{y,j}`. -/
theorem component_component (θ : Measure ℝ) [IsFiniteMeasure θ] {q j : ℕ} (hqj : q ≤ j)
    {x y : ℝ} (hy : y ∈ cellOf q x) (hx : θ (cellOf q x) ≠ 0) :
    component (component θ q x) j y = component θ j y := by
  set C := cellOf q x
  set D := cellOf j y
  have hDC : D ⊆ C := by
    have h := cellOf_subset_of_le hqj y
    rwa [cellOf_eq_of_mem hy] at h
  have hD : MeasurableSet D := measurableSet_cell _ _
  have hC : C = cell q (cellIdx q x) := rfl
  have hcomp : component θ q x = (θ C)⁻¹ • θ.restrict C := rfl
  have hmass : component θ q x D = (θ C)⁻¹ * θ D := by
    rw [hcomp, Measure.smul_apply, Measure.restrict_apply hD, inter_eq_left.2 hDC, smul_eq_mul]
  have hres : (component θ q x).restrict D = (θ C)⁻¹ • θ.restrict D := by
    rw [hcomp, Measure.restrict_smul, Measure.restrict_restrict hD, inter_eq_left.2 hDC]
  change ((component θ q x) D)⁻¹ • (component θ q x).restrict D = (θ D)⁻¹ • θ.restrict D
  rw [hmass, hres, smul_smul]
  by_cases hD0 : θ D = 0
  · rw [Measure.restrict_eq_zero.2 hD0, smul_zero, smul_zero]
  · have hCt : θ C ≠ ⊤ := measure_ne_top θ C
    have hDt : θ D ≠ ⊤ := measure_ne_top θ D
    congr 1
    rw [ENNReal.mul_inv (Or.inr hDt) (Or.inl (ENNReal.inv_ne_top.2 hx)), inv_inv, mul_comm,
      ← mul_assoc, ENNReal.inv_mul_cancel hx hCt, one_mul]

/-! ### The identity `θ = 𝔼_{i=n}(θ_{x,i})` -/

/-- `∫⁻ θ_{x,n}(s) dθ(x) = θ(s)` for a finite measure `θ` and a measurable set `s`: the measure
is the average of its components (Hochman 2014, the lemma closing Section 2.2). -/
theorem lintegral_component_apply (θ : Measure ℝ) [IsFiniteMeasure θ] (n : ℕ) {s : Set ℝ}
    (hs : MeasurableSet s) : ∫⁻ x, component θ n x s ∂θ = θ s := by
  have hmap : ∫⁻ x, component θ n x s ∂θ =
      ∫⁻ k, componentAt θ n k s ∂(θ.map (cellIdx n)) :=
    (lintegral_map (f := fun k => componentAt θ n k s) measurable_from_top
      (measurable_cellIdx n)).symm
  rw [hmap, lintegral_countable']
  have hterm : ∀ k : ℤ, componentAt θ n k s * θ.map (cellIdx n) {k} = θ (s ∩ cell n k) := by
    intro k
    rw [Measure.map_apply (measurable_cellIdx n) (measurableSet_singleton k),
      preimage_cellIdx_singleton, componentAt_apply θ n k hs]
    by_cases h0 : θ (cell n k) = 0
    · rw [measure_mono_null inter_subset_right h0]
      simp
    · rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel h0 (measure_ne_top θ _), one_mul]
  simp_rw [hterm]
  have hsum := tsum_measure_preimage_singleton (μ := θ.restrict s) (s := (univ : Set ℤ))
    countable_univ (f := cellIdx n) (fun k _ => measurable_cellIdx n (measurableSet_singleton k))
  simp only [preimage_univ, Measure.restrict_apply_univ, preimage_cellIdx_singleton,
    Measure.restrict_apply (measurableSet_cell n _)] at hsum
  rw [← hsum, tsum_univ (f := fun k : ℤ => θ (cell n k ∩ s))]
  simp_rw [inter_comm]

/-- A component of a finite measure gives every set mass at most one. -/
theorem component_apply_le_one (θ : Measure ℝ) [IsFiniteMeasure θ] (n : ℕ) (x : ℝ) (s : Set ℝ) :
    component θ n x s ≤ 1 :=
  (measure_mono (subset_univ s)).trans (componentAt_univ_le θ n _)

/-- `∫ θ_{x,n}(s) dθ(x) = θ(s)`, the real form of `lintegral_component_apply`. -/
theorem integral_component_real (θ : Measure ℝ) [IsFiniteMeasure θ] (n : ℕ) {s : Set ℝ}
    (hs : MeasurableSet s) : ∫ x, (component θ n x).real s ∂θ = θ.real s := by
  simp only [Measure.real]
  rw [integral_toReal]
  · rw [lintegral_component_apply θ n hs]
  · exact (measurable_comp_cellIdx n fun k => componentAt θ n k s).aemeasurable
  · exact Filter.Eventually.of_forall fun x =>
      (component_apply_le_one θ n x s).trans_lt ENNReal.one_lt_top

end FractalGeometry.Hochman
