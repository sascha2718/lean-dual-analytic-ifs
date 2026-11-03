module

/-
# Section 1: Basic measure theory

Section 1 of the lecture notes *Geometric Measure Theory: Dynamics and Randomness* (HT2026,
Uppsala University): outer measures, Carathéodory measurability, regularity, the metric criterion
for Borel measurability, and weak convergence of finite measures.

The results appear below in the order of the notes. A result that Mathlib already contains is
recorded with its Mathlib declaration and file, and an `example` states it in the form of the notes
and checks it against that declaration. The remaining results are proved here.

| Notes | Lean declaration | Location |
|---|---|---|
| Definition 1.1 (outer measure) | `IsOuterMeasure`; bundled as `MeasureTheory.OuterMeasure` | here; `Mathlib/MeasureTheory/OuterMeasure/Defs.lean` |
| Definition 1.2 (measure) | `MeasureTheory.Measure` | `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean` |
| Definition 1.3 (measurability) | `MeasureTheory.OuterMeasure.IsCaratheodory` | `Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean` |
| Proposition 1.4(1) | `MeasureTheory.OuterMeasure.caratheodory` | `Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean` |
| Proposition 1.4(2) | `basic_measure_properties_null` | here |
| Proposition 1.4(3) | `MeasureTheory.OuterMeasure.f_iUnion` | `Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean` |
| Proposition 1.4(4) | `MeasureTheory.tendsto_measure_iUnion_atTop`, `MeasureTheory.tendsto_measure_iInter_atTop` | `Mathlib/MeasureTheory/Measure/MeasureSpace.lean` |
| Definition 1.5 (regular, Borel, Borel regular, Radon) | `MeasureTheory.measure_toMeasurable`, `MeasureTheory.le_toOuterMeasure_caratheodory`, `MeasureTheory.Measure.Regular`, `MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure` | `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`, `Mathlib/MeasureTheory/Measure/MeasureSpace.lean`, `Mathlib/MeasureTheory/Measure/Regular.lean` |
| Theorem 1.6 (Carathéodory) | `metric_criterion` | here; the direction metric ⇒ Borel is `MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory` in `Mathlib/MeasureTheory/Measure/Hausdorff.lean` |
| Theorem 1.7 (Portmanteau) | `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`, `MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto`, `MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`, `MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto`, `MeasureTheory.limsup_measure_closed_le_iff_liminf_measure_open_ge`, `MeasureTheory.tendsto_of_forall_isOpen_le_liminf'` | `Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean`, `Mathlib/MeasureTheory/Measure/Portmanteau.lean` |
| Theorem 1.8 (weak compactness) | `weak_compactness` | here; compactness of mass-bounded finite measures is `isCompact_setOf_finiteMeasure_le_of_compactSpace` in `Mathlib/MeasureTheory/Measure/Prokhorov.lean` |
| Open-set inequality after Theorem 1.8 | `le_liminf_measure_open_of_tendsto` | here |
-/

public import Mathlib

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

/-! ## Outer measures, measures and measurability 

Copied from the library `FractalGeometry` (module `GeometricMeasureTheory.BasicMeasureTheory`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

/-- Definition 1.1 (`def:outer-measure`): `m` is an outer measure on `α` if it vanishes on the empty
set, is monotone, and is countably subadditive. Mathlib bundles outer measures as
`MeasureTheory.OuterMeasure`; `IsOuterMeasure.toOuterMeasure` passes to the bundled form. -/
structure IsOuterMeasure {α : Type*} (m : Set α → ℝ≥0∞) : Prop where
  empty : m ∅ = 0
  mono : ∀ ⦃A B : Set α⦄, A ⊆ B → m A ≤ m B
  iUnion_le : ∀ A : ℕ → Set α, m (⋃ i, A i) ≤ ∑' i, m (A i)

/-- The bundled outer measure of a set function satisfying Definition 1.1. -/
def IsOuterMeasure.toOuterMeasure {α : Type*} {m : Set α → ℝ≥0∞} (h : IsOuterMeasure m) :
    OuterMeasure α where
  measureOf := m
  empty := h.empty
  mono := fun hAB => h.mono hAB
  iUnion_nat := fun A _ => h.iUnion_le A

@[simp]
theorem IsOuterMeasure.coe_toOuterMeasure {α : Type*} {m : Set α → ℝ≥0∞}
    (h : IsOuterMeasure m) : ⇑h.toOuterMeasure = m :=
  rfl

/-- Every bundled outer measure satisfies Definition 1.1. -/
theorem isOuterMeasure_outerMeasure {α : Type*} (μ : OuterMeasure α) : IsOuterMeasure μ :=
  ⟨measure_empty, fun _ _ h => measure_mono h, fun A => measure_iUnion_le A⟩

/-! Definition 1.2 (`def:measure`) is Mathlib's `MeasureTheory.Measure`, in
`Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`.

Definition 1.3 (`def:measurability`) is `MeasureTheory.OuterMeasure.IsCaratheodory`, in
`Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean`. -/

example {α : Type*} (μ : OuterMeasure α) (A : Set α) :
    μ.IsCaratheodory A ↔ ∀ B : Set α, μ B = μ (B ∩ A) + μ (B \ A) :=
  Iff.rfl

/-! ## Proposition 1.4 (`thm:basic-measure-properties`)

Part (1): the Carathéodory-measurable sets form the σ-algebra
`MeasureTheory.OuterMeasure.caratheodory`. -/

example {α : Type*} (μ : OuterMeasure α) (A : Set α) :
    MeasurableSet[μ.caratheodory] A ↔ μ.IsCaratheodory A :=
  Iff.rfl

/-- Proposition 1.4(2) (`thm:basic-measure-properties`): a set of outer measure zero is
measurable. -/
theorem basic_measure_properties_null {α : Type*} (μ : OuterMeasure α) {A : Set α}
    (hA : μ A = 0) : μ.IsCaratheodory A := by
  refine μ.isCaratheodory_iff_le.2 fun B => ?_
  rw [measure_mono_null inter_subset_right hA, zero_add]
  exact measure_mono sdiff_subset

/-! Part (3): countable additivity on disjoint measurable sets is
`MeasureTheory.OuterMeasure.f_iUnion`. -/

example {α : Type*} (μ : OuterMeasure α) {A : ℕ → Set α} (hA : ∀ i, μ.IsCaratheodory (A i))
    (hd : Pairwise (Function.onFun Disjoint A)) : μ (⋃ i, A i) = ∑' i, μ (A i) :=
  μ.f_iUnion hA hd

/-! Part (4): continuity along monotone sequences is
`MeasureTheory.tendsto_measure_iUnion_atTop` and `MeasureTheory.tendsto_measure_iInter_atTop`,
applied to the measure `μ.toMeasure le_rfl` on the σ-algebra `μ.caratheodory`, which agrees with
`μ` on measurable sets by `MeasureTheory.toMeasure_apply`. -/

example {α : Type*} (μ : OuterMeasure α) {A : ℕ → Set α} (hA : ∀ i, μ.IsCaratheodory (A i))
    (hmono : Monotone A) : Tendsto (fun i => μ (A i)) atTop (𝓝 (μ (⋃ i, A i))) := by
  letI : MeasurableSpace α := μ.caratheodory
  have hA' : ∀ i, MeasurableSet (A i) := hA
  have h := tendsto_measure_iUnion_atTop (μ := μ.toMeasure le_rfl) hmono
  rwa [toMeasure_apply _ _ (MeasurableSet.iUnion hA'), Function.comp_def,
    funext fun i => toMeasure_apply _ _ (hA' i)] at h

example {α : Type*} (μ : OuterMeasure α) {A : ℕ → Set α} (hA : ∀ i, μ.IsCaratheodory (A i))
    (hanti : Antitone A) (hfin : μ (A 0) ≠ ∞) :
    Tendsto (fun i => μ (A i)) atTop (𝓝 (μ (⋂ i, A i))) := by
  letI : MeasurableSpace α := μ.caratheodory
  have hA' : ∀ i, MeasurableSet (A i) := hA
  have h := tendsto_measure_iInter_atTop (μ := μ.toMeasure le_rfl)
    (fun i => (hA' i).nullMeasurableSet) hanti ⟨0, by rwa [toMeasure_apply _ _ (hA' 0)]⟩
  rwa [toMeasure_apply _ _ (MeasurableSet.iInter hA'), Function.comp_def,
    funext fun i => toMeasure_apply _ _ (hA' i)] at h

/-! ## Definition 1.5 (`def:measure-regularity`)

Mathlib's measures are defined on a σ-algebra and extended to all sets through measurable hulls.
Every `MeasureTheory.Measure` is therefore regular in the sense of part (1)
(`MeasureTheory.measurableSet_toMeasurable`, `MeasureTheory.subset_toMeasurable`,
`MeasureTheory.measure_toMeasurable`), a measure on the Borel σ-algebra is Borel
(`MeasureTheory.le_toOuterMeasure_caratheodory`) and Borel regular, and a Radon measure is a
`MeasureTheory.Measure.Regular` measure on the Borel σ-algebra
(`Mathlib/MeasureTheory/Measure/Regular.lean`): finite on compact sets, outer regular, and inner
regular on open sets with respect to compact sets. -/

example {X : Type*} [MeasurableSpace X] (μ : Measure X) (A : Set X) :
    ∃ B, MeasurableSet B ∧ A ⊆ B ∧ μ B = μ A :=
  ⟨toMeasurable μ A, measurableSet_toMeasurable μ A, subset_toMeasurable μ A,
    measure_toMeasurable A⟩

example {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) :
    borel X ≤ μ.toOuterMeasure.caratheodory := by
  rw [← BorelSpace.measurable_eq]
  exact le_toOuterMeasure_caratheodory μ

/-! The examples after Definition 1.5: Lebesgue measure and Dirac measures are Radon. Both are
locally finite measures on σ-compact metric spaces, hence regular by
`MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`. -/

example (d : ℕ) : (volume : Measure (Fin d → ℝ)).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

example {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X] (x : X) :
    (Measure.dirac x).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

/-! ## Theorem 1.6 (`thm:metric-criterion`) -/

/-- Theorem 1.6 (Carathéodory, `thm:metric-criterion`): an outer measure on a metric space is Borel
if and only if it is additive on positively separated sets. Mathlib's
`MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory` is the direction from right to left. -/
theorem metric_criterion {X : Type*} [EMetricSpace X] (μ : OuterMeasure X) :
    borel X ≤ μ.caratheodory ↔ μ.IsMetric := by
  refine ⟨fun h A B hAB => ?_, fun h => h.borel_le_caratheodory⟩
  obtain ⟨r, hr, hrAB⟩ := hAB
  -- The open set `U` of points at distance less than `r` from `A` contains `A` and misses `B`.
  set U := {x | Metric.infEDist x A < r}
  have hU : μ.IsCaratheodory U :=
    h U (MeasurableSpace.measurableSet_generateFrom
      (isOpen_lt Metric.continuous_infEDist continuous_const))
  have hAU : A ⊆ U := fun x hx => by
    simp [U, Metric.infEDist_zero_of_mem hx, pos_iff_ne_zero.2 hr]
  have hBU : ∀ y ∈ B, y ∉ U := fun y hy => by
    simp only [U, mem_setOf_eq, not_lt]
    exact Metric.le_infEDist.2 fun x hx => edist_comm x y ▸ hrAB x hx y hy
  rw [hU (A ∪ B)]
  congr 2
  · ext x
    constructor
    · rintro ⟨hx | hx, hxU⟩
      · exact hx
      · exact absurd hxU (hBU x hx)
    · exact fun hx => ⟨Or.inl hx, hAU hx⟩
  · ext x
    constructor
    · rintro ⟨hx | hx, hxU⟩
      · exact absurd (hAU hx) hxU
      · exact hx
    · exact fun hx => ⟨Or.inr hx, hBU x hx⟩

/-! ## Weak convergence

Theorem 1.7 (Portmanteau, `thm:portmanteau`) is in `Mathlib/MeasureTheory/Measure/Portmanteau.lean`;
the topology on `MeasureTheory.ProbabilityMeasure` is the topology of weak convergence. -/

example {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X) :
    List.TFAE [
      ∀ f : BoundedContinuousFunction X ℝ,
        Tendsto (fun n => ∫ x, f x ∂(μs n : Measure X)) atTop (𝓝 (∫ x, f x ∂(μ : Measure X))),
      ∀ f : X → ℝ, (∃ C, ∀ x y, dist (f x) (f y) ≤ C) → (∃ L, LipschitzWith L f) →
        Tendsto (fun n => ∫ x, f x ∂(μs n : Measure X)) atTop (𝓝 (∫ x, f x ∂(μ : Measure X))),
      ∀ F : Set X, IsClosed F →
        limsup (fun n => (μs n : Measure X) F) atTop ≤ (μ : Measure X) F,
      ∀ U : Set X, IsOpen U →
        (μ : Measure X) U ≤ liminf (fun n => (μs n : Measure X) U) atTop] := by
  tfae_have 1 ↔ 2 :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.symm.trans
      tendsto_iff_forall_lipschitz_integral_tendsto
  tfae_have 1 → 3 := fun h F hF =>
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 h) hF
  tfae_have 3 → 4 := limsup_measure_closed_le_iff_liminf_measure_open_ge.1
  tfae_have 4 → 1 := fun h => ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    (tendsto_of_forall_isOpen_le_liminf' h)
  tfae_finish

/-- Theorem 1.8 (`thm:weak-compactness`): a mass-bounded sequence of finite Borel measures on a
compact metric space has a weakly convergent subsequence, and the masses converge. Mathlib proves
the compactness of the set of mass-bounded finite measures,
`isCompact_setOf_finiteMeasure_le_of_compactSpace`. The proof writes each measure as its mass times
its normalisation and extracts a convergent subsequence in `ℝ≥0 × ProbabilityMeasure K`, using
that `ProbabilityMeasure K` is compact and metrisable
(`MeasureTheory.instMetrizableSpaceProbabilityMeasure`). -/
theorem weak_compactness {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K]
    [BorelSpace K] (μ : ℕ → FiniteMeasure K) (hμ : ∃ C : ℝ≥0, ∀ n, (μ n).mass ≤ C) :
    ∃ (φ : ℕ → ℕ) (ν : FiniteMeasure K), StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) ∧
      Tendsto (fun k => (μ (φ k)).mass) atTop (𝓝 ν.mass) := by
  obtain ⟨C, hC⟩ := hμ
  rcases isEmpty_or_nonempty K with hK | hK
  · -- On an empty space all measures coincide.
    have h : ∀ n, μ n = μ 0 := fun n =>
      Subtype.ext ((Measure.eq_zero_of_isEmpty _).trans (Measure.eq_zero_of_isEmpty _).symm)
    exact ⟨id, μ 0, strictMono_id, tendsto_const_nhds.congr fun n => (h n).symm,
      tendsto_const_nhds.congr fun n => congrArg FiniteMeasure.mass (h n).symm⟩
  let p : ℕ → ℝ≥0 × ProbabilityMeasure K := fun n => ((μ n).mass, (μ n).normalize)
  obtain ⟨q, -, φ, hφ, hlim⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := C)).prod
    (isCompact_univ (X := ProbabilityMeasure K)) |>.tendsto_subseq
    (x := p) fun n => ⟨⟨zero_le, hC n⟩, mem_univ _⟩
  let g : ℝ≥0 × ProbabilityMeasure K → FiniteMeasure K := fun q => q.1 • q.2.toFiniteMeasure
  have hg : Continuous g :=
    continuous_fst.smul ((ProbabilityMeasure.toFiniteMeasure_isEmbedding K).continuous.comp
      continuous_snd)
  have hμg : μ = g ∘ p := funext fun n => (μ n).self_eq_mass_smul_normalize
  have hconv : Tendsto (μ ∘ φ) atTop (𝓝 (g q)) := by
    rw [hμg, Function.comp_assoc]
    exact (hg.tendsto q).comp hlim
  exact ⟨φ, g q, hφ, hconv, hconv.mass⟩

/-- The open-set inequality stated after Theorem 1.8: for weakly convergent finite measures,
`μ(U) ≤ liminf μₙ(U)` for every open set `U`. The proof normalises the measures and applies
`MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto`. -/
theorem le_liminf_measure_open_of_tendsto {Ω : Type*} [PseudoEMetricSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μs : ℕ → FiniteMeasure Ω} {μ : FiniteMeasure Ω}
    (h : Tendsto μs atTop (𝓝 μ)) {U : Set Ω} (hU : IsOpen U) :
    (μ : Measure Ω) U ≤ liminf (fun n => (μs n : Measure Ω) U) atTop := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp
  have : Nonempty Ω := by
    by_contra hΩ
    rw [not_nonempty_iff] at hΩ
    exact hμ (Subtype.ext (Measure.eq_zero_of_isEmpty _))
  have hmass : Tendsto (fun n => ((μs n).mass : ℝ≥0∞)) atTop (𝓝 (μ.mass : ℝ≥0∞)) :=
    (ENNReal.continuous_coe.tendsto _).comp h.mass
  have key := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (FiniteMeasure.tendsto_normalize_of_tendsto h hμ) hU
  have hmul (ν : FiniteMeasure Ω) :
      (ν : Measure Ω) U = ν.mass * (ν.normalize : Measure Ω) U := by
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ← ENNReal.coe_mul,
      ← FiniteMeasure.self_eq_mass_mul_normalize]
  calc (μ : Measure Ω) U = μ.mass * (μ.normalize : Measure Ω) U := hmul μ
    _ ≤ μ.mass * liminf (fun n => ((μs n).normalize : Measure Ω) U) atTop := by gcongr
    _ = liminf (fun n => ((μs n).mass : ℝ≥0∞)) atTop *
          liminf (fun n => ((μs n).normalize : Measure Ω) U) atTop := by
      rw [hmass.liminf_eq]
    _ ≤ liminf ((fun n => ((μs n).mass : ℝ≥0∞)) *
          fun n => ((μs n).normalize : Measure Ω) U) atTop := ENNReal.le_liminf_mul
    _ = liminf (fun n => (μs n : Measure Ω) U) atTop := by
      congr 1
      funext n
      exact (hmul (μs n)).symm

end GeometricMeasureTheory
