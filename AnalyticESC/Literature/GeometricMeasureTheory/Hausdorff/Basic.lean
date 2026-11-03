module

/-
# Section 2: Hausdorff content, measure, and dimension

The opening part of Section 2 of the notes: the Hausdorff δ-content, content and measure, their
outer-measure and Borel properties, critical exponents, null sets, and Hausdorff dimension.

The definitions are stated for a gauge `g`, as in Section 2.5; the notes' `𝓗^s_δ`, `𝓗^s_∞` and
`𝓗^s` are the gauge `t ↦ t ^ s`. Covers are countable families of open sets, indexed by `ℕ`, and
the empty set has weight zero. `hausdorffMeasureGauge_rpow` identifies the Hausdorff measure of
Definition 2.3 with Mathlib's `MeasureTheory.Measure.hausdorffMeasure`, written `μH[s]`, so all later
statements about `𝓗^s` use `μH[s]`.

| Notes | Lean declaration | Location |
|---|---|---|
| Definition 2.1 (δ-content) | `hausdorffDelta`, `hausdorffDeltaGauge` | here |
| Definition 2.2 (content) | `hausdorffContent`, `hausdorffContentGauge` | here |
| Definition 2.3 (measure) | `hausdorffMeasureGauge`; `hausdorffMeasureGauge_rpow` identifies it with `MeasureTheory.Measure.hausdorffMeasure` | here; `Mathlib/MeasureTheory/Measure/Hausdorff.lean` |
| Comparison `𝓗^s_∞ ≤ 𝓗^s_δ ≤ 𝓗^s_δ' ≤ 𝓗^s` | `hausdorffContentGauge_le_hausdorffDeltaGauge`, `hausdorffDeltaGauge_anti`, `hausdorffDeltaGauge_le_hausdorffMeasureGauge` | here |
| Content at exponent zero, content as `δ → ∞` | `hausdorffContent_zero_of_nonempty`, `hausdorffContent_eq_iInf_hausdorffDelta` | here |
| Proposition 2.4 (outer measures) | `hausdorff_outer_measures` | here |
| Proposition 2.5 (Borel) | `MeasureTheory.le_toOuterMeasure_caratheodory` for the measure `μH[s]` | `Mathlib/MeasureTheory/Measure/MeasureSpace.lean` |
| Lemma 2.6 (separated additivity) | `MeasureTheory.OuterMeasure.mkMetric'_isMetric` | `Mathlib/MeasureTheory/Measure/Hausdorff.lean` |
| Lemma 2.7 (separated continuity) | `separated_continuity`, for every metric outer measure | here |
| Direct proof of Proposition 2.5 | the proof of `MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory` | `Mathlib/MeasureTheory/Measure/Hausdorff.lean` |
| Proposition 2.8 (critical exponents) | `MeasureTheory.Measure.hausdorffMeasure_zero_or_top` | `Mathlib/MeasureTheory/Measure/Hausdorff.lean` |
| Proposition 2.9 (same null sets) | `same_null_sets` | here |
| `𝓗^s_∞(E) ≤ (diam E)^s` | `hausdorffContent_le_ediam_rpow` | here |
| Definition 2.10 (Hausdorff dimension) | `dimH`, `dimH_eq_iInf`, `dimH_def` | `Mathlib/Topology/MetricSpace/HausdorffDimension.lean` |
| Dimension through content | `dimH_eq_iInf_hausdorffContent`, `dimH_eq_iSup_hausdorffContent` | here |
| `0 < 𝓗^s(E) < ∞` implies `dim_H E = s` | `dimH_of_hausdorffMeasure_ne_zero_ne_top` | `Mathlib/Topology/MetricSpace/HausdorffDimension.lean` |

The paragraph *Hausdorff content need not be additive* is in
`GeometricMeasureTheory.Hausdorff.NonadditiveContent`.
-/

public import AnalyticESC.Literature.GeometricMeasureTheory.BasicMeasureTheory

@[expose] public section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [EMetricSpace X]

/-! ## Definitions 2.1–2.3 

Copied from the library `FractalGeometry` (module `GeometricMeasureTheory.Hausdorff.Basic`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

/-- The weight `g(|U|)` of a covering set `U`, with the empty set given weight zero. For the gauge
`t ↦ t ^ s` at `s = 0`, every non-empty set has weight one. -/
def gaugeWeight (g : ℝ≥0∞ → ℝ≥0∞) (U : Set X) : ℝ≥0∞ :=
  ⨆ _ : U.Nonempty, g (ediam U)

/-- Definition 2.1 (`def:hausdorff-delta`) for a gauge `g`: the infimum of `∑ g(|Uᵢ|)` over
countable open covers of `E` by sets of diameter less than `δ`. -/
def hausdorffDeltaGauge (g : ℝ≥0∞ → ℝ≥0∞) (δ : ℝ≥0∞) (E : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : ∀ i, IsOpen (U i)) (_ : ∀ i, ediam (U i) < δ) (_ : E ⊆ ⋃ i, U i),
    ∑' i, gaugeWeight g (U i)

/-- Definition 2.2 (`def:hausdorff-content`) for a gauge `g`: the infimum of `∑ g(|Uᵢ|)` over
countable open covers of `E`. -/
def hausdorffContentGauge (g : ℝ≥0∞ → ℝ≥0∞) (E : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : ∀ i, IsOpen (U i)) (_ : E ⊆ ⋃ i, U i), ∑' i, gaugeWeight g (U i)

/-- Definition 2.3 (`def:hausdorff-measure`) for a gauge `g`: the limit of the δ-contents as
`δ → 0`. -/
def hausdorffMeasureGauge (g : ℝ≥0∞ → ℝ≥0∞) (E : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ≥0∞) (_ : 0 < δ), hausdorffDeltaGauge g δ E

/-- Definition 2.1 (`def:hausdorff-delta`): the `s`-dimensional Hausdorff δ-content `𝓗^s_δ`. -/
abbrev hausdorffDelta (s : ℝ) : ℝ≥0∞ → Set X → ℝ≥0∞ :=
  hausdorffDeltaGauge fun t => t ^ s

/-- Definition 2.2 (`def:hausdorff-content`): the `s`-dimensional Hausdorff content `𝓗^s_∞`. -/
abbrev hausdorffContent (s : ℝ) : Set X → ℝ≥0∞ :=
  hausdorffContentGauge fun t => t ^ s

/-- The empty set has weight zero. -/
@[simp]
theorem gaugeWeight_empty (g : ℝ≥0∞ → ℝ≥0∞) : gaugeWeight g (∅ : Set X) = 0 := by
  simp [gaugeWeight]

/-- A non-empty set `U` has weight `g(|U|)`. -/
theorem gaugeWeight_of_nonempty (g : ℝ≥0∞ → ℝ≥0∞) {U : Set X} (hU : U.Nonempty) :
    gaugeWeight g U = g (ediam U) :=
  iSup_pos hU

/-- An open set containing `E` bounds the content of `E` by its weight. -/
theorem hausdorffContentGauge_le_gaugeWeight (g : ℝ≥0∞ → ℝ≥0∞) {E V : Set X} (hV : IsOpen V)
    (hEV : E ⊆ V) : hausdorffContentGauge g E ≤ gaugeWeight g V := by
  classical
  refine iInf_le_of_le (fun i => if i = 0 then V else ∅) <| iInf_le_of_le (fun i => ?_) <|
    iInf_le_of_le (hEV.trans (subset_iUnion_of_subset 0 (by simp))) ?_
  · dsimp only
    split_ifs
    exacts [hV, isOpen_empty]
  · rw [tsum_eq_single 0 fun i hi => by simp [hi]]
    simp

/-- A set of diameter less than `δ` lies in an open set of diameter less than `δ` whose weight for
the gauge `t ↦ t ^ s`, `s ≥ 0`, exceeds its own by at most `ε`. -/
private theorem exists_isOpen_superset_gaugeWeight_rpow_le {s : ℝ} (hs : 0 ≤ s) {δ ε : ℝ≥0∞}
    (hε : ε ≠ 0) {U : Set X} (hU : ediam U < δ) :
    ∃ V : Set X, IsOpen V ∧ U ⊆ V ∧ ediam V < δ ∧
      gaugeWeight (fun t => t ^ s) V ≤ gaugeWeight (fun t => t ^ s) U + ε := by
  rcases U.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, isOpen_empty, Subset.rfl, hU, by simp⟩
  have hU_top : ediam U ≠ ⊤ := (hU.trans_le le_top).ne
  have hc : Continuous fun η : ℝ≥0 => ediam U + 2 * (η : ℝ≥0∞) :=
    continuous_const.add ((ENNReal.continuous_const_mul (by simp)).comp ENNReal.continuous_coe)
  have hlim : Tendsto (fun η : ℝ≥0 => ediam U + 2 * (η : ℝ≥0∞)) (𝓝[>] 0) (𝓝 (ediam U)) :=
    (hc.tendsto' 0 _ (by simp)).mono_left nhdsWithin_le_nhds
  have h1 : ∀ᶠ t in 𝓝 (ediam U), t < δ := gt_mem_nhds hU
  have h2 : ∀ᶠ t in 𝓝 (ediam U), t ^ s < ediam U ^ s + ε :=
    (ENNReal.continuous_rpow_const.tendsto _).eventually
      (gt_mem_nhds (ENNReal.lt_add_right (ENNReal.rpow_lt_top_of_nonneg hs hU_top).ne hε))
  obtain ⟨η, ⟨hηδ, hηs⟩, hη⟩ := ((hlim.eventually (h1.and h2)).and self_mem_nhdsWithin).exists
  have hsub : U ⊆ thickening η U := self_subset_thickening (NNReal.coe_pos.2 hη) U
  refine ⟨thickening η U, isOpen_thickening, hsub, (ediam_thickening_le η).trans_lt hηδ, ?_⟩
  rw [gaugeWeight_of_nonempty _ (hne.mono hsub), gaugeWeight_of_nonempty _ hne]
  exact (ENNReal.rpow_le_rpow (ediam_thickening_le η) hs).trans hηs.le

/-- Definition 2.3 (`def:hausdorff-measure`) agrees with Mathlib's Hausdorff measure. -/
theorem hausdorffMeasureGauge_rpow [MeasurableSpace X] [BorelSpace X] {s : ℝ} (hs : 0 ≤ s)
    (E : Set X) : hausdorffMeasureGauge (fun t => t ^ s) E = μH[s] E := by
  rw [Measure.hausdorffMeasure_apply, hausdorffMeasureGauge]
  refine le_antisymm (iSup₂_le fun δ hδ => ?_) (iSup₂_mono fun r hr => ?_)
  · -- Thicken an arbitrary cover by sets of diameter at most `r < δ`.
    obtain ⟨r, hr0, hrδ⟩ := exists_between hδ
    refine le_trans ?_ (le_iSup₂ (f := fun r (_ : 0 < r) => ⨅ (t : ℕ → Set X)
      (_ : E ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r), ∑' n, ⨆ _ : (t n).Nonempty,
        ediam (t n) ^ s) r hr0)
    refine le_iInf₂ fun t hEt => le_iInf fun htr => ?_
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨ε', hε'0, hε'⟩ :=
      ENNReal.exists_pos_sum_of_countable (ENNReal.coe_ne_zero.2 hε.ne') ℕ
    choose V hVo htV hVδ hVw using fun n =>
      exists_isOpen_superset_gaugeWeight_rpow_le hs (ENNReal.coe_ne_zero.2 (hε'0 n).ne')
        ((htr n).trans_lt hrδ)
    calc hausdorffDeltaGauge (fun t => t ^ s) δ E
        ≤ ∑' n, gaugeWeight (fun t => t ^ s) (V n) :=
          iInf_le_of_le V <| iInf_le_of_le hVo <| iInf_le_of_le hVδ <|
            iInf_le_of_le (hEt.trans (iUnion_mono htV)) le_rfl
      _ ≤ ∑' n, (gaugeWeight (fun t => t ^ s) (t n) + ε' n) := ENNReal.tsum_le_tsum hVw
      _ = ∑' n, gaugeWeight (fun t => t ^ s) (t n) + ∑' n, (ε' n : ℝ≥0∞) := ENNReal.tsum_add
      _ ≤ _ := add_le_add le_rfl hε'.le
  · -- An open cover by sets of diameter less than `r` is admissible for Mathlib's definition.
    refine le_iInf fun U => le_iInf fun hU => le_iInf fun hd => le_iInf fun hE => ?_
    exact iInf₂_le_of_le U hE (iInf_le_of_le (fun n => (hd n).le) le_rfl)

/-! ### The comparison after Definition 2.3 -/

theorem hausdorffContentGauge_le_hausdorffDeltaGauge (g : ℝ≥0∞ → ℝ≥0∞) (δ : ℝ≥0∞) (E : Set X) :
    hausdorffContentGauge g E ≤ hausdorffDeltaGauge g δ E :=
  le_iInf fun U => le_iInf fun hU => le_iInf fun _ => le_iInf fun hE =>
    iInf₂_le_of_le U hU (iInf_le _ hE)

theorem hausdorffDeltaGauge_anti (g : ℝ≥0∞ → ℝ≥0∞) (E : Set X) {δ δ' : ℝ≥0∞} (h : δ' ≤ δ) :
    hausdorffDeltaGauge g δ E ≤ hausdorffDeltaGauge g δ' E :=
  le_iInf fun U => le_iInf fun hU => le_iInf fun hd => le_iInf fun hE =>
    iInf_le_of_le U <| iInf_le_of_le hU <| iInf_le_of_le (fun i => (hd i).trans_le h) <|
      iInf_le _ hE

theorem hausdorffDeltaGauge_le_hausdorffMeasureGauge (g : ℝ≥0∞ → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : 0 < δ)
    (E : Set X) : hausdorffDeltaGauge g δ E ≤ hausdorffMeasureGauge g E :=
  le_iSup₂ (f := fun δ (_ : 0 < δ) => hausdorffDeltaGauge g δ E) δ hδ

/-- The content at exponent zero is one for a non-empty set. -/
theorem hausdorffContent_zero_of_nonempty {E : Set X} (hE : E.Nonempty) :
    hausdorffContent 0 E = 1 := by
  refine le_antisymm ((hausdorffContentGauge_le_gaugeWeight _ isOpen_univ (subset_univ E)).trans
    (iSup_le fun _ => ENNReal.rpow_zero.le)) ?_
  refine le_iInf fun U => le_iInf fun _ => le_iInf fun hEU => ?_
  obtain ⟨x, hx⟩ := hE
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hEU hx)
  calc (1 : ℝ≥0∞) = gaugeWeight (fun t => t ^ (0 : ℝ)) (U i) := by
        rw [gaugeWeight_of_nonempty _ ⟨x, hi⟩, ENNReal.rpow_zero]
    _ ≤ ∑' i, gaugeWeight (fun t => t ^ (0 : ℝ)) (U i) :=
        ENNReal.le_tsum (f := fun i => gaugeWeight (fun t => t ^ (0 : ℝ)) (U i)) i

/-- For `s > 0` the content is the limit of the δ-contents as `δ → ∞`. -/
theorem hausdorffContent_eq_iInf_hausdorffDelta {s : ℝ} (hs : 0 < s) (E : Set X) :
    hausdorffContent s E = ⨅ δ : ℝ≥0∞, hausdorffDelta s δ E := by
  refine le_antisymm (le_iInf fun δ => hausdorffContentGauge_le_hausdorffDeltaGauge _ δ E)
    (iInf_le_of_le ⊤ (le_iInf fun U => le_iInf fun hU => le_iInf fun hE => ?_))
  by_cases hd : ∀ i, ediam (U i) < ⊤
  · exact iInf_le_of_le U (iInf_le_of_le hU (iInf_le_of_le hd (iInf_le _ hE)))
  · -- A covering set of infinite diameter has infinite weight.
    simp only [not_forall, lt_top_iff_ne_top, not_not] at hd
    obtain ⟨i, hi⟩ := hd
    have hne : (U i).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      simp [h] at hi
    refine le_top.trans_eq (ENNReal.tsum_eq_top_of_eq_top ⟨i, ?_⟩).symm
    rw [gaugeWeight_of_nonempty _ hne, hi, ENNReal.top_rpow_of_pos hs]

/-! ## Proposition 2.4 (`thm:hausdorff-outer-measures`) -/

omit [EMetricSpace X] in
/-- The infimum of `∑ w(Uᵢ)` over countable covers by sets satisfying `P` is the outer measure
`OuterMeasure.ofFunction` built from `w` on `P` and `∞` elsewhere. -/
private theorem iInf_cover_eq_ofFunction (P : Set X → Prop) (w : Set X → ℝ≥0∞) (hP : P ∅)
    (hw : w ∅ = 0) (E : Set X) :
    (⨅ (U : ℕ → Set X) (_ : ∀ i, P (U i)) (_ : E ⊆ ⋃ i, U i), ∑' i, w (U i)) =
      OuterMeasure.ofFunction (fun U => ⨅ _ : P U, w U) (by simp [hP, hw]) E := by
  rw [OuterMeasure.ofFunction_apply]
  refine le_antisymm (le_iInf₂ fun U hE => ?_) (le_iInf₂ fun U hU => le_iInf fun hE => ?_)
  · by_cases hU : ∀ i, P (U i)
    · exact iInf₂_le_of_le U hU <| iInf_le_of_le hE <|
        ENNReal.tsum_le_tsum fun i => by simp [hU i]
    · simp only [not_forall] at hU
      obtain ⟨i, hi⟩ := hU
      exact le_top.trans_eq (ENNReal.tsum_eq_top_of_eq_top ⟨i, by simp [hi]⟩).symm
  · exact iInf₂_le_of_le U hE (ENNReal.tsum_le_tsum fun i => by simp [hU i])

omit [EMetricSpace X] in
/-- The infimum of `∑ w(Uᵢ)` over countable covers by sets satisfying `P` is an outer measure. -/
private theorem isOuterMeasure_iInf_cover (P : Set X → Prop) (w : Set X → ℝ≥0∞) (hP : P ∅)
    (hw : w ∅ = 0) :
    IsOuterMeasure fun E : Set X =>
      ⨅ (U : ℕ → Set X) (_ : ∀ i, P (U i)) (_ : E ⊆ ⋃ i, U i), ∑' i, w (U i) := by
  rw [show (fun E : Set X => ⨅ (U : ℕ → Set X) (_ : ∀ i, P (U i)) (_ : E ⊆ ⋃ i, U i),
    ∑' i, w (U i)) = _ from funext (iInf_cover_eq_ofFunction P w hP hw)]
  exact ⟨measure_empty, fun A B h => measure_mono h, fun A => measure_iUnion_le A⟩

/-- Proposition 2.4 (`thm:hausdorff-outer-measures`): for every gauge and every `δ > 0`, the
δ-content, the content and the Hausdorff measure are outer measures. -/
theorem hausdorff_outer_measures (g : ℝ≥0∞ → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    IsOuterMeasure (hausdorffDeltaGauge (X := X) g δ) ∧
      IsOuterMeasure (hausdorffContentGauge (X := X) g) ∧
      IsOuterMeasure (hausdorffMeasureGauge (X := X) g) := by
  have hdelta : ∀ δ : ℝ≥0∞, 0 < δ → IsOuterMeasure (hausdorffDeltaGauge (X := X) g δ) := by
    intro δ hδ
    have h := isOuterMeasure_iInf_cover (X := X) (fun U => IsOpen U ∧ ediam U < δ)
      (gaugeWeight g) ⟨isOpen_empty, by rwa [ediam_empty]⟩ (gaugeWeight_empty g)
    convert h using 1
    funext E
    simp only [hausdorffDeltaGauge, forall_and, iInf_and]
  refine ⟨hdelta δ hδ,
    isOuterMeasure_iInf_cover IsOpen (gaugeWeight g) isOpen_empty (gaugeWeight_empty g), ?_⟩
  refine ⟨?_, fun A B hAB => ?_, fun A => ?_⟩
  · exact le_antisymm (iSup₂_le fun δ hδ => (hdelta δ hδ).empty.le) zero_le
  · exact iSup₂_mono fun δ hδ => (hdelta δ hδ).mono hAB
  · exact iSup₂_le fun δ hδ => ((hdelta δ hδ).iUnion_le A).trans
      (ENNReal.tsum_le_tsum fun i => hausdorffDeltaGauge_le_hausdorffMeasureGauge g hδ (A i))

/-- The Hausdorff content `𝓗^s_∞` bundled as an outer measure. -/
def hausdorffContentOuter (s : ℝ) : OuterMeasure X :=
  (hausdorff_outer_measures (X := X) (fun t => t ^ s) zero_lt_one).2.1.toOuterMeasure

@[simp]
theorem coe_hausdorffContentOuter (s : ℝ) :
    ⇑(hausdorffContentOuter (X := X) s) = hausdorffContent s :=
  rfl

/-! ## Proposition 2.5 (`thm:hausdorff-borel`)

Mathlib's `μH[s]` is a measure on the Borel σ-algebra, and a measure makes the sets of its
σ-algebra Carathéodory measurable (`MeasureTheory.le_toOuterMeasure_caratheodory`). -/

example [MeasurableSpace X] [BorelSpace X] (s : ℝ) :
    borel X ≤ (μH[s] : Measure X).toOuterMeasure.caratheodory := by
  rw [← BorelSpace.measurable_eq]
  exact le_toOuterMeasure_caratheodory _

/-! ## Lemma 2.6 (`thm:separated-additivity`)

The Hausdorff measure is a metric outer measure (`MeasureTheory.OuterMeasure.mkMetric'_isMetric`),
which is Lemma 2.6. -/

example [MeasurableSpace X] [BorelSpace X] (s : ℝ) {A B : Set X} (h : Metric.AreSeparated A B) :
    μH[s] (A ∪ B) = μH[s] A + μH[s] B := by
  simp only [Measure.hausdorffMeasure, ← OuterMeasure.coe_mkMetric]
  exact OuterMeasure.mkMetric'_isMetric _ A B h

/-! ## Lemma 2.7 (`thm:separated-continuity`) -/

/-- Lemma 2.7 (`thm:separated-continuity`), for every metric outer measure: along an increasing
sequence whose members are positively separated from the part of the union beyond the next one,
the measure is continuous. -/
theorem separated_continuity {μ : OuterMeasure X} (hμ : μ.IsMetric) {A : ℕ → Set X}
    (hA : Monotone A) (hsep : ∀ k, Metric.AreSeparated (A k) ((⋃ i, A i) \ A (k + 1))) :
    Tendsto (fun k => μ (A k)) atTop (𝓝 (μ (⋃ i, A i))) := by
  have hmono : Monotone fun k => μ (A k) := fun i j hij => measure_mono (hA hij)
  suffices h : μ (⋃ i, A i) = ⨆ k, μ (A k) by
    rw [h]
    exact tendsto_atTop_iSup hmono
  refine le_antisymm ?_ (iSup_le fun k => measure_mono (subset_iUnion A k))
  by_cases htop : ⨆ k, μ (A k) = ∞
  · rw [htop]
    exact le_top
  refine (μ.iUnion_nat_of_monotone_of_tsum_ne_top (fun n => hA n.le_succ) ?_).le
  -- Split the series of the differences `A (k + 1) \ A k` into its even and odd terms.
  rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable, ENNReal.add_ne_top]
  suffices ∀ r, (∑' k : ℕ, μ (A (2 * k + 1 + r) \ A (2 * k + r))) ≠ ∞ from
    ⟨by simpa using this 0, by simpa using this 1⟩
  intro r
  refine ne_top_of_le_ne_top htop ?_
  rw [ENNReal.tsum_eq_iSup_nat, iSup_le_iff]
  intro n
  rw [← hμ.finset_iUnion_of_pairwise_separated]
  · refine (measure_mono (iUnion₂_subset fun i hi => sdiff_subset.trans (hA ?_))).trans
      (le_iSup (fun k => μ (A k)) (2 * n + r))
    rw [Finset.mem_range] at hi
    omega
  · have key : ∀ i j, i < j → Metric.AreSeparated (A (2 * i + 1 + r) \ A (2 * i + r))
        (A (2 * j + 1 + r) \ A (2 * j + r)) := by
      intro i j hij
      refine (hsep (2 * i + 1 + r)).mono sdiff_subset ?_
      rintro x ⟨hx1, hx2⟩
      exact ⟨mem_iUnion.2 ⟨_, hx1⟩, fun hx => hx2 (hA (by omega) hx)⟩
    intro i _ j _ hij
    rcases hij.lt_or_gt with h | h
    exacts [key i j h, (key j i h).symm]

/-! ## Proposition 2.8 (`thm:critical-exponent`)

This is `MeasureTheory.Measure.hausdorffMeasure_zero_or_top`. -/

example [MeasurableSpace X] [BorelSpace X] {s t : ℝ} (hst : s < t) {E : Set X}
    (h : μH[s] E ≠ ∞) : μH[t] E = 0 :=
  (Measure.hausdorffMeasure_zero_or_top hst E).resolve_right h

/-! ## Proposition 2.9 (`thm:same-null-sets`) -/

/-- Proposition 2.9 (`thm:same-null-sets`): Hausdorff content and Hausdorff measure have the same
null sets. -/
theorem same_null_sets [MeasurableSpace X] [BorelSpace X] {s : ℝ} (hs : 0 ≤ s) (E : Set X) :
    μH[s] E = 0 ↔ hausdorffContent s E = 0 := by
  rw [← hausdorffMeasureGauge_rpow hs]
  refine ⟨fun h => le_antisymm ?_ zero_le, fun h => ?_⟩
  · exact (hausdorffContentGauge_le_hausdorffDeltaGauge (fun t : ℝ≥0∞ => t ^ s) 1 E).trans
      ((hausdorffDeltaGauge_le_hausdorffMeasureGauge _ zero_lt_one E).trans h.le)
  rcases hs.eq_or_lt with rfl | hs
  · -- At exponent zero both vanish exactly on the empty set.
    rcases E.eq_empty_or_nonempty with rfl | hE
    · exact (hausdorff_outer_measures (X := X) (fun t : ℝ≥0∞ => t ^ (0 : ℝ)) zero_lt_one).2.2.empty
    · rw [hausdorffContent_zero_of_nonempty hE] at h
      exact absurd h one_ne_zero
  refine le_antisymm (iSup₂_le fun δ hδ => le_of_forall_gt fun ε hε => ?_) zero_le
  have hpos : hausdorffContent s E < min ε (δ ^ s) :=
    h.trans_lt (lt_min hε (ENNReal.rpow_pos_of_nonneg hδ hs.le))
  obtain ⟨U, hlt⟩ := iInf_lt_iff.1 hpos
  obtain ⟨hUo, hlt⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hEU, hlt⟩ := iInf_lt_iff.1 hlt
  -- A cover of total weight less than `δ ^ s` consists of sets of diameter less than `δ`.
  have hd : ∀ i, ediam (U i) < δ := fun i => by
    rcases (U i).eq_empty_or_nonempty with he | hne
    · rw [he, ediam_empty]
      exact hδ
    · refine (ENNReal.rpow_lt_rpow_iff hs).1 ?_
      calc ediam (U i) ^ s = gaugeWeight (fun t => t ^ s) (U i) :=
            (gaugeWeight_of_nonempty (fun t => t ^ s) hne).symm
        _ ≤ ∑' i, gaugeWeight (fun t => t ^ s) (U i) :=
            ENNReal.le_tsum (f := fun i => gaugeWeight (fun t => t ^ s) (U i)) i
        _ < min ε (δ ^ s) := hlt
        _ ≤ δ ^ s := min_le_right _ _
  have hδE : hausdorffDelta s δ E ≤ ∑' i, gaugeWeight (fun t => t ^ s) (U i) :=
    iInf_le_of_le U <| iInf_le_of_le hUo <| iInf_le_of_le hd <| iInf_le _ hEU
  exact hδE.trans_lt (hlt.trans_le (min_le_left _ _))

/-- The bound `𝓗^s_∞(E) ≤ (diam E)^s` stated after Proposition 2.9. -/
theorem hausdorffContent_le_ediam_rpow {s : ℝ} (hs : 0 ≤ s) (E : Set X) :
    hausdorffContent s E ≤ ediam E ^ s := by
  rcases E.eq_empty_or_nonempty with rfl | hE
  · have h := (hausdorff_outer_measures (X := X) (fun t : ℝ≥0∞ => t ^ s) zero_lt_one).2.1.empty
    exact h.le.trans zero_le
  by_cases htop : ediam E = ⊤
  · rcases hs.eq_or_lt with rfl | hs
    · rw [hausdorffContent_zero_of_nonempty hE, ENNReal.rpow_zero]
    · rw [htop, ENNReal.top_rpow_of_pos hs]
      exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨V, hVo, hEV, -, hVw⟩ := exists_isOpen_superset_gaugeWeight_rpow_le hs
    (ENNReal.coe_ne_zero.2 hε.ne') (lt_top_iff_ne_top.2 htop)
  calc hausdorffContent s E ≤ gaugeWeight (fun t => t ^ s) V :=
        hausdorffContentGauge_le_gaugeWeight _ hVo hEV
    _ ≤ gaugeWeight (fun t => t ^ s) E + ε := hVw
    _ = ediam E ^ s + ε := by rw [gaugeWeight_of_nonempty _ hE]

/-! ## Definition 2.10 (`def:hausdorff-dimension`)

Hausdorff dimension is Mathlib's `dimH`. Mathlib defines it as `sup {s : 𝓗^s(E) = ∞}`; the notes'
formula `inf {s : 𝓗^s(E) = 0}` is `dimH_eq_iInf`. -/

example [MeasurableSpace X] [BorelSpace X] (E : Set X) :
    dimH E = ⨅ (s : ℝ≥0) (_ : μH[s] E = 0), (s : ℝ≥0∞) :=
  dimH_eq_iInf E

/-- The characterisation of Hausdorff dimension through content after Definition 2.10. -/
theorem dimH_eq_iInf_hausdorffContent (E : Set X) :
    dimH E = ⨅ (s : ℝ≥0) (_ : hausdorffContent (s : ℝ) E = 0), (s : ℝ≥0∞) := by
  borelize X
  rw [dimH_eq_iInf]
  refine iInf_congr fun s => ?_
  rw [same_null_sets s.coe_nonneg]

/-- The characterisation of Hausdorff dimension through positive content after Definition 2.10. -/
theorem dimH_eq_iSup_hausdorffContent (E : Set X) :
    dimH E = ⨆ (s : ℝ≥0) (_ : 0 < hausdorffContent (s : ℝ) E), (s : ℝ≥0∞) := by
  borelize X
  refine le_antisymm ?_ (iSup₂_le fun s hs => le_dimH_of_hausdorffMeasure_ne_zero ?_)
  · rw [dimH_def]
    refine iSup₂_le fun s hs => le_iSup₂_of_le s ?_ le_rfl
    rw [pos_iff_ne_zero, Ne, ← same_null_sets s.coe_nonneg, hs]
    exact ENNReal.top_ne_zero
  · rw [Ne, same_null_sets s.coe_nonneg]
    exact hs.ne'

end GeometricMeasureTheory
