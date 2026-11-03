module

/-
# Section 2.3: Computing the Hausdorff measure and content

Lower bounds from measures, similarity scaling, and equality of content and measure. The Cantor
sets of this subsection, including Example 2.23, are in
`GeometricMeasureTheory.Hausdorff.CantorSets`; the content of an interval is in
`GeometricMeasureTheory.Hausdorff.NonadditiveContent`.

The mass distribution principle needs only monotonicity and countable subadditivity, so it is
stated for an arbitrary outer measure `μ : F` with `[FunLike F (Set X) ℝ≥0∞]` and
`[MeasureTheory.OuterMeasureClass F X]`, which covers a measure as well as an outer measure.

| Notes | Lean declaration | Location |
|---|---|---|
| The interval: `𝓗^1_∞([0, 1]) = 𝓗^1([0, 1]) = 1` | `hausdorffContent_Icc`; `MeasureTheory.hausdorffMeasure_real` | `GeometricMeasureTheory.Hausdorff.NonadditiveContent`; `Mathlib/MeasureTheory/Measure/Hausdorff.lean` |
| The Cantor upper bound | `cantor_upper_bound` | `GeometricMeasureTheory.Hausdorff.CantorSets` |
| Lemma 2.16 (mass distribution principle) | `mass_distribution` | here |
| Sharper bounds on the real line | `mass_distribution_real` | here |
| The Cantor measure and lower bound | `exists_cantor_measure`, `cantor_lower_bound`, `middle_third_cantor` | `GeometricMeasureTheory.Hausdorff.CantorSets` |
| Proposition 2.20 (similarity scaling) | `scaling` | here |
| Scaling of `𝓗^s_δ` and `𝓗^s_∞` under similarities | `scaling_hausdorffDelta`, `scaling_hausdorffContent` | here |
| Translation and isometry invariance | `IsometryEquiv.hausdorffMeasure_image`, `Isometry.hausdorffMeasure_image` | `Mathlib/MeasureTheory/Measure/Hausdorff.lean` |
| Theorem 2.22 (equality of content and measure) | `equal_measure_content` | here |
| Example 2.23 (middle-half Cantor set) | `middle_half_cantor` | `GeometricMeasureTheory.Hausdorff.CantorSets` |
| Proposition 2.24 (open sets in `ℝ^d`) | `Real.dimH_of_nonempty_interior` | `Mathlib/Topology/MetricSpace/HausdorffDimension.lean` |
-/

public import AnalyticESC.Literature.GeometricMeasureTheory.Hausdorff.GeneralGauges

@[expose] public section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

/-! ## Lemma 2.16 (`thm:mass-distribution`) 

Copied from the library `FractalGeometry` (module `GeometricMeasureTheory.Hausdorff.Computing`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

/-- If `μ(B(x, r)) ≤ C r^s` for every `r > 0` and `U ⊆ B(x, d + η)` for every `η > 0`, then
`μ(U) ≤ C d^s`. -/
private theorem measure_le_of_subset_ball_add {X : Type*} [PseudoMetricSpace X] {F : Type*}
    [FunLike F (Set X) ℝ≥0∞] [OuterMeasureClass F X] (μ : F) {s : ℝ} {C : ℝ≥0} {x : X} {U : Set X}
    {d : ℝ} (hd : 0 ≤ d) (hball : ∀ r : ℝ, 0 < r → μ (ball x r) ≤ C * ENNReal.ofReal r ^ s)
    (hU : ∀ η : ℝ, 0 < η → U ⊆ ball x (d + η)) :
    μ U ≤ C * ENNReal.ofReal d ^ s := by
  have hc : Continuous fun η : ℝ => (C : ℝ≥0∞) * ENNReal.ofReal (d + η) ^ s :=
    (ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp <| (ENNReal.continuous_rpow_const).comp
      (ENNReal.continuous_ofReal.comp (continuous_const.add continuous_id))
  have hlim := hc.tendsto 0
  simp only [add_zero] at hlim
  refine ge_of_tendsto (hlim.mono_left (nhdsWithin_le_nhds (s := Ioi 0)))
    (eventually_nhdsWithin_of_forall fun η hη => ?_)
  have hη : 0 < η := hη
  exact (measure_mono (hU η hη)).trans (hball _ (by linarith))

/-- Lemma 2.16 (mass distribution principle, `thm:mass-distribution`), for an arbitrary outer
measure `μ`: if `μ(B(x, r)) ≤ C r^s` for every `x ∈ E` and `r > 0`, then `𝓗^s_∞(E) ≥ μ(E) / C`, and
`dim_H E ≥ s` when `μ(E) > 0`. -/
theorem mass_distribution {X : Type*} [MetricSpace X] {F : Type*} [FunLike F (Set X) ℝ≥0∞]
    [OuterMeasureClass F X] (μ : F) {s : ℝ} (hs : 0 < s) {C : ℝ≥0} (hC : C ≠ 0) {E : Set X}
    (hball : ∀ x ∈ E, ∀ r : ℝ, 0 < r → μ (ball x r) ≤ C * ENNReal.ofReal r ^ s) :
    μ E / C ≤ hausdorffContent s E ∧ (0 < μ E → ENNReal.ofReal s ≤ dimH E) := by
  borelize X
  have hcontent : μ E / C ≤ hausdorffContent s E := by
    refine mass_distribution_gauge μ _ hC fun U _ hUE => ?_
    obtain ⟨x, hxU, hxE⟩ := hUE
    by_cases htop : ediam U = ⊤
    · rw [htop, ENNReal.top_rpow_of_pos hs, ENNReal.mul_top (ENNReal.coe_ne_zero.2 hC)]
      exact le_top
    have hb : Bornology.IsBounded U := isBounded_iff_ediam_ne_top.2 htop
    have hdiam : ediam U = ENNReal.ofReal (diam U) := (ENNReal.ofReal_toReal htop).symm
    rw [hdiam]
    exact measure_le_of_subset_ball_add μ diam_nonneg (hball x hxE) fun η hη y hy =>
      mem_ball.2 ((dist_le_diam_of_mem hb hy hxU).trans_lt (lt_add_of_pos_right _ hη))
  refine ⟨hcontent, fun hμ => ?_⟩
  have hpos : 0 < hausdorffContent s E :=
    (ENNReal.div_pos_iff.2 ⟨hμ.ne', ENNReal.coe_ne_top⟩).trans_le hcontent
  have hH : μH[s] E ≠ 0 := fun h0 => hpos.ne' ((same_null_sets hs.le E).1 h0)
  exact le_dimH_of_hausdorffMeasure_ne_zero (d := s.toNNReal) (by rwa [Real.coe_toNNReal _ hs.le])

/-- The paragraph *Sharper bounds and the interval*, for an arbitrary outer measure `μ`: on the real
line, a ball bound at every centre gives `𝓗^s_∞(E) ≥ 2^s μ(E) / C`. -/
theorem mass_distribution_real {F : Type*} [FunLike F (Set ℝ) ℝ≥0∞] [OuterMeasureClass F ℝ] (μ : F)
    {s : ℝ} (hs : 0 < s) {C : ℝ≥0} (hC : C ≠ 0) {E : Set ℝ}
    (hball : ∀ x : ℝ, ∀ r : ℝ, 0 < r → μ (ball x r) ≤ C * ENNReal.ofReal r ^ s) :
    2 ^ s * μ E / C ≤ hausdorffContent s E := by
  have h2 : ((2 : ℝ≥0∞) ^ s)⁻¹ = (2 : ℝ≥0∞)⁻¹ ^ s := (ENNReal.inv_rpow 2 s).symm
  have h2ne : (2 : ℝ≥0∞) ^ s ≠ 0 := (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
  have h2top : (2 : ℝ≥0∞) ^ s ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hs.le (by norm_num)
  have hinv0 : (2 : ℝ≥0∞)⁻¹ ^ s ≠ 0 := by rw [← h2]; exact ENNReal.inv_ne_zero.2 h2top
  have hinvtop : (2 : ℝ≥0∞)⁻¹ ^ s ≠ ∞ := by rw [← h2]; exact ENNReal.inv_ne_top.2 h2ne
  -- the interval argument: an open set `U` on the line lies in a ball of radius `|U| / 2`
  have hU : ∀ U : Set ℝ, IsOpen U → (U ∩ E).Nonempty →
      μ U ≤ C * (2⁻¹ ^ s * ediam U ^ s) := by
    intro U _ hUE
    have hne : U.Nonempty := hUE.mono inter_subset_left
    by_cases htop : ediam U = ⊤
    · rw [htop, ENNReal.top_rpow_of_pos hs, ENNReal.mul_top hinv0,
        ENNReal.mul_top (ENNReal.coe_ne_zero.2 hC)]
      exact le_top
    have hb : Bornology.IsBounded U := isBounded_iff_ediam_ne_top.2 htop
    have hle : sInf U ≤ sSup U := csInf_le_csSup hne hb.bddBelow hb.bddAbove
    have hhalf : ENNReal.ofReal ((sSup U - sInf U) / 2)
        = 2⁻¹ * ENNReal.ofReal (sSup U - sInf U) := by
      rw [div_eq_inv_mul, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num),
        ENNReal.ofReal_ofNat]
    calc μ U ≤ C * ENNReal.ofReal ((sSup U - sInf U) / 2) ^ s := by
          refine measure_le_of_subset_ball_add μ (x := (sInf U + sSup U) / 2) (by linarith)
            (hball _) fun η hη y hy => ?_
          have h1 := csInf_le hb.bddBelow hy
          have h2 := le_csSup hb.bddAbove hy
          rw [mem_ball, Real.dist_eq, abs_sub_lt_iff]
          constructor <;> linarith
      _ = C * (2⁻¹ ^ s * ediam U ^ s) := by
          rw [Real.ediam_eq hb, ← ENNReal.mul_rpow_of_nonneg _ _ hs.le, hhalf]
  have h := mass_distribution_gauge μ (fun t => 2⁻¹ ^ s * t ^ s) hC hU
  rw [hausdorffContentGauge_const_mul _ hinv0 hinvtop] at h
  calc (2 : ℝ≥0∞) ^ s * μ E / C = 2 ^ s * (μ E / C) := mul_div_assoc ..
    _ ≤ 2 ^ s * (2⁻¹ ^ s * hausdorffContent s E) := mul_le_mul_right h _
    _ = hausdorffContent s E := by
        rw [← h2, ← mul_assoc, ENNReal.mul_inv_cancel h2ne h2top, one_mul]

/-! ## Proposition 2.20 (`thm:scaling`) -/

section Scaling

variable {X Y : Type*} [EMetricSpace X] [EMetricSpace Y]

/-- A map scaling all distances by `c` scales diameters by `c`. -/
private theorem ediam_image_of_edist_eq {f : X → Y} {c : ℝ≥0}
    (hdist : ∀ x y, edist (f x) (f y) = c * edist x y) (U : Set X) :
    ediam (f '' U) = c * ediam U := by
  simp only [ediam, iSup_image, hdist, ENNReal.mul_iSup]

/-- A map scaling all distances by `c` multiplies the weights for the gauge `t ↦ t ^ s`, `s ≥ 0`,
by `c ^ s`. -/
private theorem gaugeWeight_rpow_image_of_edist_eq {s : ℝ} (hs : 0 ≤ s) {f : X → Y} {c : ℝ≥0}
    (hdist : ∀ x y, edist (f x) (f y) = c * edist x y) (U : Set X) :
    gaugeWeight (fun t => t ^ s) (f '' U) = (c : ℝ≥0∞) ^ s * gaugeWeight (fun t => t ^ s) U := by
  simp only [gaugeWeight, image_nonempty, ediam_image_of_edist_eq hdist,
    ENNReal.mul_rpow_of_nonneg _ _ hs, ENNReal.mul_iSup]

/-- A bijection scaling all distances by `c ≠ 0` maps open sets to open sets. -/
private theorem isOpen_image_of_edist_eq {f : X → Y} (hf : Function.Bijective f) {c : ℝ≥0}
    (hc : c ≠ 0) (hdist : ∀ x y, edist (f x) (f y) = c * edist x y) {U : Set X} (hU : IsOpen U) :
    IsOpen (f '' U) := by
  set e := Equiv.ofBijective f hf
  have he : LipschitzWith c⁻¹ e.symm := fun u v => by
    obtain ⟨x, rfl⟩ := e.surjective u
    obtain ⟨y, rfl⟩ := e.surjective v
    rw [e.symm_apply_apply, e.symm_apply_apply, Equiv.ofBijective_apply, Equiv.ofBijective_apply,
      hdist, ENNReal.coe_inv hc, ← mul_assoc,
      ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.2 hc) ENNReal.coe_ne_top, one_mul]
  have himage : f '' U = e.symm ⁻¹' U := e.image_eq_preimage_symm U
  rw [himage]
  exact hU.preimage he.continuous

/-- Proposition 2.20 (`thm:scaling`): a bijection `E → F` that scales distances by `c > 0`
multiplies `𝓗^s` by `c^s`. -/
theorem scaling [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] {s : ℝ}
    (hs : 0 ≤ s) {E : Set X} {F : Set Y} {f : X → Y} {c : ℝ≥0} (hc : c ≠ 0) (hf : BijOn f E F)
    (hdist : ∀ x ∈ E, ∀ y ∈ E, edist (f x) (f y) = c * edist x y) :
    μH[s] F = (c : ℝ≥0∞) ^ s * μH[s] E := by
  rcases E.eq_empty_or_nonempty with rfl | ⟨x₀, -⟩
  · rw [← hf.image_eq, image_empty, measure_empty, measure_empty, mul_zero]
  have : Nonempty X := ⟨x₀⟩
  have hinv : InvOn (Function.invFunOn f E) f E F := hf.invOn_invFunOn
  have hf' : LipschitzOnWith c f E := fun x hx y hy => (hdist x hx y hy).le
  have hg : LipschitzOnWith c⁻¹ (Function.invFunOn f E) F := by
    intro u hu v hv
    obtain ⟨x, hx, rfl⟩ := hf.surjOn hu
    obtain ⟨y, hy, rfl⟩ := hf.surjOn hv
    rw [hinv.1 hx, hinv.1 hy, hdist x hx y hy, ENNReal.coe_inv hc, ← mul_assoc,
      ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.2 hc) ENNReal.coe_ne_top, one_mul]
  have h1 := hf'.hausdorffMeasure_image_le hs
  rw [hf.image_eq] at h1
  have h2 := hg.hausdorffMeasure_image_le hs
  rw [← hf.image_eq, hinv.1.image_image, hf.image_eq] at h2
  refine le_antisymm h1 ?_
  calc (c : ℝ≥0∞) ^ s * μH[s] E ≤ c ^ s * (((c⁻¹ : ℝ≥0) : ℝ≥0∞) ^ s * μH[s] F) := by gcongr
    _ = μH[s] F := by
      rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ hs, ← ENNReal.coe_mul, mul_inv_cancel₀ hc,
        ENNReal.coe_one, ENNReal.one_rpow, one_mul]

/-- The scaling of the δ-content under a similarity of the whole space, stated after
Proposition 2.20: `𝓗^s_δ(S(E)) = c^s 𝓗^s_{δ/c}(E)`. -/
theorem scaling_hausdorffDelta {s : ℝ} (hs : 0 ≤ s) {f : X → Y} (hf : Function.Bijective f)
    {c : ℝ≥0} (hc : c ≠ 0) (hdist : ∀ x y, edist (f x) (f y) = c * edist x y) (δ : ℝ≥0∞)
    (E : Set X) :
    hausdorffDelta s δ (f '' E) = (c : ℝ≥0∞) ^ s * hausdorffDelta s (δ / c) E := by
  have hc0 : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hc
  have hcs0 : (c : ℝ≥0∞) ^ s ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 hc0) ENNReal.coe_ne_top).ne'
  have hcs : (c : ℝ≥0∞) ^ s ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hs ENNReal.coe_ne_top
  have hfcont : Continuous f := (show LipschitzWith c f from fun x y => (hdist x y).le).continuous
  have hdiam : ∀ U : Set X, ediam (f '' U) < δ ↔ ediam U < δ / c := fun U => by
    rw [ediam_image_of_edist_eq hdist, ENNReal.lt_div_iff_mul_lt (Or.inl hc0)
      (Or.inl ENNReal.coe_ne_top), mul_comm]
  refine le_antisymm ?_ ?_
  · rw [← ENNReal.div_le_iff' hcs0 hcs]
    refine le_iInf fun U => le_iInf fun hU => le_iInf fun hUδ => le_iInf fun hEU => ?_
    rw [ENNReal.div_le_iff' hcs0 hcs, ← ENNReal.tsum_mul_left]
    refine iInf_le_of_le (fun i => f '' U i) <|
      iInf_le_of_le (fun i => isOpen_image_of_edist_eq hf hc hdist (hU i)) <|
      iInf_le_of_le (fun i => (hdiam _).2 (hUδ i)) <| iInf_le_of_le ?_ ?_
    · rw [← image_iUnion]
      exact image_mono hEU
    · simp only [gaugeWeight_rpow_image_of_edist_eq hs hdist, le_rfl]
  · refine le_iInf fun V => le_iInf fun hV => le_iInf fun hVδ => le_iInf fun hEV => ?_
    have himage : ∀ i, f '' (f ⁻¹' V i) = V i := fun i => image_preimage_eq _ hf.2
    calc (c : ℝ≥0∞) ^ s * hausdorffDelta s (δ / c) E
        ≤ c ^ s * ∑' i, gaugeWeight (fun t => t ^ s) (f ⁻¹' V i) := by
          gcongr
          refine iInf_le_of_le (fun i => f ⁻¹' V i) <|
            iInf_le_of_le (fun i => (hV i).preimage hfcont) <|
            iInf_le_of_le (fun i => ?_) <| iInf_le_of_le ?_ le_rfl
          · rw [← hdiam, himage]
            exact hVδ i
          · rw [← preimage_iUnion]
            exact image_subset_iff.1 hEV
      _ = ∑' i, gaugeWeight (fun t => t ^ s) (V i) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun i => ?_
          rw [← gaugeWeight_rpow_image_of_edist_eq hs hdist, himage]

/-- The scaling of the content under a similarity of the whole space, stated after
Proposition 2.20: `𝓗^s_∞(S(E)) = c^s 𝓗^s_∞(E)`. -/
theorem scaling_hausdorffContent {s : ℝ} (hs : 0 ≤ s) {f : X → Y} (hf : Function.Bijective f)
    {c : ℝ≥0} (hc : c ≠ 0) (hdist : ∀ x y, edist (f x) (f y) = c * edist x y) (E : Set X) :
    hausdorffContent s (f '' E) = (c : ℝ≥0∞) ^ s * hausdorffContent s E := by
  have hc0 : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hc
  have hcs0 : (c : ℝ≥0∞) ^ s ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 hc0) ENNReal.coe_ne_top).ne'
  have hcs : (c : ℝ≥0∞) ^ s ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hs ENNReal.coe_ne_top
  have hfcont : Continuous f := (show LipschitzWith c f from fun x y => (hdist x y).le).continuous
  refine le_antisymm ?_ ?_
  · rw [← ENNReal.div_le_iff' hcs0 hcs]
    refine le_iInf fun U => le_iInf fun hU => le_iInf fun hEU => ?_
    rw [ENNReal.div_le_iff' hcs0 hcs, ← ENNReal.tsum_mul_left]
    refine iInf_le_of_le (fun i => f '' U i) <|
      iInf_le_of_le (fun i => isOpen_image_of_edist_eq hf hc hdist (hU i)) <|
      iInf_le_of_le ?_ ?_
    · rw [← image_iUnion]
      exact image_mono hEU
    · simp only [gaugeWeight_rpow_image_of_edist_eq hs hdist, le_rfl]
  · refine le_iInf fun V => le_iInf fun hV => le_iInf fun hEV => ?_
    have himage : ∀ i, f '' (f ⁻¹' V i) = V i := fun i => image_preimage_eq _ hf.2
    calc (c : ℝ≥0∞) ^ s * hausdorffContent s E
        ≤ c ^ s * ∑' i, gaugeWeight (fun t => t ^ s) (f ⁻¹' V i) := by
          gcongr
          refine iInf_le_of_le (fun i => f ⁻¹' V i) <|
            iInf_le_of_le (fun i => (hV i).preimage hfcont) <| iInf_le_of_le ?_ le_rfl
          rw [← preimage_iUnion]
          exact image_subset_iff.1 hEV
      _ = ∑' i, gaugeWeight (fun t => t ^ s) (V i) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun i => ?_
          rw [← gaugeWeight_rpow_image_of_edist_eq hs hdist, himage]

/-! Translation and isometry invariance, the case `c = 1`, is
`IsometryEquiv.hausdorffMeasure_image`. -/

example [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] (e : X ≃ᵢ Y)
    (s : ℝ) (E : Set X) : μH[s] (e '' E) = μH[s] E :=
  e.hausdorffMeasure_image s E

end Scaling

/-! ## Theorem 2.22 (`thm:equal-measure-content`) -/

/-- Theorem 2.22 (`thm:equal-measure-content`): if `𝓗^s(F) = 𝓗^s_∞(F) < ∞`, then content and
measure agree on every measurable subset of `F`. -/
theorem equal_measure_content {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {s : ℝ} (hs : 0 ≤ s) {E F : Set X} (hF : μH[s] F = hausdorffContent s F)
    (hFfin : μH[s] F ≠ ∞) (hE : NullMeasurableSet E μH[s]) (hEF : E ⊆ F) :
    μH[s] E = hausdorffContent s E := by
  have hle : ∀ A : Set X, hausdorffContent s A ≤ μH[s] A := fun A => by
    rw [← hausdorffMeasureGauge_rpow hs]
    exact (hausdorffContentGauge_le_hausdorffDeltaGauge _ 1 A).trans
      (hausdorffDeltaGauge_le_hausdorffMeasureGauge _ zero_lt_one A)
  refine le_antisymm ?_ (hle E)
  have hsplit : μH[s] E + μH[s] (F \ E) = μH[s] F := by
    rw [← measure_inter_add_sdiff₀ F hE, inter_eq_right.2 hEF]
  have hsub : hausdorffContent s F ≤ hausdorffContent s E + hausdorffContent s (F \ E) := by
    calc hausdorffContent s F = hausdorffContentOuter s (E ∪ F \ E) := by
          rw [union_sdiff_cancel hEF, coe_hausdorffContentOuter]
      _ ≤ _ := measure_union_le _ _
  have hfin : μH[s] (F \ E) ≠ ∞ := ne_top_of_le_ne_top hFfin (measure_mono sdiff_subset)
  refine ENNReal.le_of_add_le_add_right hfin ?_
  calc μH[s] E + μH[s] (F \ E) = hausdorffContent s F := hsplit.trans hF
    _ ≤ hausdorffContent s E + hausdorffContent s (F \ E) := hsub
    _ ≤ hausdorffContent s E + μH[s] (F \ E) := by
      gcongr
      exact hle _

/-! ## Proposition 2.24 (`thm:dimension-open-sets`)

This is `Real.dimH_of_nonempty_interior`, for every finite-dimensional real normed space. -/

example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {U : Set F}
    (hU : IsOpen U) (hne : U.Nonempty) : dimH U = Module.finrank ℝ F :=
  Real.dimH_of_nonempty_interior (by rwa [hU.interior_eq])

end GeometricMeasureTheory
