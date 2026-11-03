module

public import AnalyticESC.Literature.Rapaport.Analytic.Dyadic
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.ExactDimensionEntropy

@[expose] public section

/-!
# Dyadic entropy of measures on the unit interval

Tools on dyadic entropy used in Section 4 of A. Rapaport, *Dimension of self-conformal measures
associated to an exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2. All entropies
are `ent θ (cellIdx ℓ)`, Rapaport's `H(θ, 𝒟_ℓ)` in nats.

## Main declarations

* `cellRange`, `cellIdx_mem_cellRange`, `ent_cellIdx_eq_sum`: for a measure carried by `I`, the
  entropy is a finite sum over the cells meeting `I`.
* `ent_cellIdx_le_of_compl_I`: `H(θ, 𝒟_ℓ) ≤ log (2^ℓ + 2)` for a probability measure on `I`.
* `ent_map_of_aemeasurable`, `ent_map_scale`: images, and the scaling identity
  `H(S_{2^L} θ, 𝒟_ℓ) = H(θ, 𝒟_{ℓ+L})`.
* `tendsto_ent_div_of_isExactDim`: Young's identity (Rapaport (2.9)) for a measure on `I`:
  `H(θ, 𝒟_n) / n → d log 2`, from the vendored theorem
  `ExactOverlaps.Entropy.normalized_entropy_limit_of_exact_dimension`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Main.EntropyTools`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic.SectionFour

open MeasureTheory ProbabilityTheory Set Filter Topology FractalGeometry.SelfConformal
open FractalGeometry.Rapaport.Analytic
open scoped ENNReal

/-! ### Cells meeting the unit interval -/

/-- The indices `0, …, 2^ℓ` of the level-`ℓ` cells meeting `I`. -/
def cellRange (ℓ : ℕ) : Finset ℤ := Finset.Icc 0 (2 ^ ℓ)

/-- The cell index of a point of `I` lies in `cellRange`. -/
theorem cellIdx_mem_cellRange (ℓ : ℕ) {y : ℝ} (hy : y ∈ AnalyticESC.I) :
    cellIdx ℓ y ∈ cellRange ℓ := by
  have h2 : (0 : ℝ) < 2 ^ ℓ := by positivity
  rw [cellRange, Finset.mem_Icc, cellIdx]
  constructor
  · exact Int.floor_nonneg.2 (mul_nonneg h2.le hy.1)
  · have : (2 : ℝ) ^ ℓ * y ≤ ((2 ^ ℓ : ℤ) : ℝ) := by
      push_cast
      nlinarith [hy.2]
    exact Int.floor_le_iff.2 (by linarith)

/-- A measure carried by `I` gives no mass to the cells outside `cellRange`. -/
theorem measure_cellIdx_preimage_eq_zero {θ : Measure ℝ} (hθ : θ AnalyticESC.Iᶜ = 0) {ℓ : ℕ}
    {c : ℤ} (hc : c ∉ cellRange ℓ) : θ (cellIdx ℓ ⁻¹' {c}) = 0 := by
  refine measure_mono_null (fun y hy => ?_) hθ
  intro hyI
  rw [mem_preimage, mem_singleton_iff] at hy
  exact hc (hy ▸ cellIdx_mem_cellRange ℓ hyI)

/-- For a measure carried by `I`, the dyadic labels have finitely many values of positive mass. -/
theorem finiteLabels_cellIdx {θ : Measure ℝ} (hθ : θ AnalyticESC.Iᶜ = 0) (ℓ : ℕ) :
    FiniteLabels θ (cellIdx ℓ) :=
  finiteLabels_of_subset (cellRange ℓ) fun _ hb => by
    by_contra hc
    exact hb (measure_cellIdx_preimage_eq_zero hθ hc)

/-- For a measure carried by `I`, `H(θ, 𝒟_ℓ)` is a sum over the cells meeting `I`. -/
theorem ent_cellIdx_eq_sum {θ : Measure ℝ} (hθ : θ AnalyticESC.Iᶜ = 0) (ℓ : ℕ) :
    ent θ (cellIdx ℓ) = ∑ c ∈ cellRange ℓ, Real.negMulLog (θ.real (cellIdx ℓ ⁻¹' {c})) :=
  ent_eq_sum_of_subset _ fun _ hb => by
    by_contra hc
    exact hb (measure_cellIdx_preimage_eq_zero hθ hc)

/-- `I` carries almost every point of a measure with `θ Iᶜ = 0`. -/
theorem ae_mem_I_of_compl {X : Type*} [MeasurableSpace X] {θ : Measure X} {F : X → ℝ}
    (hF : θ {x | F x ∉ AnalyticESC.I} = 0) : ∀ᵐ x ∂θ, F x ∈ AnalyticESC.I := by
  rw [ae_iff]
  simpa using hF

/-- `H(θ, 𝒟_ℓ) ≤ log (2^ℓ + 2)` for a probability measure carried by `I`. -/
theorem ent_cellIdx_le_of_compl_I {θ : Measure ℝ} [IsProbabilityMeasure θ]
    (hθ : θ AnalyticESC.Iᶜ = 0) (ℓ : ℕ) : ent θ (cellIdx ℓ) ≤ Real.log (2 ^ ℓ + 2) := by
  have h := ent_cellIdx_comp_le_log (θ := θ) (F := id) measurable_id (a := 0) (b := 1)
    zero_le_one ℓ (mem_ae_iff.2 hθ)
  simpa using h

/-- `log (2^ℓ + 2) ≤ (ℓ + 2) log 2`. -/
theorem log_two_pow_add_two_le (ℓ : ℕ) : Real.log (2 ^ ℓ + 2) ≤ (ℓ + 2) * Real.log 2 := by
  have h : (2 : ℝ) ^ ℓ + 2 ≤ 2 ^ (ℓ + 2) := by
    rw [pow_add]
    have : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
    nlinarith
  calc Real.log (2 ^ ℓ + 2) ≤ Real.log (2 ^ (ℓ + 2)) :=
        Real.log_le_log (by positivity) h
    _ = (ℓ + 2) * Real.log 2 := by
        rw [Real.log_pow]
        push_cast
        ring

/-! ### Images and scaling -/

/-- The entropy of an image measure is the entropy of the pulled back labelling, for an almost
everywhere measurable map. -/
theorem ent_map_of_aemeasurable {X : Type*} [MeasurableSpace X] {θ : Measure X} {ψ : X → ℝ}
    (hψ : AEMeasurable ψ θ) (ℓ : ℕ) :
    ent (θ.map ψ) (cellIdx ℓ) = ent θ (cellIdx ℓ ∘ ψ) := by
  rw [Measure.map_congr hψ.ae_eq_mk, ent_map hψ.measurable_mk (measurable_cellIdx ℓ)]
  refine ent_congr_ae ?_
  filter_upwards [hψ.ae_eq_mk] with x hx
  simp [hx]

/-- `cellIdx ℓ (2^L y) = cellIdx (ℓ + L) y`. -/
theorem cellIdx_two_pow_mul (ℓ L : ℕ) (y : ℝ) : cellIdx ℓ (2 ^ L * y) = cellIdx (ℓ + L) y := by
  unfold cellIdx
  rw [pow_add, mul_assoc]

/-- The scaling identity `H(S_{2^L} θ, 𝒟_ℓ) = H(θ, 𝒟_{ℓ+L})`. -/
theorem ent_map_scale (θ : Measure ℝ) (ℓ L : ℕ) :
    ent (θ.map fun y => 2 ^ L * y) (cellIdx ℓ) = ent θ (cellIdx (ℓ + L)) := by
  rw [ent_map (by fun_prop : Measurable fun y : ℝ => 2 ^ L * y) (measurable_cellIdx ℓ)]
  congr 1
  funext y
  exact cellIdx_two_pow_mul ℓ L y

/-! ### Young's identity -/

/-- The vendored finite entropy depends only on the law. -/
theorem finiteEntropy_congr {α : Type*} {p q : PMF α} (h : p = q) (hp : p.support.Finite)
    (hq : q.support.Finite) : ExactOverlaps.Entropy.finiteEntropy p hp =
      ExactOverlaps.Entropy.finiteEntropy q hq := by
  subst h
  rfl

/-- The vendored dyadic quantisation at a natural level is `cellIdx`. -/
theorem dyadicQuantize_natCast (n : ℕ) :
    ExactOverlaps.Entropy.dyadicQuantize (n : ℤ) = cellIdx n := by
  funext x
  simp [ExactOverlaps.Entropy.dyadicQuantize, cellIdx, zpow_natCast]

/-- Young's identity, Rapaport (2.9): an exact dimensional probability measure on `I` of dimension
`d` has `H(θ, 𝒟_n) / n → d log 2` (nats). -/
theorem tendsto_ent_div_of_isExactDim {θ : Measure ℝ} [IsProbabilityMeasure θ]
    (hθ : θ AnalyticESC.Iᶜ = 0) {d : ℝ} (hd : FractalGeometry.IsExactDim θ d) :
    Tendsto (fun n : ℕ => ent θ (cellIdx n) / n) atTop (𝓝 (d * Real.log 2)) := by
  set P : ProbabilityMeasure ℝ := ⟨θ, inferInstance⟩ with hP
  have hb : ExactOverlaps.Entropy.HasBoundedSupport P := ⟨0, 1, mem_ae_iff.2 hθ⟩
  have hd' : ExactOverlaps.HasExactDimension (P : Measure ℝ) d := hd
  have h := ExactOverlaps.Entropy.normalized_entropy_limit_of_exact_dimension P hb hd'
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have heq : ∀ n : ℕ, 0 < n → ent θ (cellIdx n) / n =
      ExactOverlaps.Entropy.normalizedDyadicEntropy P hb n * Real.log 2 := by
    intro n hn
    have hlaw : ExactOverlaps.Entropy.dyadicLaw P n = (θ.map (cellIdx n)).toPMF := by
      apply PMF.toMeasure_injective
      rw [ExactOverlaps.Entropy.dyadicLaw_toMeasure, Measure.toPMF_toMeasure,
        dyadicQuantize_natCast]
      rfl
    have hfin := finiteLabels_cellIdx hθ n
    rw [ExactOverlaps.Entropy.normalizedDyadicEntropy, ExactOverlaps.Entropy.dyadicEntropy,
      finiteEntropy_congr hlaw _ ((finiteLabels_iff_toPMF (measurable_cellIdx n)).1 hfin),
      ← ent_eq_finiteEntropy (measurable_cellIdx n) hfin]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp
  have h2 := h.mul_const (Real.log 2)
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (heq n hn).symm

/-! ### Conditional entropy as a sum over cells -/

/-- The summand `G(a, b) = a log b - a log a` of the conditional entropy
`H(θ, 𝒟_{ℓ+s} ∣ 𝒟_ℓ) = ∑_A G(θ(A), θ(B_A))`, where `B_A` is the level-`ℓ` cell containing the
level-`(ℓ+s)` cell `A`. -/
noncomputable def condTerm (a b : ℝ) : ℝ := a * Real.log b - a * Real.log a

/-- A level-`(ℓ+s)` cell lies in the level-`ℓ` cell with index `c / 2^s`. -/
theorem cellIdx_preimage_inter (ℓ s : ℕ) (c' c : ℤ) :
    cellIdx ℓ ⁻¹' {c'} ∩ cellIdx (ℓ + s) ⁻¹' {c} =
      if c / 2 ^ s = c' then cellIdx (ℓ + s) ⁻¹' {c} else ∅ := by
  ext y
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
  rw [cellIdx_eq_ediv ℓ s y]
  split_ifs with h
  · simp only [mem_preimage, mem_singleton_iff]
    constructor
    · exact fun h' => h'.2
    · intro h'
      exact ⟨by rw [h', h], h'⟩
  · simp only [mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    exact h (h2 ▸ h1)

/-- The index `c / 2^s` of the coarse cell of a fine cell meeting `I` lies in `cellRange ℓ`. -/
theorem ediv_mem_cellRange {ℓ s : ℕ} {c : ℤ} (hc : c ∈ cellRange (ℓ + s)) :
    c / 2 ^ s ∈ cellRange ℓ := by
  rw [cellRange, Finset.mem_Icc] at hc ⊢
  have h2 : (0 : ℤ) < 2 ^ s := by positivity
  refine ⟨Int.ediv_nonneg hc.1 h2.le, ?_⟩
  calc c / 2 ^ s ≤ 2 ^ (ℓ + s) / 2 ^ s := Int.ediv_le_ediv h2 hc.2
    _ = 2 ^ ℓ := by rw [pow_add, Int.mul_ediv_cancel _ h2.ne']

/-- The coarse cell is the union of its fine cells: `θ(B) = ∑_{A ⊆ B} θ(A)`. -/
theorem sum_measureReal_fine_cells {θ : Measure ℝ} [IsFiniteMeasure θ]
    (hθ : θ AnalyticESC.Iᶜ = 0) (ℓ s : ℕ) (c' : ℤ) :
    ∑ c ∈ cellRange (ℓ + s) with c / 2 ^ s = c', θ.real (cellIdx (ℓ + s) ⁻¹' {c}) =
      θ.real (cellIdx ℓ ⁻¹' {c'}) := by
  have h := sum_measureReal_inter_fiber (θ := θ) (measurable_cellIdx (ℓ + s))
    (cellRange (ℓ + s)) (fun b hb => by
      by_contra hc
      exact hb (measure_cellIdx_preimage_eq_zero hθ hc))
    (A := cellIdx ℓ ⁻¹' {c'}) (measurable_cellIdx ℓ (measurableSet_singleton c'))
  rw [← h, Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [cellIdx_preimage_inter]
  split_ifs <;> simp

/-- The conditional entropy `H(θ, 𝒟_{ℓ+s}) - H(θ, 𝒟_ℓ)` of a finite measure on `I` as a sum over
the fine cells. -/
theorem ent_sub_ent_eq_sum {θ : Measure ℝ} [IsFiniteMeasure θ] (hθ : θ AnalyticESC.Iᶜ = 0)
    (ℓ s : ℕ) :
    ent θ (cellIdx (ℓ + s)) - ent θ (cellIdx ℓ) =
      ∑ c ∈ cellRange (ℓ + s), condTerm (θ.real (cellIdx (ℓ + s) ⁻¹' {c}))
        (θ.real (cellIdx ℓ ⁻¹' {c / 2 ^ s})) := by
  have hsplit : ∀ c, condTerm (θ.real (cellIdx (ℓ + s) ⁻¹' {c}))
      (θ.real (cellIdx ℓ ⁻¹' {c / 2 ^ s})) =
      θ.real (cellIdx (ℓ + s) ⁻¹' {c}) * Real.log (θ.real (cellIdx ℓ ⁻¹' {c / 2 ^ s})) +
        Real.negMulLog (θ.real (cellIdx (ℓ + s) ⁻¹' {c})) := by
    intro c
    rw [condTerm, Real.negMulLog]
    ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, ← ent_cellIdx_eq_sum hθ, ent_cellIdx_eq_sum hθ ℓ]
  have hfib := Finset.sum_fiberwise_of_maps_to (s := cellRange (ℓ + s)) (t := cellRange ℓ)
    (g := fun c => c / 2 ^ s) (fun c hc => ediv_mem_cellRange hc)
    (fun c => θ.real (cellIdx (ℓ + s) ⁻¹' {c}) * Real.log (θ.real (cellIdx ℓ ⁻¹' {c / 2 ^ s})))
  rw [← hfib]
  have hin : ∀ c' ∈ cellRange ℓ, ∑ c ∈ cellRange (ℓ + s) with c / 2 ^ s = c',
      θ.real (cellIdx (ℓ + s) ⁻¹' {c}) * Real.log (θ.real (cellIdx ℓ ⁻¹' {c / 2 ^ s})) =
      -Real.negMulLog (θ.real (cellIdx ℓ ⁻¹' {c'})) := by
    intro c' _
    rw [Finset.sum_congr rfl fun c hc => by rw [(Finset.mem_filter.1 hc).2], ← Finset.sum_mul,
      sum_measureReal_fine_cells hθ ℓ s c', Real.negMulLog]
    ring
  rw [Finset.sum_congr rfl hin, Finset.sum_neg_distrib]
  ring

/-- The tangent inequality behind the log-sum inequality: for `0 ≤ a ≤ b` and `t > 0`,
`G(a, b) ≤ -a (log t + 1) + b t`. -/
theorem condTerm_le {a b t : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 < t) :
    condTerm a b ≤ -a * (Real.log t + 1) + b * t := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp [condTerm]
    exact mul_nonneg (by linarith) ht.le
  · have hb : 0 < b := ha'.trans_le hab
    have hy : 0 < b * t / a := by positivity
    have hlog := Real.log_le_sub_one_of_pos hy
    rw [Real.log_div (by positivity) ha'.ne', Real.log_mul hb.ne' ht.ne'] at hlog
    have : a * (Real.log b + Real.log t - Real.log a) ≤ a * (b * t / a - 1) :=
      mul_le_mul_of_nonneg_left hlog ha
    rw [condTerm]
    have h2 : a * (b * t / a - 1) = b * t - a := by field_simp
    nlinarith

/-- `|G(a, b)| ≤ 1` for `0 ≤ a ≤ b ≤ 1`. -/
theorem abs_condTerm_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |condTerm a b| ≤ 1 := by
  have hb0 : 0 ≤ b := ha.trans hab
  have h1 : 0 ≤ -a * Real.log a := by
    have := Real.negMulLog_nonneg ha (hab.trans hb)
    rwa [Real.negMulLog] at this
  have h2 : -a * Real.log a ≤ 1 := by
    have := Real.negMulLog_le_one_sub_self ha
    rw [Real.negMulLog] at this
    linarith
  have h3 : a * Real.log b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha (Real.log_nonpos hb0 hb)
  have h4 : -1 ≤ a * Real.log b := by
    have h5 : b * Real.log b ≤ a * Real.log b :=
      mul_le_mul_of_nonpos_right hab (Real.log_nonpos hb0 hb)
    have h6 := Real.self_sub_one_le_mul_log hb0
    linarith
  rw [condTerm, abs_le]
  constructor <;> linarith

/-! ### Concavity of conditional entropy under integral mixtures -/

section Mixture

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
  {θ : α → Measure ℝ} [∀ x, IsProbabilityMeasure (θ x)]
  {ρ : Measure ℝ} [IsProbabilityMeasure ρ]

omit [∀ x, IsProbabilityMeasure (θ x)] [IsProbabilityMeasure μ] in
/-- The masses of a measurable family of measures are measurable. -/
theorem measurable_measureReal_of_kernel
    (hmeas : ∀ s : Set ℝ, MeasurableSet s → Measurable fun x => θ x s) {A : Set ℝ}
    (hA : MeasurableSet A) : Measurable fun x => (θ x).real A :=
  ENNReal.measurable_toReal.comp (hmeas A hA)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ] in
/-- The real masses of a mixture are the integrals of the masses. -/
theorem integral_measureReal_of_mixture
    (hmeas : ∀ s : Set ℝ, MeasurableSet s → Measurable fun x => θ x s)
    (hρ : ∀ s : Set ℝ, MeasurableSet s → ρ s = ∫⁻ x, θ x s ∂μ) {A : Set ℝ}
    (hA : MeasurableSet A) : ∫ x, (θ x).real A ∂μ = ρ.real A := by
  simp only [measureReal_def]
  rw [integral_toReal (hmeas A hA).aemeasurable (Eventually.of_forall fun x => measure_lt_top _ _),
    hρ A hA]

/-- The log-sum inequality for one pair of nested sets: for a mixture `ρ = ∫ θ_x dμ(x)` and
`A ⊆ B`, `∫ G(θ_x(A), θ_x(B)) dμ ≤ G(ρ(A), ρ(B))`. -/
theorem integral_condTerm_le
    (hmeas : ∀ s : Set ℝ, MeasurableSet s → Measurable fun x => θ x s)
    (hρ : ∀ s : Set ℝ, MeasurableSet s → ρ s = ∫⁻ x, θ x s ∂μ) {A B : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    ∫ x, condTerm ((θ x).real A) ((θ x).real B) ∂μ ≤ condTerm (ρ.real A) (ρ.real B) := by
  have hmA := measurable_measureReal_of_kernel hmeas hA
  have hmB := measurable_measureReal_of_kernel hmeas hB
  have hle : ∀ x, (θ x).real A ≤ (θ x).real B := fun x => measureReal_mono hAB
  have hmeasG : Measurable fun x => condTerm ((θ x).real A) ((θ x).real B) := by
    unfold condTerm
    exact (hmA.mul (Real.measurable_log.comp hmB)).sub (hmA.mul (Real.measurable_log.comp hmA))
  have hintG : Integrable (fun x => condTerm ((θ x).real A) ((θ x).real B)) μ :=
    Integrable.of_bound hmeasG.aestronglyMeasurable 1 (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact abs_condTerm_le measureReal_nonneg (hle x) measureReal_le_one)
  rcases (measureReal_nonneg (μ := ρ) (s := A)).eq_or_lt with h0 | hpos
  · have h0' : ∫⁻ x, θ x A ∂μ = 0 := by
      rw [← hρ A hA]
      rw [measureReal_def, eq_comm, ENNReal.toReal_eq_zero_iff] at h0
      exact h0.resolve_right (measure_ne_top _ _)
    have hae := (lintegral_eq_zero_iff (hmeas A hA)).1 h0'
    rw [← h0]
    refine le_of_eq ?_
    calc ∫ x, condTerm ((θ x).real A) ((θ x).real B) ∂μ = ∫ _x, (0 : ℝ) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hae] with x hx
          simp [condTerm, measureReal_def, hx]
      _ = condTerm 0 (ρ.real B) := by simp [condTerm]
  · have hBpos : 0 < ρ.real B := hpos.trans_le (measureReal_mono hAB)
    set t := ρ.real A / ρ.real B with ht
    have htpos : 0 < t := div_pos hpos hBpos
    have hpt : ∀ x, condTerm ((θ x).real A) ((θ x).real B) ≤
        -(θ x).real A * (Real.log t + 1) + (θ x).real B * t := fun x =>
      condTerm_le measureReal_nonneg (hle x) htpos
    have hintA : Integrable (fun x => (θ x).real A) μ :=
      Integrable.of_mem_Icc 0 1 hmA.aemeasurable
        (Eventually.of_forall fun x => ⟨measureReal_nonneg, measureReal_le_one⟩)
    have hintB : Integrable (fun x => (θ x).real B) μ :=
      Integrable.of_mem_Icc 0 1 hmB.aemeasurable
        (Eventually.of_forall fun x => ⟨measureReal_nonneg, measureReal_le_one⟩)
    have hA' : Integrable (fun x => -(θ x).real A * (Real.log t + 1)) μ := hintA.neg.mul_const _
    have hB' : Integrable (fun x => (θ x).real B * t) μ := hintB.mul_const _
    have hint2 : Integrable (fun x => -(θ x).real A * (Real.log t + 1) + (θ x).real B * t) μ :=
      hA'.add hB'
    calc ∫ x, condTerm ((θ x).real A) ((θ x).real B) ∂μ
        ≤ ∫ x, (-(θ x).real A * (Real.log t + 1) + (θ x).real B * t) ∂μ :=
          integral_mono hintG hint2 hpt
      _ = -ρ.real A * (Real.log t + 1) + ρ.real B * t := by
          rw [integral_add hA' hB', integral_mul_const,
            integral_mul_const, integral_neg, integral_measureReal_of_mixture hmeas hρ hA,
            integral_measureReal_of_mixture hmeas hρ hB]
      _ = condTerm (ρ.real A) (ρ.real B) := by
          rw [condTerm, ht, Real.log_div hpos.ne' hBpos.ne']
          field_simp
          ring

/-- Concavity of conditional dyadic entropy under integral mixtures: if `ρ = ∫ θ_x dμ(x)` with
all `θ_x` carried by `I`, then
`∫ (H(θ_x, 𝒟_{ℓ+s}) - H(θ_x, 𝒟_ℓ)) dμ(x) ≤ H(ρ, 𝒟_{ℓ+s}) - H(ρ, 𝒟_ℓ)`. -/
theorem integral_ent_sub_le (hθI : ∀ x, θ x AnalyticESC.Iᶜ = 0)
    (hmeas : ∀ s : Set ℝ, MeasurableSet s → Measurable fun x => θ x s)
    (hρ : ∀ s : Set ℝ, MeasurableSet s → ρ s = ∫⁻ x, θ x s ∂μ) (ℓ s : ℕ) :
    ∫ x, (ent (θ x) (cellIdx (ℓ + s)) - ent (θ x) (cellIdx ℓ)) ∂μ ≤
      ent ρ (cellIdx (ℓ + s)) - ent ρ (cellIdx ℓ) := by
  have hρI : ρ AnalyticESC.Iᶜ = 0 := by
    rw [hρ _ measurableSet_Icc.compl]
    simp [hθI]
  have hcell : ∀ (ℓ' : ℕ) (c : ℤ), MeasurableSet (cellIdx ℓ' ⁻¹' {c}) := fun ℓ' c =>
    measurable_cellIdx ℓ' (measurableSet_singleton c)
  rw [ent_sub_ent_eq_sum hρI]
  rw [integral_congr_ae (Eventually.of_forall fun x => ent_sub_ent_eq_sum (hθI x) ℓ s)]
  rw [integral_finsetSum]
  · refine Finset.sum_le_sum fun c _ => integral_condTerm_le hmeas hρ (hcell _ _) (hcell _ _) ?_
    intro y hy
    simp only [mem_preimage, mem_singleton_iff] at hy ⊢
    rw [cellIdx_eq_ediv ℓ s y, hy]
  · intro c _
    have hmA := measurable_measureReal_of_kernel hmeas (hcell (ℓ + s) c)
    have hmB := measurable_measureReal_of_kernel hmeas (hcell ℓ (c / 2 ^ s))
    have hmeasG : Measurable fun x => condTerm ((θ x).real (cellIdx (ℓ + s) ⁻¹' {c}))
        ((θ x).real (cellIdx ℓ ⁻¹' {c / 2 ^ s})) := by
      unfold condTerm
      exact (hmA.mul (Real.measurable_log.comp hmB)).sub
        (hmA.mul (Real.measurable_log.comp hmA))
    refine Integrable.of_bound hmeasG.aestronglyMeasurable 1 (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    refine abs_condTerm_le measureReal_nonneg (measureReal_mono ?_) measureReal_le_one
    intro y hy
    simp only [mem_preimage, mem_singleton_iff] at hy ⊢
    rw [cellIdx_eq_ediv ℓ s y, hy]

omit [∀ x, IsProbabilityMeasure (θ x)] [IsProbabilityMeasure μ] in
/-- The entropy of a measurable family of measures carried by `I` is measurable. -/
theorem measurable_ent_of_kernel (hθI : ∀ x, θ x AnalyticESC.Iᶜ = 0)
    (hmeas : ∀ s : Set ℝ, MeasurableSet s → Measurable fun x => θ x s) (ℓ : ℕ) :
    Measurable fun x => ent (θ x) (cellIdx ℓ) := by
  simp_rw [ent_cellIdx_eq_sum (hθI _)]
  refine Finset.measurable_sum _ fun c _ => ?_
  exact Real.continuous_negMulLog.measurable.comp
    (measurable_measureReal_of_kernel hmeas (measurable_cellIdx ℓ (measurableSet_singleton c)))

end Mixture

end FractalGeometry.Rapaport.Analytic.SectionFour
