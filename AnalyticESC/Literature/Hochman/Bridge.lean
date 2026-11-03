module

public import AnalyticESC.Literature.Hochman.Cells
public import AnalyticESC.Literature.ExactOverlaps.Entropy.SufficientInverse

@[expose] public section

/-!
# Bridge to the dyadic entropy of the Kittle–Kogler library

The vendored library `ExactOverlaps` (Kittle–Kogler) works with probability measures
`μ : ProbabilityMeasure ℝ` of bounded support, the discrete laws `dyadicLaw μ i` of the dyadic
cell labels `dyadicQuantize i x = ⌊2^i x⌋` at integer levels, and the Shannon entropy
`ExactOverlaps.Entropy.dyadicEntropy` in nats. This file identifies these objects with the shared
vocabulary `FractalGeometry.SelfConformal` (natural levels, entropies in bits, raw components as
measures), for use in the proof of Hochman's entropy growth theorem (Hochman, Ann. of Math. 180
(2014), Theorem 2.8).

## Main declarations

* `cellIdx_eq_dyadicQuantize`, `cell_eq_dyadicCell`, `dyadicLaw_toReal`: cells and labels.
* `toPM`, `hasBoundedSupport_toPM`, `hasBoundedSupport_of_compl`: probability measures with
  bounded support.
* `kDyadicEntropy_eq`, `normalizedDyadicEntropy_eq`: Kittle–Kogler's entropy is our entropy times
  `log 2`, and their normalised entropy is `H(μ, 𝒟_n) / n` in bits.
* `rawComponent_eq_componentAt`: their raw components are our components.
* `integral_comp_cellIdx`: the integral of a function of the cell index is a finite sum over the
  cells meeting the support.
* `sum_support_eq_sum_Icc`: sums over the support of `dyadicLaw μ n` as sums over cell indices.

Copied from the library `FractalGeometry` (module `FractalGeometry.Hochman.Bridge`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Hochman

open MeasureTheory Set FractalGeometry.SelfConformal
open ExactOverlaps.Entropy (dyadicQuantize dyadicCell dyadicLaw HasBoundedSupport rawComponent
  dyadicLaw_apply dyadicLaw_support_finite dyadicLaw_support_subset)
open scoped ENNReal

/-! ### Cells and labels -/

/-- Our cell index is Kittle–Kogler's dyadic label at a natural level. -/
theorem cellIdx_eq_dyadicQuantize (n : ℕ) (x : ℝ) : cellIdx n x = dyadicQuantize n x := by
  rw [cellIdx, dyadicQuantize, zpow_natCast]

/-- Our cells are Kittle–Kogler's dyadic cells at natural levels. -/
theorem cell_eq_dyadicCell (n : ℕ) (k : ℤ) : cell n k = dyadicCell n k := by
  ext x
  rw [mem_cell_iff, cellIdx_eq_dyadicQuantize]
  rfl

/-- The weights of the discrete law of the labels are the masses of the cells. -/
theorem dyadicLaw_toReal (μ : ProbabilityMeasure ℝ) (n : ℕ) (k : ℤ) :
    (dyadicLaw μ n k).toReal = (μ : Measure ℝ).real (cell n k) := by
  rw [dyadicLaw_apply, cell_eq_dyadicCell]
  rfl

/-- The weights vanish off the support. -/
theorem measureReal_cell_eq_zero_of_not_mem_support (μ : ProbabilityMeasure ℝ) {n : ℕ} {k : ℤ}
    (hk : k ∉ (dyadicLaw μ n).support) : (μ : Measure ℝ).real (cell n k) = 0 := by
  rw [← dyadicLaw_toReal, (PMF.apply_eq_zero_iff _ _).2 hk, ENNReal.toReal_zero]

/-! ### Probability measures of bounded support -/

/-- A probability measure on `ℝ`, bundled. -/
noncomputable def toPM (θ : Measure ℝ) [IsProbabilityMeasure θ] : ProbabilityMeasure ℝ :=
  ⟨θ, inferInstance⟩

/-- The underlying measure of `toPM θ` is `θ`. -/
@[simp]
theorem toPM_coe (θ : Measure ℝ) [IsProbabilityMeasure θ] : ((toPM θ : ProbabilityMeasure ℝ) :
    Measure ℝ) = θ := rfl

/-- A measure carried by a compact interval has bounded support in the sense of Kittle–Kogler. -/
theorem hasBoundedSupport_of_compl (μ : ProbabilityMeasure ℝ) {a b : ℝ}
    (h : (μ : Measure ℝ) (Icc a b)ᶜ = 0) : HasBoundedSupport μ :=
  ⟨a, b, ae_iff.2 h⟩

/-- A probability measure carried by a compact interval has bounded support. -/
theorem hasBoundedSupport_toPM (θ : Measure ℝ) [IsProbabilityMeasure θ] {a b : ℝ}
    (h : θ (Icc a b)ᶜ = 0) : HasBoundedSupport (toPM θ) :=
  hasBoundedSupport_of_compl (toPM θ) h

/-- Bounded support as a null complement. -/
theorem exists_compl_eq_zero_of_hasBoundedSupport {μ : ProbabilityMeasure ℝ}
    (h : HasBoundedSupport μ) : ∃ a b : ℝ, (μ : Measure ℝ) (Icc a b)ᶜ = 0 := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨a, b, ae_iff.1 hab⟩

/-! ### Entropies -/

/-- Kittle–Kogler's dyadic entropy (nats) at a natural level is our dyadic entropy (bits) times
`log 2`. -/
theorem kDyadicEntropy_eq (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (n : ℕ) :
    ExactOverlaps.Entropy.dyadicEntropy μ hμ n = dyadicEntropy (μ : Measure ℝ) n * Real.log 2 := by
  rw [dyadicEntropy, div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne']
  unfold ExactOverlaps.Entropy.dyadicEntropy ExactOverlaps.Entropy.finiteEntropy
  symm
  rw [tsum_eq_sum (s := (dyadicLaw_support_finite μ hμ n).toFinset)]
  · exact Finset.sum_congr rfl fun k _ => by rw [dyadicLaw_toReal]
  · intro k hk
    rw [Set.Finite.mem_toFinset] at hk
    rw [measureReal_cell_eq_zero_of_not_mem_support μ hk, Real.negMulLog_zero]

/-- Kittle–Kogler's normalised entropy is `H(μ, 𝒟_n) / n` in bits. -/
theorem normalizedDyadicEntropy_eq (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (n : ℕ) :
    ExactOverlaps.Entropy.normalizedDyadicEntropy μ hμ n = dyadicEntropy (μ : Measure ℝ) n / n := by
  rw [ExactOverlaps.Entropy.normalizedDyadicEntropy, kDyadicEntropy_eq,
    mul_div_mul_right _ _ (Real.log_pos one_lt_two).ne']

/-- Kittle–Kogler's raw components are our components. -/
theorem rawComponent_eq_componentAt (μ : ProbabilityMeasure ℝ) (n : ℕ)
    (k : (dyadicLaw μ n).support) :
    (rawComponent μ n k : Measure ℝ) = componentAt (μ : Measure ℝ) n k := by
  rw [componentAt, cell_eq_dyadicCell]
  rfl

/-! ### Integrals and sums over cells -/

/-- The cell index of a point of `[a, b]` lies between those of `a` and `b`. -/
theorem cellIdx_mem_Icc {n : ℕ} {a b y : ℝ} (hy : y ∈ Icc a b) :
    cellIdx n y ∈ Finset.Icc (cellIdx n a) (cellIdx n b) := by
  have h : (0 : ℝ) ≤ 2 ^ n := by positivity
  exact Finset.mem_Icc.2 ⟨Int.floor_mono (mul_le_mul_of_nonneg_left hy.1 h),
    Int.floor_mono (mul_le_mul_of_nonneg_left hy.2 h)⟩

/-- A cell whose index lies outside the range of indices of `[a, b]` misses `[a, b]`. -/
theorem measure_cell_eq_zero_of_not_mem (θ : Measure ℝ) {a b : ℝ} (hab : θ (Icc a b)ᶜ = 0)
    {n : ℕ} {k : ℤ} (hk : k ∉ Finset.Icc (cellIdx n a) (cellIdx n b)) : θ (cell n k) = 0 := by
  refine measure_mono_null (s := cell n k) (t := (Icc a b)ᶜ) ?_ hab
  intro y hy hyab
  rw [mem_cell_iff] at hy
  exact hk (hy ▸ cellIdx_mem_Icc hyab)

/-- The integral of a function of the level-`n` cell index against a finite measure carried by
`[a, b]` is the finite sum `∑_k θ(D_k) G(k)` over the cells meeting `[a, b]`. -/
theorem integral_comp_cellIdx (θ : Measure ℝ) [IsFiniteMeasure θ] {a b : ℝ}
    (hab : θ (Icc a b)ᶜ = 0) (n : ℕ) (G : ℤ → ℝ) :
    ∫ y, G (cellIdx n y) ∂θ =
      ∑ k ∈ Finset.Icc (cellIdx n a) (cellIdx n b), θ.real (cell n k) * G k := by
  set F := Finset.Icc (cellIdx n a) (cellIdx n b)
  have hmap : ∫ y, G (cellIdx n y) ∂θ = ∫ k, G k ∂(θ.map (cellIdx n)) :=
    (integral_map (measurable_cellIdx n).aemeasurable
      measurable_from_top.aestronglyMeasurable).symm
  have hae : ∀ᵐ k ∂(θ.map (cellIdx n)), k ∈ (F : Set ℤ) := by
    rw [ae_map_iff (measurable_cellIdx n).aemeasurable MeasurableSet.of_discrete, ae_iff]
    refine measure_mono_null (t := (Icc a b)ᶜ) ?_ hab
    intro y hy hyab
    exact hy (cellIdx_mem_Icc hyab)
  rw [hmap, ← Measure.restrict_eq_self_of_ae_mem hae, setIntegral_finset F IntegrableOn.finset]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_measureReal_apply (measurable_cellIdx n) (measurableSet_singleton k),
    preimage_cellIdx_singleton, smul_eq_mul]

/-- A sum over the support of the discrete law `dyadicLaw μ n`, weighted by the law, is the sum over
the cells meeting `[a, b]` weighted by their masses. -/
theorem sum_support_eq_sum_Icc (μ : ProbabilityMeasure ℝ) {a b : ℝ}
    (hab : (μ : Measure ℝ) (Icc a b)ᶜ = 0) (n : ℕ) [Fintype (dyadicLaw μ n).support]
    (f : ℤ → ℝ) :
    ∑ k : (dyadicLaw μ n).support, (dyadicLaw μ n k).toReal * f k =
      ∑ k ∈ Finset.Icc (cellIdx n a) (cellIdx n b), (μ : Measure ℝ).real (cell n k) * f k := by
  rw [← Finset.sum_subtype (dyadicLaw μ n).support.toFinset (p := (· ∈ (dyadicLaw μ n).support))
    (by simp) (fun k => (dyadicLaw μ n k).toReal * f k)]
  simp_rw [dyadicLaw_toReal]
  apply Finset.sum_subset
  · intro k hk
    rw [Set.mem_toFinset] at hk
    by_contra hk'
    have h0 : dyadicLaw μ n k = 0 := by
      rw [dyadicLaw_apply, ← cell_eq_dyadicCell]
      exact measure_cell_eq_zero_of_not_mem _ hab hk'
    exact (PMF.apply_eq_zero_iff _ _).1 h0 hk
  · intro k _ hk
    rw [Set.mem_toFinset] at hk
    rw [measureReal_cell_eq_zero_of_not_mem_support μ hk, zero_mul]

end FractalGeometry.Hochman
