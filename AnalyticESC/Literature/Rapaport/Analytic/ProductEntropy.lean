module

public import AnalyticESC.Literature.Rapaport.Analytic.Entropy

@[expose] public section

/-!
# Entropy and components of product measures

For product measures `ν × θ` and product labellings `(f, g)`: the components are products of
components, the entropy is additive, and component averages split into iterated averages. These
are basic properties of entropy (M. Hochman, *On self-similar sets with overlaps and inverse
theorems for entropy*, Ann. of Math. 180 (2014), Section 3.1) used in Section 3 of A. Rapaport,
*Dimension of self-conformal measures associated to an exponentially separated analytic IFS on
ℝ*, arXiv:2412.16753v2.

## Main declarations

* `preimage_prodLabel`, `FiniteLabels.prodLabel`: fibres and finiteness for `(f ∘ fst, g ∘ snd)`.
* `comp_prod`: `(ν × θ)_{(b, c)} = ν_b × θ_c`.
* `ent_prod`: `H(ν × θ, f × g) = H(ν, f) + H(θ, g)`.
* `ent_comp_fst`, `ent_comp_snd`: entropies of labellings of one coordinate.
* `cavg_prod`: the component average of `ν × θ` as an iterated average.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.ProductEntropy`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {L L' : Type*}

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- The fibres of a product labelling are products of fibres. -/
theorem preimage_prodLabel (f : X → L) (g : Y → L') (b : L) (c : L') :
    (fun z : X × Y => (f z.1, g z.2)) ⁻¹' {(b, c)} = (f ⁻¹' {b}) ×ˢ (g ⁻¹' {c}) := by
  ext z
  simp [Prod.ext_iff]

variable {ν : Measure X} {θ : Measure Y}

/-- Almost sure properties of the coordinates hold almost surely for the product measure. -/
theorem ae_prod_of_ae [SFinite ν] [SFinite θ] {P : X → Prop} {Q : Y → Prop}
    (hP : ∀ᵐ x ∂ν, P x) (hQ : ∀ᵐ y ∂θ, Q y) : ∀ᵐ z ∂(ν.prod θ), P z.1 ∧ Q z.2 := by
  have h1 : ∀ᵐ z ∂(ν.prod θ), P z.1 := Measure.quasiMeasurePreserving_fst.ae hP
  have h2 : ∀ᵐ z ∂(ν.prod θ), Q z.2 := Measure.quasiMeasurePreserving_snd.ae hQ
  filter_upwards [h1, h2] with z hz1 hz2
  exact ⟨hz1, hz2⟩

/-- Product labellings of labellings with finite labels have finite labels. -/
theorem FiniteLabels.prodLabel [SFinite θ] {f : X → L} {g : Y → L'} (hf : FiniteLabels ν f)
    (hg : FiniteLabels θ g) :
    FiniteLabels (ν.prod θ) (fun z : X × Y => (f z.1, g z.2)) := by
  refine (hf.prod hg).subset fun bc hbc => ?_
  simp only [Function.mem_support, ne_eq] at hbc ⊢
  rw [preimage_prodLabel, Measure.prod_prod] at hbc
  exact ⟨fun h => hbc (by simp only at h; rw [h, zero_mul]),
    fun h => hbc (by simp only at h; rw [h, mul_zero])⟩

variable [MeasurableSpace L] [MeasurableSingletonClass L] [MeasurableSpace L']
  [MeasurableSingletonClass L']

/-- The components of a product measure for a product labelling are products of components. -/
theorem comp_prod [IsFiniteMeasure ν] [IsFiniteMeasure θ] {f : X → L} {g : Y → L'}
    (hf : Measurable f) (hg : Measurable g) (b : L) (c : L') :
    comp (ν.prod θ) (fun z : X × Y => (f z.1, g z.2)) (b, c) =
      (comp ν f b).prod (comp θ g c) := by
  have hA := hf (measurableSet_singleton b)
  have hB := hg (measurableSet_singleton c)
  rw [comp, comp, comp, preimage_prodLabel, ProbabilityTheory.cond, ProbabilityTheory.cond,
    ProbabilityTheory.cond, Measure.prod_prod,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.prod_restrict]
  congr 1
  rw [ENNReal.mul_inv (Or.inr (measure_ne_top _ _)) (Or.inl (measure_ne_top _ _)), mul_comm]

variable [Countable L] [Countable L']

/-- Additivity of entropy for product measures and product labellings. -/
theorem ent_prod [IsProbabilityMeasure ν] [IsProbabilityMeasure θ] {f : X → L} {g : Y → L'}
    (hf : Measurable f) (hg : Measurable g) (hfin : FiniteLabels ν f)
    (hgin : FiniteLabels θ g) :
    ent (ν.prod θ) (fun z : X × Y => (f z.1, g z.2)) = ent ν f + ent θ g := by
  classical
  rw [ent_eq_sum_of_subset (hfin.toFinset ×ˢ hgin.toFinset) fun bc hbc => by
      rw [Finset.mem_product, hfin.mem_toFinset, hgin.mem_toFinset]
      rw [preimage_prodLabel, Measure.prod_prod] at hbc
      exact ⟨fun h => hbc (by rw [h, zero_mul]), fun h => hbc (by rw [h, mul_zero])⟩,
    ent_eq_sum hfin, ent_eq_sum hgin, Finset.sum_product]
  have h1 := sum_measureReal_fiber hf hfin.toFinset (fun _ hb => hfin.mem_toFinset.2 hb)
    (θ := ν)
  have h2 := sum_measureReal_fiber hg hgin.toFinset (fun _ hb => hgin.mem_toFinset.2 hb)
    (θ := θ)
  have he : ∀ b c, (ν.prod θ).real ((fun z : X × Y => (f z.1, g z.2)) ⁻¹' {(b, c)}) =
      ν.real (f ⁻¹' {b}) * θ.real (g ⁻¹' {c}) := fun b c => by
    rw [preimage_prodLabel, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]
    rfl
  simp only [he, Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    h1, h2, one_mul]

omit [Countable L] [MeasurableSpace L'] [MeasurableSingletonClass L'] [Countable L'] in
/-- The entropy of a labelling of the first coordinate. -/
theorem ent_comp_fst [IsProbabilityMeasure ν] [IsProbabilityMeasure θ] {f : X → L}
    (hf : Measurable f) : ent (ν.prod θ) (fun z : X × Y => f z.1) = ent ν f := by
  have h := ent_map (θ := ν.prod θ) measurable_fst hf
  rw [Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h.symm

omit [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L] [Countable L'] in
/-- The entropy of a labelling of the second coordinate. -/
theorem ent_comp_snd [IsProbabilityMeasure ν] [IsProbabilityMeasure θ] {g : Y → L'}
    (hg : Measurable g) : ent (ν.prod θ) (fun z : X × Y => g z.2) = ent θ g := by
  have h := ent_map (θ := ν.prod θ) measurable_snd hg
  rw [Measure.map_snd_prod, measure_univ, one_smul] at h
  exact h.symm

omit [Countable L] [Countable L'] in
/-- The component average of a product measure for a product labelling is the iterated
component average. -/
theorem cavg_prod [IsProbabilityMeasure ν] [IsProbabilityMeasure θ] {f : X → L} {g : Y → L'}
    (hf : Measurable f) (hg : Measurable g) (hfin : FiniteLabels ν f)
    (hgin : FiniteLabels θ g) (F : Measure (X × Y) → ℝ) :
    cavg (ν.prod θ) (fun z : X × Y => (f z.1, g z.2)) F =
      cavg ν f (fun ρ => cavg θ g (fun τ => F (ρ.prod τ))) := by
  classical
  rw [cavg_eq_sum_of_subset (hfin.toFinset ×ˢ hgin.toFinset) fun bc hbc => by
      rw [Finset.mem_product, hfin.mem_toFinset, hgin.mem_toFinset]
      rw [preimage_prodLabel, Measure.prod_prod] at hbc
      exact ⟨fun h => hbc (by rw [h, zero_mul]), fun h => hbc (by rw [h, mul_zero])⟩,
    cavg_eq_sum hfin, Finset.sum_product]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [cavg_eq_sum hgin, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [comp_prod hf hg, preimage_prodLabel, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]
  simp only [measureReal_def]
  ring

end FractalGeometry.Rapaport.Analytic
