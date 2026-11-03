module

public import AnalyticESC.Literature.Hochman.ScaleTransfer

@[expose] public section

/-!
# Dyadic rescaling of measures on the line

The affine map `x ↦ (2^i x - K) / 2^c` (`K ∈ ℤ`) maps the level-`(i + p)` dyadic cells bijectively
onto the level-`(c + p)` dyadic cells, so it shifts dyadic entropies and components exactly. It
commutes with convolution up to adding the translation parameters, and with `K = ⌊2^i a⌋` and
`2^c ≥ 1 + L` it maps an interval `[a, a + L 2^{-i}]` into `[0, 1]`. This is the change of scale
by which Bárány–Hochman–Rapaport (Invent. Math. 216 (2019), Section 4.1) derive the
scale-shifted form of Hochman's Theorem 2.8 used by Rapaport (arXiv:2412.16753v2, Theorem 3.2).

## Main declarations

* `resc`, `measurable_resc`, `cellIdx_resc`, `preimage_resc_cell`: the map and its action on
  cells.
* `dyadicEntropy_map_resc`: `H(θ ∘ resc⁻¹, 𝒟_{c+p}) = H(θ, 𝒟_{i+p})`.
* `component_map_resc`: components of the image are images of components.
* `measureReal_map_resc_setOf_component`: the mass of components with a given entropy.
* `map_resc_conv`: compatibility with convolution.
* `map_resc_compl_Icc`: the image of a measure carried by `[a, a + L 2^{-i}]` is carried by
  `[0, 1]`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Hochman.Rescaling`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Hochman

open MeasureTheory Set FractalGeometry.SelfConformal
open scoped ENNReal MeasureTheory

/-- The affine map `x ↦ (2^i x - K) / 2^c`. -/
noncomputable def resc (i c : ℕ) (K : ℤ) (x : ℝ) : ℝ := (2 ^ i * x - K) / 2 ^ c

/-- `resc` is measurable. -/
theorem measurable_resc (i c : ℕ) (K : ℤ) : Measurable (resc i c K) := by
  unfold resc
  fun_prop

/-- `resc` sends the level-`(i + p)` cell of `x` to the level-`(c + p)` cell of its image:
`⌊2^{c+p} resc x⌋ = ⌊2^{i+p} x⌋ - 2^p K`. -/
theorem cellIdx_resc (i c p : ℕ) (K : ℤ) (x : ℝ) :
    cellIdx (c + p) (resc i c K x) = cellIdx (i + p) x - 2 ^ p * K := by
  unfold cellIdx resc
  have h : (2 : ℝ) ^ (c + p) * ((2 ^ i * x - K) / 2 ^ c) =
      2 ^ (i + p) * x - ((2 ^ p * K : ℤ) : ℝ) := by
    rw [pow_add, pow_add]
    push_cast
    field_simp
  rw [h, Int.floor_sub_intCast]

/-- The preimage of a level-`(c + p)` cell under `resc` is a level-`(i + p)` cell. -/
theorem preimage_resc_cell (i c p : ℕ) (K k : ℤ) :
    resc i c K ⁻¹' cell (c + p) k = cell (i + p) (k + 2 ^ p * K) := by
  ext x
  rw [mem_preimage, mem_cell_iff, mem_cell_iff, cellIdx_resc]
  omega

/-- The preimage of the level-`(c + p)` cell of `resc x` is the level-`(i + p)` cell of `x`. -/
theorem preimage_resc_cellOf (i c p : ℕ) (K : ℤ) (x : ℝ) :
    resc i c K ⁻¹' cellOf (c + p) (resc i c K x) = cellOf (i + p) x := by
  rw [cellOf, preimage_resc_cell, cellIdx_resc, sub_add_cancel]
  rfl

/-- Rescaling shifts the dyadic entropy exactly: `H(θ ∘ resc⁻¹, 𝒟_{c+p}) = H(θ, 𝒟_{i+p})`. -/
theorem dyadicEntropy_map_resc (θ : Measure ℝ) (i c p : ℕ) (K : ℤ) :
    dyadicEntropy (θ.map (resc i c K)) (c + p) = dyadicEntropy θ (i + p) := by
  unfold dyadicEntropy
  congr 1
  have hterm : ∀ k : ℤ, (θ.map (resc i c K)).real (cell (c + p) k) =
      θ.real (cell (i + p) (k + 2 ^ p * K)) := by
    intro k
    rw [map_measureReal_apply (measurable_resc i c K) (measurableSet_cell _ _), preimage_resc_cell]
  simp_rw [hterm]
  exact (Equiv.addRight (2 ^ p * K)).tsum_eq (fun k => Real.negMulLog (θ.real (cell (i + p) k)))

/-- Components of the rescaled measure are rescaled components:
`(θ ∘ resc⁻¹)_{resc x, c+p} = θ_{x, i+p} ∘ resc⁻¹`. -/
theorem component_map_resc (θ : Measure ℝ) (i c p : ℕ) (K : ℤ) (x : ℝ) :
    component (θ.map (resc i c K)) (c + p) (resc i c K x) =
      (component θ (i + p) x).map (resc i c K) := by
  have hf := measurable_resc i c K
  change ((θ.map (resc i c K)) (cellOf (c + p) (resc i c K x)))⁻¹ •
      (θ.map (resc i c K)).restrict (cellOf (c + p) (resc i c K x)) =
    ((θ (cellOf (i + p) x))⁻¹ • θ.restrict (cellOf (i + p) x)).map (resc i c K)
  have hC : MeasurableSet (cellOf (c + p) (resc i c K x)) := measurableSet_cell _ _
  rw [Measure.map_apply hf hC, Measure.restrict_map hf hC, preimage_resc_cellOf,
    Measure.map_smul _ hf.aemeasurable]

/-- The mass of the set of points whose rescaled component has a given entropy property. -/
theorem measureReal_map_resc_setOf_component (θ : Measure ℝ) (i c p M : ℕ) (K : ℤ)
    (P : ℝ → Prop) :
    (θ.map (resc i c K)).real
        {y | P (dyadicEntropy (component (θ.map (resc i c K)) (c + p) y) (c + p + M))} =
      θ.real {x | P (dyadicEntropy (component θ (i + p) x) (i + p + M))} := by
  rw [map_measureReal_apply (measurable_resc i c K)
    (measurableSet_setOf_component _ (c + p) fun ρ => P (dyadicEntropy ρ (c + p + M)))]
  congr 1
  ext x
  change P (dyadicEntropy (component (θ.map (resc i c K)) (c + p) (resc i c K x)) (c + p + M)) ↔
    P (dyadicEntropy (component θ (i + p) x) (i + p + M))
  rw [component_map_resc, add_assoc c, add_assoc i, dyadicEntropy_map_resc]

/-- Rescaling is compatible with convolution:
`(ξ ∘ resc_{K₁}⁻¹) ∗ (θ ∘ resc_{K₂}⁻¹) = (ξ ∗ θ) ∘ resc_{K₁+K₂}⁻¹`. -/
theorem map_resc_conv (ξ θ : Measure ℝ) [SFinite ξ] [SFinite θ] (i c : ℕ) (K₁ K₂ : ℤ) :
    (ξ.map (resc i c K₁)) ∗ (θ.map (resc i c K₂)) = (ξ ∗ θ).map (resc i c (K₁ + K₂)) := by
  have h₁ := measurable_resc i c K₁
  have h₂ := measurable_resc i c K₂
  have h₃ := measurable_resc i c (K₁ + K₂)
  have hadd : Measurable fun z : ℝ × ℝ => z.1 + z.2 := measurable_fst.add measurable_snd
  unfold Measure.conv
  rw [Measure.map_prod_map ξ θ h₁ h₂, Measure.map_map hadd (h₁.prodMap h₂),
    Measure.map_map h₃ hadd]
  congr 1
  funext z
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, resc]
  push_cast
  ring

/-- With `K = ⌊2^i a⌋` and `1 + L ≤ 2^c`, the rescaling maps `[a, a + L 2^{-i}]` into `[0, 1]`;
so the image of a measure carried by `[a, a + L 2^{-i}]` is carried by `[0, 1]`. -/
theorem map_resc_compl_Icc (ξ : Measure ℝ) {a L : ℝ} {i c : ℕ}
    (h : ξ (Icc a (a + L / 2 ^ i))ᶜ = 0) (hc : 1 + L ≤ 2 ^ c) :
    (ξ.map (resc i c ⌊2 ^ i * a⌋)) (Icc 0 1)ᶜ = 0 := by
  rw [Measure.map_apply (measurable_resc i c _) measurableSet_Icc.compl]
  refine measure_mono_null (t := (Icc a (a + L / 2 ^ i))ᶜ) ?_ h
  intro x hx hxa
  apply hx
  have h2i : (0 : ℝ) < 2 ^ i := by positivity
  have h2c : (0 : ℝ) < 2 ^ c := by positivity
  have hfl := Int.floor_le (2 ^ i * a)
  have hlt := Int.lt_floor_add_one (2 ^ i * a)
  have hx1 : 2 ^ i * a ≤ 2 ^ i * x := mul_le_mul_of_nonneg_left hxa.1 h2i.le
  have hx2 : 2 ^ i * x ≤ 2 ^ i * a + L := by
    have := mul_le_mul_of_nonneg_left hxa.2 h2i.le
    rwa [mul_add, mul_div_cancel₀ _ h2i.ne'] at this
  simp only [resc, mem_Icc]
  constructor
  · exact div_nonneg (by linarith) h2c.le
  · rw [div_le_one h2c]
    linarith

end FractalGeometry.Hochman
