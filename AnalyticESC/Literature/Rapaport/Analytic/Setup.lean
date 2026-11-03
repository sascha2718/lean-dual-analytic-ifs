module

public import AnalyticESC.Literature.Rapaport.Analytic.Multiscale
public import AnalyticESC.Literature.Rapaport.Analytic.Statements

@[expose] public section

/-!
# Setting of Section 3: bi-Lipschitz maps of `I` and the structure of `μ`

Vocabulary for the proof of Theorem 3.1 of A. Rapaport, *Dimension of self-conformal measures
associated to an exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2.

The maps `ψ ∈ C¹(I, I)` with `ε ≤ |ψ'| ≤ ε⁻¹` of Section 3 enter the proofs only through the
bounds `ε |x - y| ≤ |ψ x - ψ y| ≤ ε⁻¹ |x - y|` on `I` (`BiLipOn`). The self-conformal measure
`μ` enters only through the properties collected in `SCStructure`: it is a probability measure on
`I` without atoms, and for every `n` it is a finite convex combination of images `g_u μ` under
maps `g_u : I → I` with `C⁻¹ 2^{-n} |x - y| ≤ |g_u x - g_u y| ≤ C 2^{-n} |x - y|` (relation
(2.7) with the cut-sets `Ψ_n` and the bounds (2.8)).

## Main declarations

* `BiLipOn f a b`: `a |x - y| ≤ |f x - f y| ≤ b |x - y|` for `x, y ∈ I`.
* `biLipOn_of_hasDerivWithinAt`: derivative bounds give `BiLipOn` (mean value theorem).
* `SCStructure μ`: the properties of a self-conformal measure used in Section 3.
* `pairAvg ν θ i G`: the average of `G(ν_{p,i}, θ_{x,i})` over the level-`i` components.
* `clampToI f`: `f ∘ proj_I`, a continuous map agreeing with `f` on `I` when `f` is continuous on
  `I`; `map_clampToI` shows that it has the same image measures.
* `levelProb_mono`, `measureReal_le_cavg`, `cavg_affine3`, `cavg_ind_le_one`,
  `cavg_measureReal_le_one`: elementary facts on averages.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Setup`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic

open MeasureTheory ProbabilityTheory Set Filter Topology FractalGeometry.SelfConformal
open scoped ENNReal

/-! ### Bi-Lipschitz maps of `I` -/

/-- `a |x - y| ≤ |f x - f y| ≤ b |x - y|` for all `x, y ∈ I`. -/
def BiLipOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x ∈ AnalyticESC.I, ∀ y ∈ AnalyticESC.I, a * |x - y| ≤ |f x - f y| ∧ |f x - f y| ≤ b * |x - y|

/-- Compositions of bi-Lipschitz maps of `I` are bi-Lipschitz. -/
theorem BiLipOn.comp {f g : ℝ → ℝ} {a b a' b' : ℝ} (hf : BiLipOn f a b) (hg : BiLipOn g a' b')
    (hgI : MapsTo g AnalyticESC.I AnalyticESC.I) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    BiLipOn (f ∘ g) (a * a') (b * b') := by
  intro x hx y hy
  obtain ⟨h1, h2⟩ := hf (g x) (hgI hx) (g y) (hgI hy)
  obtain ⟨h3, h4⟩ := hg x hx y hy
  simp only [Function.comp_apply]
  constructor
  · calc a * a' * |x - y| = a * (a' * |x - y|) := by ring
      _ ≤ a * |g x - g y| := mul_le_mul_of_nonneg_left h3 ha
      _ ≤ |f (g x) - f (g y)| := h1
  · calc |f (g x) - f (g y)| ≤ b * |g x - g y| := h2
      _ ≤ b * (b' * |x - y|) := mul_le_mul_of_nonneg_left h4 hb
      _ = b * b' * |x - y| := by ring

/-- Bi-Lipschitz maps of `I` are continuous on `I`. -/
theorem BiLipOn.continuousOn {f : ℝ → ℝ} {a b : ℝ} (hf : BiLipOn f a b) :
    ContinuousOn f AnalyticESC.I := by
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨ε / (|b| + 1), by positivity, fun {y} hy hxy => ?_⟩
  rw [Real.dist_eq] at hxy ⊢
  have h := (hf y hy x hx).2
  calc |f y - f x| ≤ b * |y - x| := h
    _ ≤ |b| * |y - x| := mul_le_mul_of_nonneg_right (le_abs_self b) (abs_nonneg _)
    _ ≤ (|b| + 1) * |y - x| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ < (|b| + 1) * (ε / (|b| + 1)) := mul_lt_mul_of_pos_left hxy (by positivity)
    _ = ε := by field_simp

/-- The mean value theorem: a map with a derivative within `I` at each point of `I` and
`a ≤ |f'| ≤ b` on `I` satisfies `a |x - y| ≤ |f x - f y| ≤ b |x - y|` on `I`. -/
theorem biLipOn_of_hasDerivWithinAt {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ AnalyticESC.I, HasDerivWithinAt f (f' x) AnalyticESC.I x)
    (hb : ∀ x ∈ AnalyticESC.I, a ≤ |f' x| ∧ |f' x| ≤ b) : BiLipOn f a b := by
  have hcont : ContinuousOn f AnalyticESC.I := fun x hx => (hf x hx).continuousWithinAt
  have key : ∀ x ∈ AnalyticESC.I, ∀ y ∈ AnalyticESC.I, x < y →
      a * |x - y| ≤ |f x - f y| ∧ |f x - f y| ≤ b * |x - y| := by
    intro x hx y hy hxy
    have hsub : Icc x y ⊆ AnalyticESC.I := Icc_subset_Icc hx.1 hy.2
    obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope f f' hxy (hcont.mono hsub) fun c hc => by
      have hcI : c ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt hx.1 hc.1, lt_of_lt_of_le hc.2 hy.2⟩
      exact (hf c (Ioo_subset_Icc_self hcI)).hasDerivAt (Icc_mem_nhds hcI.1 hcI.2)
    have hcI : c ∈ AnalyticESC.I := hsub (Ioo_subset_Icc_self hc)
    have hyx : 0 < y - x := sub_pos.2 hxy
    have he : |f x - f y| = |f' c| * |x - y| := by
      have hne : |x - y| ≠ 0 := abs_ne_zero.2 (by linarith)
      rw [hc', abs_div, abs_sub_comm (f y) (f x), abs_sub_comm y x, div_mul_cancel₀ _ hne]
    rw [he]
    exact ⟨mul_le_mul_of_nonneg_right (hb c hcI).1 (abs_nonneg _),
      mul_le_mul_of_nonneg_right (hb c hcI).2 (abs_nonneg _)⟩
  intro x hx y hy
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · exact key x hx y hy hxy
  · simp
  · rw [abs_sub_comm x, abs_sub_comm (f x)]
    exact key y hy x hx hxy

/-! ### Clamping to `I` -/

/-- `f ∘ proj_I`: equal to `f` on `I`, and constant on each side of `I`. -/
noncomputable def clampToI (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => f (Set.projIcc (0 : ℝ) 1 zero_le_one x)

/-- `clampToI f` agrees with `f` on `I`. -/
theorem clampToI_eq {f : ℝ → ℝ} {x : ℝ} (hx : x ∈ AnalyticESC.I) : clampToI f x = f x := by
  simp [clampToI, Set.projIcc_of_mem zero_le_one hx]

/-- `clampToI f` is continuous when `f` is continuous on `I`. -/
theorem continuous_clampToI {f : ℝ → ℝ} (hf : ContinuousOn f AnalyticESC.I) :
    Continuous (clampToI f) := by
  have h1 : Continuous fun x : ℝ => (Set.projIcc (0 : ℝ) 1 zero_le_one x : ℝ) :=
    continuous_subtype_val.comp continuous_projIcc
  exact hf.comp_continuous h1 fun x => (Set.projIcc (0 : ℝ) 1 zero_le_one x).2

/-- `clampToI f` is bi-Lipschitz on `I` with the constants of `f`. -/
theorem BiLipOn.clampToI {f : ℝ → ℝ} {a b : ℝ} (hf : BiLipOn f a b) : BiLipOn (clampToI f) a b := by
  intro x hx y hy
  rw [clampToI_eq hx, clampToI_eq hy]
  exact hf x hx y hy

/-- `clampToI f` maps `I` into `I` when `f` does. -/
theorem mapsTo_clampToI {f : ℝ → ℝ} (hf : MapsTo f AnalyticESC.I AnalyticESC.I) :
    MapsTo (clampToI f) AnalyticESC.I AnalyticESC.I := fun x hx => by
  rw [clampToI_eq hx]
  exact hf hx

/-- `clampToI f` takes values in `I` when `f` maps `I` into `I`. -/
theorem clampToI_mem {f : ℝ → ℝ} (hf : MapsTo f AnalyticESC.I AnalyticESC.I) (x : ℝ) :
    clampToI f x ∈ AnalyticESC.I :=
  hf (Set.projIcc (0 : ℝ) 1 zero_le_one x).2

/-- A measure carried by `I` has the same images under `f` and `clampToI f`. -/
theorem map_clampToI {μ : Measure ℝ} (hμ : μ AnalyticESC.Iᶜ = 0) (f : ℝ → ℝ) :
    μ.map (clampToI f) = μ.map f := by
  refine Measure.map_congr ?_
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun x hx => ?_) hμ
  intro hxI
  exact hx (clampToI_eq hxI)

/-! ### The structure of the self-conformal measure -/

/-- The properties of a self-conformal measure `μ` on `I` used in Section 3: `μ` is a probability
measure on `I` without atoms, and there is `C ≥ 1` such that for every `n` the measure `μ` is a
finite convex combination `∑_u w_u g_u μ` of images of `μ` under continuous maps `g_u` with
`g_u(I) ⊆ I` and `C⁻¹ 2^{-n} |x - y| ≤ |g_u x - g_u y| ≤ C 2^{-n} |x - y|` on `I`. -/
structure SCStructure (μ : Measure ℝ) : Prop where
  isProb : IsProbabilityMeasure μ
  compl_I : μ AnalyticESC.Iᶜ = 0
  noAtoms : ∀ x, μ {x} = 0
  decomp : ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, ∃ K : ℕ, ∃ w : Fin K → ℝ, ∃ g : Fin K → ℝ → ℝ,
    (∀ u, 0 ≤ w u) ∧ ∑ u, w u = 1 ∧ μ = ∑ u, ENNReal.ofReal (w u) • μ.map (g u) ∧
    ∀ u, Continuous (g u) ∧ MapsTo (g u) AnalyticESC.I AnalyticESC.I ∧
      BiLipOn (g u) (C⁻¹ / 2 ^ n) (C / 2 ^ n)

/-! ### Averages over components -/

/-- The average `𝔼(G(ν_{p,i}, θ_{x,i}))` over the level-`i` components of `ν` and `θ`, for
`(p, x)` distributed according to `ν × θ`. -/
noncomputable def pairAvg {k : ℕ} (ν : Measure (Poly k)) (θ : Measure ℝ) (i : ℕ)
    (G : Measure (Poly k) → Measure ℝ → ℝ) : ℝ :=
  cavg ν (cellIdxVec i) fun ρ => cavg θ (cellIdx i) fun τ => G ρ τ

/-- `levelProb` is monotone in the property. -/
theorem levelProb_mono (θ : Measure ℝ) [IsFiniteMeasure θ] (i n : ℕ) {P Q : ℕ → ℝ → Prop}
    (h : ∀ j x, P j x → Q j x) : levelProb θ i n P ≤ levelProb θ i n Q := by
  unfold levelProb
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun j _ => ?_) (by positivity)
  exact measureReal_mono (fun x hx => h j x hx)

/-- The mass of an arbitrary set is at most the average of its masses under the components:
`θ(G) ≤ ∑_b θ(f⁻¹{b}) θ_{f = b}(G)`. -/
theorem measureReal_le_cavg {X : Type*} [MeasurableSpace X] {θ : Measure X}
    [IsFiniteMeasure θ] {L : Type*} [MeasurableSpace L] [MeasurableSingletonClass L]
    [Countable L] {f : X → L} (hf : Measurable f) (hfin : FiniteLabels θ f) (G : Set X) :
    θ.real G ≤ cavg θ f fun τ => τ.real G := by
  classical
  rw [cavg_eq_sum hfin]
  have h1 : θ G ≤ ∑ b ∈ hfin.toFinset, θ (f ⁻¹' {b} ∩ G) := by
    have hnull := hfin.ae_mem
    calc θ G ≤ θ (⋃ b ∈ hfin.toFinset, f ⁻¹' {b} ∩ G) + θ {x | f x ∉ hfin.toFinset} := by
          refine (measure_mono fun x hx => ?_).trans (measure_union_le _ _)
          by_cases hxs : f x ∈ hfin.toFinset
          · exact Or.inl (Set.mem_biUnion hxs ⟨rfl, hx⟩)
          · exact Or.inr hxs
      _ = θ (⋃ b ∈ hfin.toFinset, f ⁻¹' {b} ∩ G) := by
          rw [ae_iff] at hnull
          simp [hnull]
      _ ≤ ∑ b ∈ hfin.toFinset, θ (f ⁻¹' {b} ∩ G) := measure_biUnion_finset_le _ _
  have h2 : θ.real G ≤ ∑ b ∈ hfin.toFinset, θ.real (f ⁻¹' {b} ∩ G) := by
    simp only [measureReal_def]
    rw [← ENNReal.toReal_sum fun _ _ => measure_ne_top _ _]
    exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun _ _ => measure_ne_top _ _) h1
  refine h2.trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_))
  rw [comp_real_apply hf]
  by_cases hb : θ.real (f ⁻¹' {b}) = 0
  · have : θ.real (f ⁻¹' {b} ∩ G) = 0 :=
      le_antisymm (hb ▸ measureReal_mono Set.inter_subset_left) measureReal_nonneg
    rw [this, hb]
    simp
  · field_simp

/-! ### Linear combinations of component averages -/

section Cavg

variable {X : Type*} [MeasurableSpace X] {θ : Measure X} [IsProbabilityMeasure θ]
variable {L : Type*} [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L]

/-- Component averages of affine combinations of three functions. -/
theorem cavg_affine3 {f : X → L} (hf : Measurable f) (hfin : FiniteLabels θ f)
    (F₁ F₂ F₃ : Measure X → ℝ) (α β γ c : ℝ) :
    cavg θ f (fun τ => α * F₁ τ + β * F₂ τ + γ * F₃ τ + c) =
      α * cavg θ f F₁ + β * cavg θ f F₂ + γ * cavg θ f F₃ + c := by
  rw [cavg_eq_sum hfin, cavg_eq_sum hfin, cavg_eq_sum hfin, cavg_eq_sum hfin]
  have h1 := sum_measureReal_fiber hf hfin.toFinset (fun _ hb => hfin.mem_toFinset.2 hb)
    (θ := θ)
  calc ∑ b ∈ hfin.toFinset, θ.real (f ⁻¹' {b}) *
        (α * F₁ (comp θ f b) + β * F₂ (comp θ f b) + γ * F₃ (comp θ f b) + c)
      = α * ∑ b ∈ hfin.toFinset, θ.real (f ⁻¹' {b}) * F₁ (comp θ f b) +
        β * ∑ b ∈ hfin.toFinset, θ.real (f ⁻¹' {b}) * F₂ (comp θ f b) +
        γ * ∑ b ∈ hfin.toFinset, θ.real (f ⁻¹' {b}) * F₃ (comp θ f b) +
        c * ∑ b ∈ hfin.toFinset, θ.real (f ⁻¹' {b}) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ = _ := by rw [h1, mul_one]

/-- Component averages of indicators are at most `1`. -/
theorem cavg_ind_le_one {f : X → L} (hf : Measurable f) (hfin : FiniteLabels θ f)
    (P : Measure X → Prop) [DecidablePred P] :
    cavg θ f (fun τ => if P τ then 1 else 0) ≤ 1 :=
  cavg_le_of_le hf hfin fun b _ => by split_ifs <;> norm_num

/-- Component averages of the masses of a set are at most `1`. -/
theorem cavg_measureReal_le_one {f : X → L} (hf : Measurable f) (hfin : FiniteLabels θ f)
    (S : Set X) : cavg θ f (fun τ => τ.real S) ≤ 1 :=
  cavg_le_of_le hf hfin fun b hb => by
    have := comp_isProbabilityMeasure hb
    exact measureReal_le_one

end Cavg

end FractalGeometry.Rapaport.Analytic
