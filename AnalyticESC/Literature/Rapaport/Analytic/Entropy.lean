module

public import AnalyticESC.Literature.ExactOverlaps.Entropy.ConditionalMixture
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.MixtureEntropyBounds
public import Mathlib.Probability.ConditionalProbability

@[expose] public section

/-!
# Shannon entropy of labellings

The basic calculus of entropy with respect to countable partitions used throughout Section 3 of
A. Rapaport, *Dimension of self-conformal measures associated to an exponentially separated
analytic IFS on ℝ*, arXiv:2412.16753v2 (Section 2.7 there, with the properties of entropy of
M. Hochman, *On self-similar sets with overlaps and inverse theorems for entropy*, Ann. of Math.
180 (2014), Section 3.1).

A labelling `f : X → L` into a countable type stands for the partition into its fibres. The
entropy `ent θ f` (natural logarithms) and the conditional entropy `cent θ f g` are `H(θ, 𝒟)` and
`H(θ, 𝒟 ∣ ℰ)`. The proofs bridge to the finite entropy `finiteEntropy` of the vendored
Kittle–Kogler library `ExactOverlaps`.

Adapted from the `BoxLike` formalisation of Rapaport arXiv:2309.03985, Section 3 (the module
`BoxLike.Rapaport.Entropy.Basic` and the entropy definitions of `BoxLike.Rapaport.Defs`).

## Main declarations

* `ent`, `cent`, `FiniteLabels`, `comp`, `cavg`: entropy, conditional entropy, finiteness of the
  labels of positive mass, components `θ_{f = b}` and component averages; the instance
  `isZeroOrProbabilityMeasure_comp`.
* Finite labels and sums: `ent_eq_sum_of_subset`, `ent_eq_sum`, `cavg_eq_sum`,
  `finiteLabels_of_ae_mem_finset`, `FiniteLabels.pair`, `FiniteLabels.comp`.
* Elementary properties: `ent_nonneg`, `ent_comp_injective`, `ent_congr_ae`, `ent_map`,
  `ent_pair_eq_add_cent`.
* Inequalities: `ent_le_of_factor`, `ent_pair_le`, `cent_nonneg`, `cent_le_ent`,
  `ent_le_log_card`, `ent_le_log_of_ae_mem`.
* Components: `comp_isProbabilityMeasure`, `comp_apply`, `eq_sum_comp`, `cent_eq_cavg`.
* Commensurability: `ent_le_ent_add_log_of_fiber_card`, `abs_ent_sub_ent_le_log_of_commensurable`.
* Finite mixtures: `sum_ent_le_ent` (concavity), `ent_le_sum_ent_add` (almost convexity),
  `sum_cent_le_cent`, `cent_le_sum_cent_add`, `ent_le_two_pieces`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Entropy`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic

open MeasureTheory ProbabilityTheory ExactOverlaps.Entropy
open scoped ENNReal

/-! ### Entropy of a labelling -/

section Defs

variable {X : Type*} [MeasurableSpace X] {θ' : Measure X}

/-- The Shannon entropy, in nats, of the law of the labels `f` under `θ`: `H(θ, 𝒟)` for the
partition `𝒟` into the fibres of `f`. -/
noncomputable def ent (θ : Measure X) {L : Type*} (f : X → L) : ℝ :=
  ∑' b : L, Real.negMulLog (θ.real (f ⁻¹' {b}))

/-- The conditional entropy `H(θ, 𝒟 ∣ ℰ) = H(θ, 𝒟 ∨ ℰ) - H(θ, ℰ)` of the labelling `f` given the
labelling `g`. -/
noncomputable def cent (θ : Measure X) {L L' : Type*} (f : X → L) (g : X → L') : ℝ :=
  ent θ (fun x => (f x, g x)) - ent θ g

/-- Only finitely many labels carry positive mass. -/
def FiniteLabels (θ : Measure X) {L : Type*} (f : X → L) : Prop :=
  (Function.support fun b : L => θ (f ⁻¹' {b})).Finite

/-- The component `θ_{f = b}`: the normalised restriction of `θ` to the fibre of the label `b`. -/
noncomputable def comp (θ : Measure X) {L : Type*} (f : X → L) (b : L) : Measure X :=
  θ[|f ⁻¹' {b}]

/-- The component average `𝔼_{x}(F(θ_{x}))`: the mean of `F` over the components of `θ` for the
labelling `f`, weighted by their masses. -/
noncomputable def cavg (θ : Measure X) {L : Type*} (f : X → L) (F : Measure X → ℝ) : ℝ :=
  ∑' b : L, θ.real (f ⁻¹' {b}) * F (comp θ f b)

/-- A component is a probability measure or the zero measure. -/
instance isZeroOrProbabilityMeasure_comp [IsFiniteMeasure θ'] {L : Type*} (f : X → L) (b : L) :
    IsZeroOrProbabilityMeasure (comp θ' f b) :=
  inferInstanceAs (IsZeroOrProbabilityMeasure (θ'[|f ⁻¹' {b}]))

end Defs

variable {X : Type*} [MeasurableSpace X] {θ : Measure X}
variable {L L' L'' M : Type*}

/-! ### Finite labels and finite sums -/

section FiniteSums

/-- Entropy as a finite sum over any finset containing every label of positive mass: the
series defining `H(θ, 𝒟)` has only these nonzero terms. -/
theorem ent_eq_sum_of_subset {f : X → L} (s : Finset L)
    (hs : ∀ b, θ (f ⁻¹' {b}) ≠ 0 → b ∈ s) :
    ent θ f = ∑ b ∈ s, Real.negMulLog (θ.real (f ⁻¹' {b})) := by
  unfold ent
  apply tsum_eq_sum
  intro b hb
  have h0 : θ (f ⁻¹' {b}) = 0 := by
    by_contra h
    exact hb (hs b h)
  simp [measureReal_def, h0]

/-- Membership in the finset of labels of positive mass. -/
theorem FiniteLabels.mem_toFinset {f : X → L} (hfin : FiniteLabels θ f) {b : L} :
    b ∈ hfin.toFinset ↔ θ (f ⁻¹' {b}) ≠ 0 :=
  (Set.Finite.mem_toFinset hfin).trans Function.mem_support

/-- Entropy as a finite sum over the labels of positive mass. -/
theorem ent_eq_sum {f : X → L} (hfin : FiniteLabels θ f) :
    ent θ f = ∑ b ∈ hfin.toFinset, Real.negMulLog (θ.real (f ⁻¹' {b})) :=
  ent_eq_sum_of_subset _ fun _ hb => hfin.mem_toFinset.2 hb

/-- The component average as a finite sum over any finset containing every label of positive
mass. -/
theorem cavg_eq_sum_of_subset {f : X → L} (s : Finset L) (hs : ∀ b, θ (f ⁻¹' {b}) ≠ 0 → b ∈ s)
    (F : Measure X → ℝ) :
    cavg θ f F = ∑ b ∈ s, θ.real (f ⁻¹' {b}) * F (comp θ f b) := by
  unfold cavg
  apply tsum_eq_sum
  intro b hb
  have h0 : θ (f ⁻¹' {b}) = 0 := by
    by_contra h
    exact hb (hs b h)
  simp [measureReal_def, h0]

/-- The component average as a finite sum over the labels of positive mass. -/
theorem cavg_eq_sum {f : X → L} (hfin : FiniteLabels θ f) (F : Measure X → ℝ) :
    cavg θ f F = ∑ b ∈ hfin.toFinset, θ.real (f ⁻¹' {b}) * F (comp θ f b) :=
  cavg_eq_sum_of_subset _ (fun _ hb => hfin.mem_toFinset.2 hb) F

/-- A labelling whose labels of positive mass lie in a finset has finite labels. -/
theorem finiteLabels_of_subset {f : X → L} (s : Finset L)
    (hs : ∀ b, θ (f ⁻¹' {b}) ≠ 0 → b ∈ s) : FiniteLabels θ f :=
  s.finite_toSet.subset fun b hb => hs b hb

/-- If almost every point has its label in `s`, then every label of positive mass lies in `s`. -/
theorem mem_of_ae_mem {f : X → L} {s : Finset L} (h : ∀ᵐ x ∂θ, f x ∈ s) (b : L)
    (hb : θ (f ⁻¹' {b}) ≠ 0) : b ∈ s := by
  by_contra hbs
  apply hb
  apply measure_mono_null _ (ae_iff.1 h)
  intro x hx
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
  simp [hx, hbs]

/-- A labelling which almost surely takes values in a finset has finite labels. -/
theorem finiteLabels_of_ae_mem_finset {f : X → L} (s : Finset L) (h : ∀ᵐ x ∂θ, f x ∈ s) :
    FiniteLabels θ f :=
  finiteLabels_of_subset s (mem_of_ae_mem h)

omit [MeasurableSpace X] in
/-- The fibre of a label of the join `𝒟 ∨ ℰ` is the intersection of the two fibres. -/
theorem preimage_pair_singleton (f : X → L) (g : X → L') (b : L) (c : L') :
    (fun x => (f x, g x)) ⁻¹' {(b, c)} = g ⁻¹' {c} ∩ f ⁻¹' {b} := by
  ext x
  simp [Prod.ext_iff, and_comm]

/-- The join of two labellings with finite labels has finite labels. -/
theorem FiniteLabels.pair {f : X → L} {g : X → L'} (hf : FiniteLabels θ f)
    (hg : FiniteLabels θ g) : FiniteLabels θ (fun x => (f x, g x)) := by
  refine (hf.prod hg).subset fun p hp => ⟨fun h => hp ?_, fun h => hp ?_⟩
  · exact measure_mono_null (by rw [preimage_pair_singleton]; exact Set.inter_subset_right) h
  · exact measure_mono_null (by rw [preimage_pair_singleton]; exact Set.inter_subset_left) h

/-- A recoding `φ ∘ f` of a labelling with finite labels has finite labels. -/
theorem FiniteLabels.comp [Countable L] {f : X → L} (hf : FiniteLabels θ f) (φ : L → L') :
    FiniteLabels θ (φ ∘ f) := by
  refine (hf.image φ).subset fun c hc => ?_
  by_contra hcon
  apply hc
  change θ ((φ ∘ f) ⁻¹' {c}) = 0
  have he : (φ ∘ f) ⁻¹' {c} = ⋃ b ∈ φ ⁻¹' {c}, f ⁻¹' {b} := by
    ext x
    simp
  rw [he, measure_biUnion_null_iff (Set.to_countable _)]
  intro b hb
  by_contra hb'
  exact hcon ⟨b, hb', hb⟩

/-- A labelling `g = φ ∘ f` coarser than a labelling `f` with finite labels has finite labels. -/
theorem FiniteLabels.of_factor [Countable L] {f : X → L} {g : X → L'} (hf : FiniteLabels θ f)
    (φ : L → L') (hg : g = φ ∘ f) : FiniteLabels θ g :=
  hg ▸ hf.comp φ

/-- The first labelling of a join with finite labels has finite labels. -/
theorem FiniteLabels.fst [Countable L] [Countable L'] {f : X → L} {g : X → L'}
    (h : FiniteLabels θ (fun x => (f x, g x))) : FiniteLabels θ f :=
  h.comp Prod.fst

/-- The second labelling of a join with finite labels has finite labels. -/
theorem FiniteLabels.snd [Countable L] [Countable L'] {f : X → L} {g : X → L'}
    (h : FiniteLabels θ (fun x => (f x, g x))) : FiniteLabels θ g :=
  h.comp Prod.snd

/-- Finite labels pass to absolutely continuous measures. -/
theorem FiniteLabels.of_absolutelyContinuous {θ' : Measure X} {f : X → L}
    (h : FiniteLabels θ f) (hθ : θ' ≪ θ) : FiniteLabels θ' f :=
  h.subset fun _ hb h0 => hb (hθ h0)

/-- Finite labels pass to the components `θ_{g = c}`. -/
theorem FiniteLabels.comp_measure {f : X → L} (h : FiniteLabels θ f) (g : X → L') (c : L') :
    FiniteLabels (FractalGeometry.Rapaport.Analytic.comp θ g c) f :=
  h.of_absolutelyContinuous cond_absolutelyContinuous

/-- The labels outside a finset containing every label of positive mass form a null set. -/
theorem measure_preimage_compl_eq_zero [Countable L] {f : X → L} (s : Finset L)
    (hs : ∀ b, θ (f ⁻¹' {b}) ≠ 0 → b ∈ s) : θ (f ⁻¹' (↑s : Set L)ᶜ) = 0 := by
  have he : f ⁻¹' (↑s : Set L)ᶜ = ⋃ b ∈ (↑s : Set L)ᶜ, f ⁻¹' {b} := by
    ext x
    simp
  rw [he, measure_biUnion_null_iff (Set.to_countable _)]
  intro b hb
  by_contra h
  exact hb (hs b h)

/-- Almost every point carries a label of positive mass. -/
theorem FiniteLabels.ae_mem [Countable L] {f : X → L} (hfin : FiniteLabels θ f) :
    ∀ᵐ x ∂θ, f x ∈ hfin.toFinset :=
  measure_preimage_compl_eq_zero _ fun _ hb => hfin.mem_toFinset.2 hb

end FiniteSums

/-! ### Measurable labellings: fibre sums and the bridge to `finiteEntropy` -/

section Measurable

variable [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L]
variable [MeasurableSpace L'] [MeasurableSingletonClass L'] [Countable L']
variable [MeasurableSpace L''] [MeasurableSingletonClass L''] [Countable L'']
variable [MeasurableSpace M] [MeasurableSingletonClass M] [Countable M]

/-- The fibres of a measurable labelling partition every measurable set, up to the null set of
labels outside a finset containing every label of positive mass. -/
theorem sum_measure_inter_fiber {f : X → L} (hf : Measurable f) (s : Finset L)
    (hs : ∀ b, θ (f ⁻¹' {b}) ≠ 0 → b ∈ s) {A : Set X} (hA : MeasurableSet A) :
    ∑ b ∈ s, θ (A ∩ f ⁻¹' {b}) = θ A := by
  rw [← measure_biUnion_finset]
  · have he : (⋃ b ∈ s, A ∩ f ⁻¹' {b}) = A ∩ f ⁻¹' (↑s : Set L) := by
      ext x
      simp
    rw [he, measure_inter_conull]
    rw [← Set.preimage_compl]
    exact measure_preimage_compl_eq_zero s hs
  · intro b _ c _ hbc
    exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right
      ((Set.disjoint_singleton.2 hbc).preimage f)
  · intro b _
    exact hA.inter (hf (measurableSet_singleton b))

/-- The real-valued form of `sum_measure_inter_fiber` for a finite measure. -/
theorem sum_measureReal_inter_fiber [IsFiniteMeasure θ] {f : X → L} (hf : Measurable f)
    (s : Finset L) (hs : ∀ b, θ (f ⁻¹' {b}) ≠ 0 → b ∈ s) {A : Set X} (hA : MeasurableSet A) :
    ∑ b ∈ s, θ.real (A ∩ f ⁻¹' {b}) = θ.real A := by
  simp only [measureReal_def]
  rw [← ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _), sum_measure_inter_fiber hf s hs hA]

/-- The masses of the labels of a measurable labelling sum to `1`. -/
theorem sum_measureReal_fiber [IsProbabilityMeasure θ] {f : X → L} (hf : Measurable f)
    (s : Finset L) (hs : ∀ b, θ (f ⁻¹' {b}) ≠ 0 → b ∈ s) :
    ∑ b ∈ s, θ.real (f ⁻¹' {b}) = 1 := by
  have h := sum_measureReal_inter_fiber hf s hs MeasurableSet.univ (θ := θ)
  simpa only [Set.univ_inter, probReal_univ] using h

variable [IsProbabilityMeasure θ]

/-- The law of the labels: the mass of the label `b` is that of its fibre. -/
theorem toPMF_map_apply {f : X → L} (hf : Measurable f) (b : L) :
    (θ.map f).toPMF b = θ (f ⁻¹' {b}) := by
  rw [Measure.toPMF_apply, Measure.map_apply hf (measurableSet_singleton b)]

/-- The real mass of a label under the law of the labels. -/
theorem toPMF_map_toReal {f : X → L} (hf : Measurable f) (b : L) :
    ((θ.map f).toPMF b).toReal = θ.real (f ⁻¹' {b}) := by
  rw [toPMF_map_apply hf, measureReal_def]

/-- `FiniteLabels` is the finiteness of the support of the law of the labels. -/
theorem finiteLabels_iff_toPMF {f : X → L} (hf : Measurable f) :
    FiniteLabels θ f ↔ ((θ.map f).toPMF).support.Finite := by
  have he : ((θ.map f).toPMF).support = Function.support fun b => θ (f ⁻¹' {b}) := by
    ext b
    rw [PMF.mem_support_iff, toPMF_map_apply hf, Function.mem_support]
  rw [he]
  rfl

/-- The bridge to the vendored finite entropy, for an arbitrary proof of finiteness. -/
theorem ent_eq_finiteEntropy' {f : X → L} (hf : Measurable f)
    (h : ((θ.map f).toPMF).support.Finite) : ent θ f = finiteEntropy ((θ.map f).toPMF) h := by
  unfold finiteEntropy
  rw [ent_eq_sum_of_subset h.toFinset]
  · exact Finset.sum_congr rfl fun b _ => by rw [toPMF_map_toReal hf]
  · intro b hb
    rw [Set.Finite.mem_toFinset, PMF.mem_support_iff, toPMF_map_apply hf]
    exact hb

/-- The entropy of a measurable labelling with finite labels is the vendored finite Shannon
entropy of the law of its labels: `H(θ, 𝒟)` is `finiteEntropy` of the
push-forward `f θ`. -/
theorem ent_eq_finiteEntropy {f : X → L} (hf : Measurable f) (hfin : FiniteLabels θ f) :
    ent θ f = finiteEntropy ((θ.map f).toPMF) ((finiteLabels_iff_toPMF hf).1 hfin) :=
  ent_eq_finiteEntropy' hf _

/-- A statistic of the law of a labelling is the law of the recoded labelling. -/
theorem toPMF_map_map {F : X → M} (hF : Measurable F) (φ : M → L) :
    ((θ.map F).toPMF).map φ = (θ.map (φ ∘ F)).toPMF := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable φ), Measure.toPMF_toMeasure,
    Measure.toPMF_toMeasure, Measure.map_map (measurable_of_countable φ) hF]

/-- The bridge for a recoded labelling `g = φ ∘ F`: its entropy is the finite entropy of the
statistic `φ` of the law of `F`. All the inequalities of this file reduce to the vendored
calculus through this identity with a common labelling `F`. -/
theorem ent_eq_finiteEntropy_map {F : X → M} (hF : Measurable F) (φ : M → L) (g : X → L)
    (hg : g = φ ∘ F) (h : (((θ.map F).toPMF).map φ).support.Finite) :
    ent θ g = finiteEntropy (((θ.map F).toPMF).map φ) h := by
  subst hg
  have h' : ((θ.map (φ ∘ F)).toPMF).support.Finite := by rwa [← toPMF_map_map hF φ]
  rw [ent_eq_finiteEntropy' ((measurable_of_countable φ).comp hF) h']
  exact finiteEntropy_congr (toPMF_map_map hF φ).symm _ _

omit [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L] in
/-- The finiteness of the support of a statistic of the law of a labelling with finite
labels. -/
theorem toPMF_map_support_finite {F : X → M} (hF : Measurable F) (hfin : FiniteLabels θ F)
    (φ : M → L) : (((θ.map F).toPMF).map φ).support.Finite := by
  rw [PMF.support_map]
  exact ((finiteLabels_iff_toPMF hF).1 hfin).image φ

end Measurable

/-! ### Elementary properties and the chain rule -/

section Elementary

/-- Entropy is nonnegative, since every term `-t log t` with `t ∈ [0, 1]` is. -/
theorem ent_nonneg [IsZeroOrProbabilityMeasure θ] (f : X → L) : 0 ≤ ent θ f :=
  tsum_nonneg fun _ => Real.negMulLog_nonneg measureReal_nonneg measureReal_le_one

/-- The zero measure has zero entropy; the components of null fibres are zero measures. -/
theorem ent_zero (f : X → L) : ent (0 : Measure X) f = 0 := by
  simp [ent]

/-- An injective recoding of the labels does not change the partition, hence not its entropy. -/
theorem ent_comp_injective {φ : L → L'} (hφ : Function.Injective φ) (f : X → L) :
    ent θ (φ ∘ f) = ent θ f := by
  unfold ent
  have hsupp : Function.support (fun c => Real.negMulLog (θ.real ((φ ∘ f) ⁻¹' {c}))) ⊆
      Set.range φ := by
    intro c hc
    by_contra hcr
    apply hc
    have he : (φ ∘ f) ⁻¹' {c} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false]
      exact fun h => hcr ⟨f x, h⟩
    simp [he]
  rw [← hφ.tsum_eq hsupp]
  refine tsum_congr fun b => ?_
  have he : (φ ∘ f) ⁻¹' {φ b} = f ⁻¹' {b} := by
    ext x
    simp [hφ.eq_iff]
  simp only [he]

/-- The form of `ent_comp_injective` for a labelling `g = φ ∘ f` with `φ` injective. -/
theorem ent_eq_of_injective {φ : L → L'} (hφ : Function.Injective φ) {f : X → L} {g : X → L'}
    (hg : g = φ ∘ f) : ent θ g = ent θ f := by
  subst hg
  exact ent_comp_injective hφ f

/-- The join is symmetric: `H(θ, 𝒟 ∨ ℰ) = H(θ, ℰ ∨ 𝒟)`. -/
theorem ent_pair_comm (f : X → L) (g : X → L') :
    ent θ (fun x => (f x, g x)) = ent θ (fun x => (g x, f x)) :=
  ent_eq_of_injective Prod.swap_injective rfl

/-- Labellings which agree almost everywhere have the same entropy. -/
theorem ent_congr_ae {f g : X → L} (h : f =ᵐ[θ] g) : ent θ f = ent θ g := by
  unfold ent
  refine tsum_congr fun b => ?_
  rw [measureReal_def, measureReal_def, measure_congr (h.preimage {b})]

/-- The chain rule `H(θ, 𝒟 ∨ ℰ) = H(θ, ℰ) + H(θ, 𝒟 ∣ ℰ)`, which is
the definition of `cent`. -/
theorem ent_pair_eq_add_cent (f : X → L) (g : X → L') :
    ent θ (fun x => (f x, g x)) = ent θ g + cent θ f g := by
  unfold cent
  ring

/-- The conditional chain rule `H(θ, 𝒟 ∨ ℰ ∣ 𝒬) = H(θ, ℰ ∣ 𝒬) + H(θ, 𝒟 ∣ 𝒬 ∨ ℰ)`,
with `ℰ = f`, `𝒟 = f'` and `𝒬 = g`. -/
theorem cent_pair_left (f : X → L) (f' : X → L') (g : X → L'') :
    cent θ (fun x => (f x, f' x)) g = cent θ f g + cent θ f' (fun x => (f x, g x)) := by
  have h : ent θ (fun x => ((f x, f' x), g x)) = ent θ (fun x => (f' x, (f x, g x))) := by
    refine ent_eq_of_injective (φ := fun a : L' × L × L'' => ((a.2.1, a.1), a.2.2)) ?_ rfl
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨h.1.2, h.1.1, h.2⟩
  unfold cent
  linarith

/-- A labelling determined by the conditioning labelling has zero conditional entropy. -/
theorem cent_eq_zero_of_factor {f : X → L} {g : X → L'} (φ : L' → L) (h : f = φ ∘ g) :
    cent θ f g = 0 := by
  subst h
  have he : ent θ (fun x => ((φ ∘ g) x, g x)) = ent θ g :=
    ent_eq_of_injective (φ := fun c => (φ c, c)) (fun _ _ h => (Prod.mk.inj h).2) rfl
  unfold cent
  linarith

/-- `H(θ, 𝒟 ∣ 𝒟) = 0`. -/
theorem cent_self (f : X → L) : cent θ f f = 0 :=
  cent_eq_zero_of_factor id rfl

/-- An injective recoding of the first labelling does not change the conditional entropy. -/
theorem cent_comp_left_eq_of_injective {φ : L → L'} (hφ : Function.Injective φ) (f : X → L)
    (g : X → L'') : cent θ (φ ∘ f) g = cent θ f g := by
  have h : ent θ (fun x => ((φ ∘ f) x, g x)) = ent θ (fun x => (f x, g x)) :=
    ent_eq_of_injective (hφ.prodMap Function.injective_id) rfl
  unfold cent
  rw [h]

/-- An injective recoding of the conditioning labelling does not change the conditional
entropy. -/
theorem cent_comp_right_eq_of_injective {ψ : L' → L''} (hψ : Function.Injective ψ) (f : X → L)
    (g : X → L') : cent θ f (ψ ∘ g) = cent θ f g := by
  have h : ent θ (fun x => (f x, (ψ ∘ g) x)) = ent θ (fun x => (f x, g x)) :=
    ent_eq_of_injective (Function.injective_id.prodMap hψ) rfl
  unfold cent
  rw [h, ent_comp_injective hψ]

end Elementary

/-! ### Inequalities through the vendored calculus -/

section Inequalities

variable [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L]
variable [MeasurableSpace L'] [MeasurableSingletonClass L'] [Countable L']
variable [MeasurableSpace L''] [MeasurableSingletonClass L''] [Countable L'']

omit [Countable L] in
/-- Entropy of a push-forward, `H(ψ θ, 𝒞) = H(θ, ψ⁻¹ 𝒞)` for the partition
`𝒞` into the fibres of `f`. -/
theorem ent_map {Y : Type*} [MeasurableSpace Y] {ψ : X → Y} (hψ : Measurable ψ) {f : Y → L}
    (hf : Measurable f) : ent (θ.map ψ) f = ent θ (f ∘ ψ) := by
  unfold ent
  refine tsum_congr fun b => ?_
  rw [map_measureReal_apply hψ (hf (measurableSet_singleton b))]
  rfl

omit [Countable L] [Countable L'] in
/-- Conditional entropy of a push-forward. -/
theorem cent_map {Y : Type*} [MeasurableSpace Y] {ψ : X → Y} (hψ : Measurable ψ) {f : Y → L}
    {g : Y → L'} (hf : Measurable f) (hg : Measurable g) :
    cent (θ.map ψ) f g = cent θ (f ∘ ψ) (g ∘ ψ) := by
  unfold cent
  rw [ent_map hψ (hf.prodMk hg), ent_map hψ hg]
  rfl

omit [Countable L] in
/-- Finite labels for a push-forward. -/
theorem finiteLabels_map_iff {Y : Type*} [MeasurableSpace Y] {ψ : X → Y} (hψ : Measurable ψ)
    {f : Y → L} (hf : Measurable f) : FiniteLabels (θ.map ψ) f ↔ FiniteLabels θ (f ∘ ψ) := by
  have he : (fun b => θ.map ψ (f ⁻¹' {b})) = fun b => θ ((f ∘ ψ) ⁻¹' {b}) :=
    funext fun b => Measure.map_apply hψ (hf (measurableSet_singleton b))
  unfold FiniteLabels
  rw [he]

omit [Countable L] in
/-- Finite labels pass to a push-forward. -/
theorem FiniteLabels.map {Y : Type*} [MeasurableSpace Y] {ψ : X → Y} (hψ : Measurable ψ)
    {f : Y → L} (hf : Measurable f) (h : FiniteLabels θ (f ∘ ψ)) : FiniteLabels (θ.map ψ) f :=
  (finiteLabels_map_iff hψ hf).2 h

variable [IsProbabilityMeasure θ]

/-- A coarser partition has smaller entropy: `g = φ ∘ f` gives `H(θ, g) ≤ H(θ, f)`; the vendored
`finiteEntropy_map_le`. -/
theorem ent_le_of_factor {f : X → L} (hf : Measurable f) (hfin : FiniteLabels θ f) (φ : L → L')
    {g : X → L'} (hg : g = φ ∘ f) : ent θ g ≤ ent θ f := by
  have hp := (finiteLabels_iff_toPMF hf).1 hfin
  rw [ent_eq_finiteEntropy_map hf φ g hg (toPMF_map_support_finite hf hfin φ),
    ent_eq_finiteEntropy' hf hp]
  exact finiteEntropy_map_le _ hp φ

/-- Recoding the labels cannot increase entropy. -/
theorem ent_comp_le {f : X → L} (hf : Measurable f) (hfin : FiniteLabels θ f) (φ : L → L') :
    ent θ (φ ∘ f) ≤ ent θ f :=
  ent_le_of_factor hf hfin φ rfl

/-- Subadditivity `H(θ, 𝒟 ∨ ℰ) ≤ H(θ, 𝒟) + H(θ, ℰ)`, equivalently
`H(θ, 𝒟 ∣ ℰ) ≤ H(θ, 𝒟)`; the vendored `finiteEntropy_pair_map_le`. -/
theorem ent_pair_le {f : X → L} {g : X → L'} (hf : Measurable f) (hg : Measurable g)
    (hfinf : FiniteLabels θ f) (hfing : FiniteLabels θ g) :
    ent θ (fun x => (f x, g x)) ≤ ent θ f + ent θ g := by
  have hF := hf.prodMk hg
  have hp := (finiteLabels_iff_toPMF hF).1 (hfinf.pair hfing)
  have h := finiteEntropy_pair_map_le _ hp Prod.fst Prod.snd
  rwa [← ent_eq_finiteEntropy_map hF (fun a : L × L' => (a.1, a.2)) (fun x => (f x, g x)) rfl,
    ← ent_eq_finiteEntropy_map hF Prod.fst f rfl,
    ← ent_eq_finiteEntropy_map hF Prod.snd g rfl] at h

/-- `H(θ, ℰ) ≤ H(θ, 𝒟 ∨ ℰ)`. -/
theorem ent_le_ent_pair {f : X → L} {g : X → L'} (hf : Measurable f) (hg : Measurable g)
    (hfinf : FiniteLabels θ f) (hfing : FiniteLabels θ g) :
    ent θ g ≤ ent θ (fun x => (f x, g x)) :=
  ent_le_of_factor (hf.prodMk hg) (hfinf.pair hfing) Prod.snd rfl

/-- `H(θ, 𝒟) ≤ H(θ, 𝒟 ∨ ℰ)`. -/
theorem ent_le_ent_pair_left {f : X → L} {g : X → L'} (hf : Measurable f) (hg : Measurable g)
    (hfinf : FiniteLabels θ f) (hfing : FiniteLabels θ g) :
    ent θ f ≤ ent θ (fun x => (f x, g x)) :=
  ent_le_of_factor (hf.prodMk hg) (hfinf.pair hfing) Prod.fst rfl

/-- Conditional entropy is nonnegative. -/
theorem cent_nonneg {f : X → L} {g : X → L'} (hf : Measurable f) (hg : Measurable g)
    (hfinf : FiniteLabels θ f) (hfing : FiniteLabels θ g) : 0 ≤ cent θ f g := by
  have h := ent_le_ent_pair hf hg hfinf hfing
  unfold cent
  linarith

/-- Conditioning cannot increase entropy: `H(θ, 𝒟 ∣ ℰ) ≤ H(θ, 𝒟)`. -/
theorem cent_le_ent {f : X → L} {g : X → L'} (hf : Measurable f) (hg : Measurable g)
    (hfinf : FiniteLabels θ f) (hfing : FiniteLabels θ g) : cent θ f g ≤ ent θ f := by
  have h := ent_pair_le hf hg hfinf hfing
  unfold cent
  linarith

/-- Strong subadditivity: `H(𝒟 ∨ ℰ ∨ ℱ) + H(𝒟) ≤ H(𝒟 ∨ ℰ) + H(𝒟 ∨ ℱ)`, the vendored
`finiteEntropy_submodular`; it is the monotonicity of conditional entropy in the conditioning
partition. -/
theorem ent_submodular {f : X → L} {g : X → L'} {h : X → L''} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h) (hfinf : FiniteLabels θ f)
    (hfing : FiniteLabels θ g) (hfinh : FiniteLabels θ h) :
    ent θ (fun x => (f x, (g x, h x))) + ent θ f ≤
      ent θ (fun x => (f x, g x)) + ent θ (fun x => (f x, h x)) := by
  have hF := hf.prodMk (hg.prodMk hh)
  have hp := (finiteLabels_iff_toPMF hF).1 (hfinf.pair (hfing.pair hfinh))
  have key := finiteEntropy_submodular _ hp Prod.fst (fun a => a.2.1) (fun a => a.2.2)
  rwa [← ent_eq_finiteEntropy_map hF (fun a : L × L' × L'' => (a.1, (a.2.1, a.2.2)))
      (fun x => (f x, (g x, h x))) rfl,
    ← ent_eq_finiteEntropy_map hF (fun a : L × L' × L'' => (a.1, a.2.1))
      (fun x => (f x, g x)) rfl,
    ← ent_eq_finiteEntropy_map hF (fun a : L × L' × L'' => (a.1, a.2.2))
      (fun x => (f x, h x)) rfl,
    ← ent_eq_finiteEntropy_map hF Prod.fst f rfl] at key

/-- The cardinality bound: if every label of positive mass lies in
`s`, then `H(θ, 𝒟) ≤ log #s`; the vendored `finiteEntropy_le_log_of_card_le`. -/
theorem ent_le_log_card {f : X → L} (hf : Measurable f) (s : Finset L)
    (hs : ∀ b, θ (f ⁻¹' {b}) ≠ 0 → b ∈ s) : ent θ f ≤ Real.log s.card := by
  have hp := (finiteLabels_iff_toPMF hf).1 (finiteLabels_of_subset s hs)
  rw [ent_eq_finiteEntropy' hf hp]
  apply finiteEntropy_le_log_of_card_le
  apply Finset.card_le_card
  intro b hb
  rw [Set.Finite.mem_toFinset, PMF.mem_support_iff, toPMF_map_apply hf] at hb
  exact hs b hb

/-- The cardinality bound for a labelling which almost surely takes values in `s`. -/
theorem ent_le_log_of_ae_mem {f : X → L} (hf : Measurable f) (s : Finset L)
    (h : ∀ᵐ x ∂θ, f x ∈ s) : ent θ f ≤ Real.log s.card :=
  ent_le_log_card hf s (mem_of_ae_mem h)

/-- An almost surely constant labelling has zero entropy. -/
theorem ent_eq_zero_of_ae_eq {f : X → L} (hf : Measurable f) (b : L) (h : ∀ᵐ x ∂θ, f x = b) :
    ent θ f = 0 := by
  refine le_antisymm ?_ (ent_nonneg f)
  have h' : ∀ᵐ x ∂θ, f x ∈ ({b} : Finset L) := by
    filter_upwards [h] with x hx
    simp [hx]
  simpa using ent_le_log_of_ae_mem hf {b} h'

end Inequalities

/-! ### Components and component averages -/

section Components

/-- The component `θ_{f = b}` of a label of positive mass is a probability measure. -/
theorem comp_isProbabilityMeasure [IsFiniteMeasure θ] {f : X → L} {b : L}
    (h : θ (f ⁻¹' {b}) ≠ 0) : IsProbabilityMeasure (comp θ f b) :=
  cond_isProbabilityMeasure h

variable [MeasurableSpace L] [MeasurableSingletonClass L]

/-- The component `θ_E = θ(E)⁻¹ θ|_E` of the fibre `E = f⁻¹ {b}`. -/
theorem comp_apply {f : X → L} (hf : Measurable f) (b : L) (s : Set X) :
    comp θ f b s = (θ (f ⁻¹' {b}))⁻¹ * θ (f ⁻¹' {b} ∩ s) :=
  cond_apply (hf (measurableSet_singleton b)) θ s

/-- The real mass of a set under a component. -/
theorem comp_real_apply {f : X → L} (hf : Measurable f) (b : L) (s : Set X) :
    (comp θ f b).real s = θ.real (f ⁻¹' {b} ∩ s) / θ.real (f ⁻¹' {b}) := by
  rw [measureReal_def, comp_apply hf, ENNReal.toReal_mul, ENNReal.toReal_inv, measureReal_def,
    measureReal_def, div_eq_inv_mul]

/-- A component is carried by its fibre. -/
theorem ae_comp_mem {f : X → L} (hf : Measurable f) (b : L) :
    ∀ᵐ x ∂(comp θ f b), f x = b :=
  ae_cond_mem (hf (measurableSet_singleton b))

/-- The decomposition of a finite measure into its components: `θ = ∑_b θ(f⁻¹ {b}) θ_{f = b}`
over the labels of positive mass. -/
theorem eq_sum_comp [IsFiniteMeasure θ] [Countable L] {f : X → L} (hf : Measurable f)
    (hfin : FiniteLabels θ f) : θ = ∑ b ∈ hfin.toFinset, θ (f ⁻¹' {b}) • comp θ f b := by
  ext A hA
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [← sum_measure_inter_fiber hf hfin.toFinset (fun _ hb => hfin.mem_toFinset.2 hb) hA]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm, comp, cond_mul_eq_inter (hf (measurableSet_singleton b)), Set.inter_comm]

/-- The component of a push-forward is the push-forward of the component of the pulled-back
labelling. -/
theorem comp_map {Y : Type*} [MeasurableSpace Y] {ψ : X → Y} (hψ : Measurable ψ) {f : Y → L}
    (hf : Measurable f) (b : L) : comp (θ.map ψ) f b = (comp θ (f ∘ ψ) b).map ψ := by
  ext s hs
  rw [Measure.map_apply hψ hs, comp, comp, cond_apply (hf (measurableSet_singleton b)),
    cond_apply ((hf.comp hψ) (measurableSet_singleton b)),
    Measure.map_apply hψ (hf (measurableSet_singleton b)),
    Measure.map_apply hψ ((hf (measurableSet_singleton b)).inter hs)]
  rfl

omit [MeasurableSpace L] [MeasurableSingletonClass L] in
/-- The component average is additive in the averaged quantity. -/
theorem cavg_add {f : X → L} (hfin : FiniteLabels θ f) (F G : Measure X → ℝ) :
    cavg θ f (fun ρ => F ρ + G ρ) = cavg θ f F + cavg θ f G := by
  simp only [cavg_eq_sum hfin, mul_add, Finset.sum_add_distrib]

omit [MeasurableSpace L] [MeasurableSingletonClass L] in
/-- The component average commutes with differences. -/
theorem cavg_sub {f : X → L} (hfin : FiniteLabels θ f) (F G : Measure X → ℝ) :
    cavg θ f (fun ρ => F ρ - G ρ) = cavg θ f F - cavg θ f G := by
  simp only [cavg_eq_sum hfin, mul_sub, Finset.sum_sub_distrib]

omit [MeasurableSpace L] [MeasurableSingletonClass L] in
/-- The component average is homogeneous. -/
theorem cavg_const_mul {f : X → L} (hfin : FiniteLabels θ f) (a : ℝ) (F : Measure X → ℝ) :
    cavg θ f (fun ρ => a * F ρ) = a * cavg θ f F := by
  simp only [cavg_eq_sum hfin, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

omit [MeasurableSpace L] [MeasurableSingletonClass L] in
/-- The component average is monotone, comparing only the components of positive mass. -/
theorem cavg_mono {f : X → L} (hfin : FiniteLabels θ f) {F G : Measure X → ℝ}
    (h : ∀ b, θ (f ⁻¹' {b}) ≠ 0 → F (comp θ f b) ≤ G (comp θ f b)) :
    cavg θ f F ≤ cavg θ f G := by
  rw [cavg_eq_sum hfin, cavg_eq_sum hfin]
  exact Finset.sum_le_sum fun b hb =>
    mul_le_mul_of_nonneg_left (h b (hfin.mem_toFinset.1 hb)) measureReal_nonneg

omit [MeasurableSpace L] [MeasurableSingletonClass L] in
/-- The component average of a quantity nonnegative on the components is nonnegative. -/
theorem cavg_nonneg {f : X → L} (hfin : FiniteLabels θ f) {F : Measure X → ℝ}
    (h : ∀ b, θ (f ⁻¹' {b}) ≠ 0 → 0 ≤ F (comp θ f b)) : 0 ≤ cavg θ f F := by
  rw [cavg_eq_sum hfin]
  exact Finset.sum_nonneg fun b hb => mul_nonneg measureReal_nonneg (h b (hfin.mem_toFinset.1 hb))

variable [Countable L] [IsProbabilityMeasure θ]

/-- The component average of a constant is the constant. -/
theorem cavg_const {f : X → L} (hf : Measurable f) (hfin : FiniteLabels θ f) (a : ℝ) :
    cavg θ f (fun _ => a) = a := by
  rw [cavg_eq_sum hfin, ← Finset.sum_mul,
    sum_measureReal_fiber hf _ (fun _ hb => hfin.mem_toFinset.2 hb), one_mul]

/-- An upper bound on the components bounds the component average. -/
theorem cavg_le_of_le {f : X → L} (hf : Measurable f) (hfin : FiniteLabels θ f)
    {F : Measure X → ℝ} {B : ℝ} (h : ∀ b, θ (f ⁻¹' {b}) ≠ 0 → F (comp θ f b) ≤ B) :
    cavg θ f F ≤ B :=
  (cavg_mono hfin (G := fun _ => B) h).trans_eq (cavg_const hf hfin B)

/-- A lower bound on the components bounds the component average. -/
theorem le_cavg_of_le {f : X → L} (hf : Measurable f) (hfin : FiniteLabels θ f)
    {F : Measure X → ℝ} {B : ℝ} (h : ∀ b, θ (f ⁻¹' {b}) ≠ 0 → B ≤ F (comp θ f b)) :
    B ≤ cavg θ f F :=
  (cavg_const hf hfin B).symm.trans_le (cavg_mono hfin (F := fun _ => B) h)

/-- Markov's inequality for component averages: if `F ≤ B` on the components and `t < B`, the
components with `F > t` carry mass at least `(𝔼 F - t) / (B - t)`. -/
theorem cavg_indicator_ge {f : X → L} (hf : Measurable f) (hfin : FiniteLabels θ f)
    {F : Measure X → ℝ} {t B : ℝ} (htB : t < B)
    (hF : ∀ b, θ (f ⁻¹' {b}) ≠ 0 → F (comp θ f b) ≤ B) :
    (cavg θ f F - t) / (B - t) ≤ cavg θ f (fun ρ => if t < F ρ then 1 else 0) := by
  have hpos : 0 < B - t := sub_pos.2 htB
  rw [div_le_iff₀ hpos]
  have h1 : cavg θ f F ≤ cavg θ f (fun ρ => t + (B - t) * (if t < F ρ then 1 else 0)) := by
    apply cavg_mono hfin
    intro b hb
    split_ifs with h
    · linarith [hF b hb]
    · linarith [not_lt.1 h]
  rw [cavg_add hfin, cavg_const hf hfin, cavg_const_mul hfin] at h1
  linarith

omit [Countable L] [IsProbabilityMeasure θ] [MeasurableSpace L] [MeasurableSingletonClass L] in
/-- Markov's inequality for component averages: if `F ≥ 0` on the components and `t > 0`, the
components with `F ≥ t` carry mass at most `𝔼 F / t`. -/
theorem cavg_indicator_le {f : X → L} (hfin : FiniteLabels θ f) {F : Measure X → ℝ} {t : ℝ}
    (ht : 0 < t) (hF : ∀ b, θ (f ⁻¹' {b}) ≠ 0 → 0 ≤ F (comp θ f b)) :
    cavg θ f (fun ρ => if t ≤ F ρ then 1 else 0) ≤ cavg θ f F / t := by
  rw [le_div_iff₀ ht, mul_comm, ← cavg_const_mul hfin]
  apply cavg_mono hfin
  intro b hb
  split_ifs with h
  · linarith
  · linarith [hF b hb]

end Components

/-- The identity `q · (-(p/q) log(p/q)) = -p log p + p log q` for `q > 0`. -/
private lemma mul_negMulLog_div {p q : ℝ} (hq : 0 < q) :
    q * Real.negMulLog (p / q) = Real.negMulLog p + p * Real.log q := by
  have hq' : q ≠ 0 := hq.ne'
  rw [div_eq_mul_inv, Real.negMulLog_mul]
  simp only [Real.negMulLog, Real.log_inv]
  field_simp

/-! ### Conditional entropy as an average, monotonicity and commensurability -/

section Conditional

variable [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L]
variable [MeasurableSpace L'] [MeasurableSingletonClass L'] [Countable L']
variable [MeasurableSpace L''] [MeasurableSingletonClass L''] [Countable L'']
variable [IsProbabilityMeasure θ]

omit [Countable L'] in
/-- Conditional entropy is the average entropy of the components, the definition
`H(θ, 𝒟 ∣ ℰ) = ∑_E θ(E) H(θ_E, 𝒟)`, here derived from the chain rule. -/
theorem cent_eq_cavg {f : X → L} {g : X → L'} (hf : Measurable f) (hg : Measurable g)
    (hfinf : FiniteLabels θ f) (hfing : FiniteLabels θ g) :
    cent θ f g = cavg θ g (fun ρ => ent ρ f) := by
  have hSf : ∀ b, θ (f ⁻¹' {b}) ≠ 0 → b ∈ hfinf.toFinset := fun _ hb => hfinf.mem_toFinset.2 hb
  have hSg : ∀ c, θ (g ⁻¹' {c}) ≠ 0 → c ∈ hfing.toFinset := fun _ hc => hfing.mem_toFinset.2 hc
  have hpair : ent θ (fun x => (f x, g x)) = ∑ c ∈ hfing.toFinset, ∑ b ∈ hfinf.toFinset,
      Real.negMulLog (θ.real (g ⁻¹' {c} ∩ f ⁻¹' {b})) := by
    rw [ent_eq_sum_of_subset (hfinf.toFinset ×ˢ hfing.toFinset), Finset.sum_product_right]
    · simp only [preimage_pair_singleton]
    · rintro ⟨b, c⟩ h
      rw [preimage_pair_singleton] at h
      rw [Finset.mem_product]
      exact ⟨hSf b fun h0 => h (measure_mono_null Set.inter_subset_right h0),
        hSg c fun h0 => h (measure_mono_null Set.inter_subset_left h0)⟩
  have hcomp : ∀ c ∈ hfing.toFinset, θ.real (g ⁻¹' {c}) * ent (comp θ g c) f =
      ∑ b ∈ hfinf.toFinset, Real.negMulLog (θ.real (g ⁻¹' {c} ∩ f ⁻¹' {b})) -
        Real.negMulLog (θ.real (g ⁻¹' {c})) := by
    intro c hc
    have hq : 0 < θ.real (g ⁻¹' {c}) := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos (hfing.mem_toFinset.1 hc) (measure_ne_top _ _)
    rw [ent_eq_sum_of_subset (θ := comp θ g c) hfinf.toFinset fun b hb =>
      hSf b fun h0 => hb (cond_absolutelyContinuous h0), Finset.mul_sum]
    simp only [comp_real_apply hg, mul_negMulLog_div hq]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul,
      sum_measureReal_inter_fiber hf _ hSf (hg (measurableSet_singleton c))]
    simp only [Real.negMulLog]
    ring
  rw [cent, hpair, cavg_eq_sum hfing, ent_eq_sum hfing, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun c hc => (hcomp c hc).symm

omit [Countable L'] in
/-- Conditional entropy as the finite sum `∑_c θ(g⁻¹ {c}) H(θ_{g = c}, 𝒟)` over the labels of
positive mass. -/
theorem cent_eq_sum_comp {f : X → L} {g : X → L'} (hf : Measurable f) (hg : Measurable g)
    (hfinf : FiniteLabels θ f) (hfing : FiniteLabels θ g) :
    cent θ f g = ∑ c ∈ hfing.toFinset, θ.real (g ⁻¹' {c}) * ent (comp θ g c) f := by
  rw [cent_eq_cavg hf hg hfinf hfing, cavg_eq_sum hfing]

/-- Conditional entropy increases with the first partition: `f = φ ∘ f'` gives
`H(θ, f ∣ g) ≤ H(θ, f' ∣ g)`. -/
theorem cent_le_of_factor {f : X → L} {f' : X → L'} {g : X → L''} (hf' : Measurable f')
    (hg : Measurable g) (hfinf' : FiniteLabels θ f') (hfing : FiniteLabels θ g) (φ : L' → L)
    (h : f = φ ∘ f') : cent θ f g ≤ cent θ f' g := by
  have he := ent_le_of_factor (hf'.prodMk hg) (hfinf'.pair hfing) (Prod.map φ id)
    (g := fun x => (f x, g x)) (by subst h; rfl)
  unfold cent
  linarith

/-- Conditioning on a finer partition cannot increase entropy:
`H(θ, f ∣ g ∨ h) ≤ H(θ, f ∣ g)`. -/
theorem cent_pair_right_le {f : X → L} {g : X → L'} {h : X → L''} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h) (hfinf : FiniteLabels θ f)
    (hfing : FiniteLabels θ g) (hfinh : FiniteLabels θ h) :
    cent θ f (fun x => (g x, h x)) ≤ cent θ f g := by
  have hsub := ent_submodular hg hf hh hfing hfinf hfinh
  have e1 : ent θ (fun x => (f x, (g x, h x))) = ent θ (fun x => (g x, (f x, h x))) := by
    refine ent_eq_of_injective (φ := fun a : L' × L × L'' => (a.2.1, (a.1, a.2.2))) ?_ rfl
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨h.2.1, h.1, h.2.2⟩
  have e2 := ent_pair_comm (θ := θ) f g
  unfold cent
  linarith

/-- Conditional entropy decreases in the conditioning partition: `g = ψ ∘ g'` gives
`H(θ, f ∣ g') ≤ H(θ, f ∣ g)`. -/
theorem cent_anti_of_factor {f : X → L} {g : X → L'} {g' : X → L''} (hf : Measurable f)
    (hg' : Measurable g') (hfinf : FiniteLabels θ f) (hfing' : FiniteLabels θ g')
    (ψ : L'' → L') (h : g = ψ ∘ g') : cent θ f g' ≤ cent θ f g := by
  subst h
  have e : cent θ f g' = cent θ f (fun x => ((ψ ∘ g') x, g' x)) :=
    (cent_comp_right_eq_of_injective (ψ := fun c => (ψ c, c))
      (fun _ _ h => (Prod.mk.inj h).2) f g').symm
  rw [e]
  exact cent_pair_right_le hf ((measurable_of_countable ψ).comp hg') hg' hfinf (hfing'.comp ψ)
    hfing'

/-- `H(θ, 𝒟 ∣ ℰ) ≥ H(θ, 𝒟) - H(θ, ℰ)`, from the chain rule and `H(θ, 𝒟) ≤ H(θ, 𝒟 ∨ ℰ)`. -/
theorem ent_sub_ent_le_cent {f : X → L} {g : X → L'} (hf : Measurable f) (hg : Measurable g)
    (hfinf : FiniteLabels θ f) (hfing : FiniteLabels θ g) : ent θ f - ent θ g ≤ cent θ f g := by
  have h := ent_le_ent_pair_left hf hg hfinf hfing
  unfold cent
  linarith

omit [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L] [MeasurableSpace L']
  [MeasurableSingletonClass L'] [Countable L'] [MeasurableSpace L'']
  [MeasurableSingletonClass L''] [Countable L''] [IsProbabilityMeasure θ] in
/-- `log #s ≤ log N` for a finset of at most `N` elements, including the empty finset. -/
theorem log_card_le_log {s : Finset L} {N : ℕ} (h : s.card ≤ N) :
    Real.log s.card ≤ Real.log N := by
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg N
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast h)

omit [Countable L'] in
/-- A component for a label `c` of `g` whose fibre meets at most `N` labels of `f` has entropy
at most `log N`. -/
theorem ent_comp_le_log {f : X → L} {g : X → L'} (hf : Measurable f) (hg : Measurable g)
    (c : L') {N : ℕ} (h : ∃ s : Finset L, s.card ≤ N ∧ ∀ x, g x = c → f x ∈ s) :
    ent (comp θ g c) f ≤ Real.log N := by
  obtain ⟨s, hsN, hs⟩ := h
  by_cases hc : θ (g ⁻¹' {c}) = 0
  · rw [comp, cond_eq_zero_of_meas_eq_zero hc, ent_zero]
    exact Real.log_natCast_nonneg N
  have := comp_isProbabilityMeasure hc
  refine (ent_le_log_card hf s fun b hb => ?_).trans (log_card_le_log hsN)
  have hpos := inter_pos_of_cond_ne_zero (hg (measurableSet_singleton c)) hb
  obtain ⟨x, hxc, hxb⟩ := nonempty_of_measure_ne_zero hpos.ne'
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hxc hxb
  rw [← hxb]
  exact hs x hxc

/-- If every label of `g` meets at most `N` labels of `f`, then `H(θ, f ∣ g) ≤ log N`. -/
theorem cent_le_log_of_fiber_card {f : X → L} {g : X → L'} (hf : Measurable f)
    (hg : Measurable g) (hfinf : FiniteLabels θ f) (hfing : FiniteLabels θ g) {N : ℕ}
    (h : ∀ c, ∃ s : Finset L, s.card ≤ N ∧ ∀ x, g x = c → f x ∈ s) :
    cent θ f g ≤ Real.log N := by
  rw [cent_eq_cavg hf hg hfinf hfing]
  exact cavg_le_of_le hg hfing fun c _ => ent_comp_le_log hf hg c (h c)

/-- One half of the commensurability bound: if every label of `g`
meets at most `N` labels of `f`, then `H(θ, f) ≤ H(θ, g) + log N`. -/
theorem ent_le_ent_add_log_of_fiber_card {f : X → L} {g : X → L'} (hf : Measurable f)
    (hg : Measurable g) (hfinf : FiniteLabels θ f) (hfing : FiniteLabels θ g) {N : ℕ}
    (h : ∀ c, ∃ s : Finset L, s.card ≤ N ∧ ∀ x, g x = c → f x ∈ s) :
    ent θ f ≤ ent θ g + Real.log N := by
  have h1 := ent_le_ent_pair_left hf hg hfinf hfing
  have h2 := cent_le_log_of_fiber_card hf hg hfinf hfing h
  unfold cent at h2
  linarith

/-- The commensurability bound, in the sharper form
`|H(θ, 𝒟) - H(θ, ℰ)| ≤ log C` for `C`-commensurable partitions. -/
theorem abs_ent_sub_ent_le_log_of_commensurable {f : X → L} {g : X → L'} (hf : Measurable f)
    (hg : Measurable g) (hfinf : FiniteLabels θ f) (hfing : FiniteLabels θ g) {N : ℕ}
    (hfg : ∀ c, ∃ s : Finset L, s.card ≤ N ∧ ∀ x, g x = c → f x ∈ s)
    (hgf : ∀ b, ∃ s : Finset L', s.card ≤ N ∧ ∀ x, f x = b → g x ∈ s) :
    |ent θ f - ent θ g| ≤ Real.log N := by
  have h1 := ent_le_ent_add_log_of_fiber_card hf hg hfinf hfing hfg
  have h2 := ent_le_ent_add_log_of_fiber_card hg hf hfing hfinf hgf
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The conditional form of the commensurability bound: if every label of `(g, h)` meets at
most `N` labels of `f`, then `H(θ, f ∣ h) ≤ H(θ, g ∣ h) + log N`. -/
theorem cent_le_cent_add_log_of_fiber_card {f : X → L} {g : X → L'} {h : X → L''}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (hfinf : FiniteLabels θ f)
    (hfing : FiniteLabels θ g) (hfinh : FiniteLabels θ h) {N : ℕ}
    (hN : ∀ c, ∃ s : Finset L, s.card ≤ N ∧ ∀ x, (g x, h x) = c → f x ∈ s) :
    cent θ f h ≤ cent θ g h + Real.log N := by
  have h1 : cent θ f h ≤ cent θ (fun x => (g x, f x)) h :=
    cent_le_of_factor (hg.prodMk hf) hh (hfing.pair hfinf) hfinh Prod.snd rfl
  have h2 := cent_pair_left (θ := θ) g f h
  have h3 := cent_le_log_of_fiber_card hf (hg.prodMk hh) hfinf (hfing.pair hfinh) hN
  linarith

/-- Commensurable conditioning partitions change conditional entropy by at most `2 log N`: if
every label of `g'` meets at most `N` labels of `g` and conversely, then
`H(θ, f ∣ g) ≤ H(θ, f ∣ g') + 2 log N`. -/
theorem cent_le_cent_add_two_log_of_commensurable_cond {f : X → L} {g : X → L'}
    {g' : X → L''} (hf : Measurable f) (hg : Measurable g) (hg' : Measurable g')
    (hfinf : FiniteLabels θ f) (hfing : FiniteLabels θ g) (hfing' : FiniteLabels θ g')
    {N : ℕ} (h1 : ∀ c, ∃ s : Finset L', s.card ≤ N ∧ ∀ x, g' x = c → g x ∈ s)
    (h2 : ∀ c, ∃ s : Finset L'', s.card ≤ N ∧ ∀ x, g x = c → g' x ∈ s) :
    cent θ f g ≤ cent θ f g' + 2 * Real.log N := by
  classical
  have e1 : ent θ (fun x => (f x, g x)) ≤ ent θ (fun x => (f x, g' x)) + Real.log N := by
    refine ent_le_ent_add_log_of_fiber_card (hf.prodMk hg) (hf.prodMk hg') (hfinf.pair hfing)
      (hfinf.pair hfing') fun c => ?_
    obtain ⟨s, hs, hsub⟩ := h1 c.2
    refine ⟨s.image fun d => (c.1, d), Finset.card_image_le.trans hs, fun x hx => ?_⟩
    rw [Finset.mem_image]
    exact ⟨g x, hsub x (congrArg Prod.snd hx), Prod.ext (congrArg Prod.fst hx).symm rfl⟩
  have e2 := ent_le_ent_add_log_of_fiber_card hg' hg hfing' hfing h2
  unfold cent
  linarith

end Conditional

/-! ### Finite mixtures: concavity and almost convexity -/

section Mixture

variable {ι : Type*} [Fintype ι]

/-- The probability vector `w` as a law on `ι`. -/
private noncomputable def weightPMF {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    PMF ι :=
  PMF.ofFintype (fun i => ENNReal.ofReal (w i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw0 i), hw1, ENNReal.ofReal_one])

/-- The masses of `weightPMF`. -/
private lemma weightPMF_apply {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (i : ι) :
    weightPMF hw0 hw1 i = ENNReal.ofReal (w i) :=
  rfl

/-- The real masses of `weightPMF`. -/
private lemma weightPMF_toReal {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (i : ι) :
    (weightPMF hw0 hw1 i).toReal = w i := by
  rw [weightPMF_apply, ENNReal.toReal_ofReal (hw0 i)]

/-- The finite entropy of `weightPMF` is the entropy `H(w)` of the probability vector. -/
private lemma finiteEntropy_weightPMF {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (h : (weightPMF hw0 hw1).support.Finite) :
    finiteEntropy (weightPMF hw0 hw1) h = ∑ i, Real.negMulLog (w i) := by
  rw [finiteEntropy_eq_sum_of_support_subset _ h Finset.univ (by simp)]
  exact Finset.sum_congr rfl fun i _ => by rw [weightPMF_toReal]

/-- The entropy of a probability vector is at most the logarithm of its length. -/
theorem sum_negMulLog_le_log_card {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    ∑ i, Real.negMulLog (w i) ≤ Real.log (Fintype.card ι) := by
  have h : (weightPMF hw0 hw1).support.Finite := Set.toFinite _
  rw [← finiteEntropy_weightPMF hw0 hw1 h]
  exact finiteEntropy_le_log_of_card_le _ h (Finset.card_le_univ _)

/-- Evaluation of a finite mixture `θ = ∑ w i θ i`. -/
private lemma mixture_apply {θs : ι → Measure X} {w : ι → ℝ}
    (hθ : θ = ∑ i, ENNReal.ofReal (w i) • θs i) (A : Set X) :
    θ A = ∑ i, ENNReal.ofReal (w i) * θs i A := by
  rw [hθ, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]

/-- The pieces of positive weight of a mixture inherit finite labels. -/
private lemma finiteLabels_of_mixture {θs : ι → Measure X} {w : ι → ℝ}
    (hθ : θ = ∑ i, ENNReal.ofReal (w i) • θs i) {F : X → M} (hfin : FiniteLabels θ F) (i : ι)
    (hi : 0 < w i) : FiniteLabels (θs i) F := by
  refine hfin.subset fun b hb h0 => hb ?_
  change θ (F ⁻¹' {b}) = 0 at h0
  change θs i (F ⁻¹' {b}) = 0
  rw [mixture_apply hθ, Finset.sum_eq_zero_iff] at h0
  exact (mul_eq_zero.1 (h0 i (Finset.mem_univ i))).resolve_left (ENNReal.ofReal_pos.2 hi).ne'

variable [MeasurableSpace M] [MeasurableSingletonClass M] [Countable M] [IsProbabilityMeasure θ]

/-- The laws of the labels under the pieces of a mixture, with the law under the mixture itself
in place of the pieces of zero weight. -/
private noncomputable def mixLaw (θ : Measure X) [IsProbabilityMeasure θ] (θs : ι → Measure X)
    (w : ι → ℝ) (hθs : ∀ i, w i ≠ 0 → IsProbabilityMeasure (θs i)) (F : X → M) (i : ι) :
    PMF M :=
  if hi : w i = 0 then (θ.map F).toPMF else
    haveI := hθs i hi
    ((θs i).map F).toPMF

/-- The laws `mixLaw` have finite support. -/
private lemma mixLaw_support_finite {θs : ι → Measure X} {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hθs : ∀ i, w i ≠ 0 → IsProbabilityMeasure (θs i))
    (hθ : θ = ∑ i, ENNReal.ofReal (w i) • θs i) {F : X → M} (hF : Measurable F)
    (hfin : FiniteLabels θ F) (i : ι) : (mixLaw θ θs w hθs F i).support.Finite := by
  by_cases hi : w i = 0
  · rw [mixLaw, dite_eq_left hi]
    exact (finiteLabels_iff_toPMF hF).1 hfin
  · have := hθs i hi
    rw [mixLaw, dite_eq_right hi]
    exact (finiteLabels_iff_toPMF hF).1
      (finiteLabels_of_mixture hθ hfin i (lt_of_le_of_ne (hw0 i) (Ne.symm hi)))

/-- Mixing the laws `mixLaw` with the weights `w` gives the law of the labels under `θ`. -/
private lemma bind_mixLaw {θs : ι → Measure X} {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hθs : ∀ i, w i ≠ 0 → IsProbabilityMeasure (θs i))
    (hθ : θ = ∑ i, ENNReal.ofReal (w i) • θs i) {F : X → M} (hF : Measurable F) :
    (weightPMF hw0 hw1).bind (mixLaw θ θs w hθs F) = (θ.map F).toPMF := by
  ext a
  rw [PMF.bind_apply, tsum_fintype, toPMF_map_apply hF, mixture_apply hθ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [weightPMF_apply]
  by_cases hi : w i = 0
  · simp [hi]
  · have := hθs i hi
    rw [mixLaw, dite_eq_right hi, toPMF_map_apply hF]

/-- The weighted entropy of a piece through `mixLaw`. -/
private lemma mul_ent_eq_mixLaw {θs : ι → Measure X} {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hθs : ∀ i, w i ≠ 0 → IsProbabilityMeasure (θs i)) {F : X → M}
    (hF : Measurable F) (i : ι) (h : (mixLaw θ θs w hθs F i).support.Finite) :
    w i * ent (θs i) F =
      (weightPMF hw0 hw1 i).toReal * finiteEntropy (mixLaw θ θs w hθs F i) h := by
  rw [weightPMF_toReal]
  by_cases hi : w i = 0
  · simp [hi]
  · have := hθs i hi
    have he : mixLaw θ θs w hθs F i = ((θs i).map F).toPMF := by rw [mixLaw, dite_eq_right hi]
    rw [ent_eq_finiteEntropy' hF (he ▸ h)]
    exact congrArg _ (finiteEntropy_congr he.symm _ _)

/-- Conditional entropy is invariant under equality of the laws. -/
private lemma conditionalEntropy_congr {α β : Type*} {p q : PMF α} (h : p = q)
    (hp : p.support.Finite) (hq : q.support.Finite) (f : α → β) :
    conditionalEntropy p hp f = conditionalEntropy q hq f := by
  subst h
  rfl

omit [MeasurableSpace M] [MeasurableSingletonClass M] [Countable M] in
/-- Conditional entropy as the vendored `conditionalEntropy` of the joint law, given its second
coordinate. -/
private lemma cent_eq_conditionalEntropy [MeasurableSpace L] [MeasurableSingletonClass L]
    [Countable L] [MeasurableSpace L'] [MeasurableSingletonClass L'] [Countable L']
    {f : X → L} {g : X → L'} (hf : Measurable f) (hg : Measurable g)
    (h : ((θ.map fun x => (f x, g x)).toPMF).support.Finite) :
    cent θ f g = conditionalEntropy ((θ.map fun x => (f x, g x)).toPMF) h Prod.snd := by
  rw [conditionalEntropy_eq_entropy_sub, cent, ← ent_eq_finiteEntropy' (hf.prodMk hg) h,
    ← ent_eq_finiteEntropy_map (hf.prodMk hg) Prod.snd g rfl]

omit [MeasurableSpace M] [MeasurableSingletonClass M] [Countable M] in
/-- The weighted conditional entropy of a piece through `mixLaw`. -/
private lemma mul_cent_eq_mixLaw [MeasurableSpace L] [MeasurableSingletonClass L]
    [Countable L] [MeasurableSpace L'] [MeasurableSingletonClass L'] [Countable L']
    {θs : ι → Measure X} {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hθs : ∀ i, w i ≠ 0 → IsProbabilityMeasure (θs i)) {f : X → L} {g : X → L'}
    (hf : Measurable f) (hg : Measurable g) (i : ι)
    (h : (mixLaw θ θs w hθs (fun x => (f x, g x)) i).support.Finite) :
    w i * cent (θs i) f g = (weightPMF hw0 hw1 i).toReal *
      conditionalEntropy (mixLaw θ θs w hθs (fun x => (f x, g x)) i) h Prod.snd := by
  rw [weightPMF_toReal]
  by_cases hi : w i = 0
  · simp [hi]
  · have := hθs i hi
    have he : mixLaw θ θs w hθs (fun x => (f x, g x)) i =
        ((θs i).map fun x => (f x, g x)).toPMF := by rw [mixLaw, dite_eq_right hi]
    rw [cent_eq_conditionalEntropy hf hg (he ▸ h)]
    exact congrArg _ (conditionalEntropy_congr he.symm _ _ _)

/-- Almost convexity of entropy, where only the pieces of positive
weight need to be probability measures; the pieces of zero weight are arbitrary measures. -/
theorem ent_le_sum_ent_add_of_ne_zero {θs : ι → Measure X} {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hθs : ∀ i, w i ≠ 0 → IsProbabilityMeasure (θs i))
    (hθ : θ = ∑ i, ENNReal.ofReal (w i) • θs i) {f : X → M} (hf : Measurable f)
    (hfin : FiniteLabels θ f) :
    ent θ f ≤ ∑ i, w i * ent (θs i) f + ∑ i, Real.negMulLog (w i) := by
  have hq := mixLaw_support_finite hw0 hθs hθ hf hfin
  have h := finiteEntropy_bind_le (weightPMF hw0 hw1) (mixLaw θ θs w hθs f) hq
  rw [finiteEntropy_weightPMF, finiteEntropy_congr (bind_mixLaw hw0 hw1 hθs hθ hf) _
    ((finiteLabels_iff_toPMF hf).1 hfin), ← ent_eq_finiteEntropy' hf] at h
  rw [Finset.sum_congr rfl fun i _ => mul_ent_eq_mixLaw hw0 hw1 hθs hf i (hq i)]
  linarith

variable {θs : ι → Measure X} [∀ i, IsProbabilityMeasure (θs i)] {w : ι → ℝ}

/-- Concavity of entropy, the left inequality of: for
`θ = ∑ w i θ i`, `∑ w i H(θ i, 𝒟) ≤ H(θ, 𝒟)`; the vendored `average_finiteEntropy_le_bind`. -/
theorem sum_ent_le_ent (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hθ : θ = ∑ i, ENNReal.ofReal (w i) • θs i) {f : X → M} (hf : Measurable f)
    (hfin : FiniteLabels θ f) : ∑ i, w i * ent (θs i) f ≤ ent θ f := by
  have hθs : ∀ i, w i ≠ 0 → IsProbabilityMeasure (θs i) := fun _ _ => inferInstance
  have hq := mixLaw_support_finite hw0 hθs hθ hf hfin
  have h := average_finiteEntropy_le_bind (weightPMF hw0 hw1) (mixLaw θ θs w hθs f) hq
  rw [finiteEntropy_congr (bind_mixLaw hw0 hw1 hθs hθ hf) _
    ((finiteLabels_iff_toPMF hf).1 hfin), ← ent_eq_finiteEntropy' hf] at h
  rw [Finset.sum_congr rfl fun i _ => mul_ent_eq_mixLaw hw0 hw1 hθs hf i (hq i)]
  exact h

/-- Almost convexity of entropy, the right inequality of: for
`θ = ∑ w i θ i`, `H(θ, 𝒟) ≤ ∑ w i H(θ i, 𝒟) + H(w)`; the vendored `finiteEntropy_bind_le`. -/
theorem ent_le_sum_ent_add (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hθ : θ = ∑ i, ENNReal.ofReal (w i) • θs i) {f : X → M} (hf : Measurable f)
    (hfin : FiniteLabels θ f) :
    ent θ f ≤ ∑ i, w i * ent (θs i) f + ∑ i, Real.negMulLog (w i) :=
  ent_le_sum_ent_add_of_ne_zero hw0 hw1 (fun _ _ => inferInstance) hθ hf hfin

omit [MeasurableSpace M] [MeasurableSingletonClass M] [Countable M] in
/-- Concavity of conditional entropy:
`∑ w i H(θ i, 𝒟 ∣ ℰ) ≤ H(θ, 𝒟 ∣ ℰ)`; the vendored `average_conditionalEntropy_le_bind`. -/
theorem sum_cent_le_cent [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L]
    [MeasurableSpace L'] [MeasurableSingletonClass L'] [Countable L'] (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hθ : θ = ∑ i, ENNReal.ofReal (w i) • θs i) {f : X → L} {g : X → L'}
    (hf : Measurable f) (hg : Measurable g) (hfinf : FiniteLabels θ f)
    (hfing : FiniteLabels θ g) : ∑ i, w i * cent (θs i) f g ≤ cent θ f g := by
  have hθs : ∀ i, w i ≠ 0 → IsProbabilityMeasure (θs i) := fun _ _ => inferInstance
  have hF := hf.prodMk hg
  have hfin := hfinf.pair hfing
  have hq := mixLaw_support_finite hw0 hθs hθ hF hfin
  have h := average_conditionalEntropy_le_bind (weightPMF hw0 hw1)
    (mixLaw θ θs w hθs fun x => (f x, g x)) hq Prod.snd
  rw [conditionalEntropy_congr (bind_mixLaw hw0 hw1 hθs hθ hF) _
    ((finiteLabels_iff_toPMF hF).1 hfin), ← cent_eq_conditionalEntropy hf hg] at h
  rw [Finset.sum_congr rfl fun i _ => mul_cent_eq_mixLaw hw0 hw1 hθs hf hg i (hq i)]
  exact h

omit [MeasurableSpace M] [MeasurableSingletonClass M] [Countable M] in
/-- Almost convexity of conditional entropy:
`H(θ, 𝒟 ∣ ℰ) ≤ ∑ w i H(θ i, 𝒟 ∣ ℰ) + H(w)`; the vendored `conditionalEntropy_bind_le`. -/
theorem cent_le_sum_cent_add [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L]
    [MeasurableSpace L'] [MeasurableSingletonClass L'] [Countable L'] (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hθ : θ = ∑ i, ENNReal.ofReal (w i) • θs i) {f : X → L} {g : X → L'}
    (hf : Measurable f) (hg : Measurable g) (hfinf : FiniteLabels θ f)
    (hfing : FiniteLabels θ g) :
    cent θ f g ≤ ∑ i, w i * cent (θs i) f g + ∑ i, Real.negMulLog (w i) := by
  have hθs : ∀ i, w i ≠ 0 → IsProbabilityMeasure (θs i) := fun _ _ => inferInstance
  have hF := hf.prodMk hg
  have hfin := hfinf.pair hfing
  have hq := mixLaw_support_finite hw0 hθs hθ hF hfin
  have h := conditionalEntropy_bind_le (weightPMF hw0 hw1)
    (mixLaw θ θs w hθs fun x => (f x, g x)) hq Prod.snd
  rw [finiteEntropy_weightPMF, conditionalEntropy_congr (bind_mixLaw hw0 hw1 hθs hθ hF) _
    ((finiteLabels_iff_toPMF hF).1 hfin), ← cent_eq_conditionalEntropy hf hg] at h
  rw [Finset.sum_congr rfl fun i _ => mul_cent_eq_mixLaw hw0 hw1 hθs hf hg i (hq i)]
  linarith

omit [∀ i, IsProbabilityMeasure (θs i)] in
/-- Almost convexity for the split of `θ` along a measurable set `B` and its complement,
`θ = θ(B) θ_B + θ(Bᶜ) θ_{Bᶜ}`, with `H(θ(B), θ(Bᶜ)) ≤ log 2`. A null piece is the zero
measure and contributes nothing. -/
theorem ent_le_two_pieces {f : X → M} (hf : Measurable f) (hfin : FiniteLabels θ f)
    {B : Set X} (hB : MeasurableSet B) :
    ent θ f ≤ θ.real B * ent (θ[|B]) f + θ.real Bᶜ * ent (θ[|Bᶜ]) f + Real.log 2 := by
  let w : Fin 2 → ℝ := ![θ.real B, θ.real Bᶜ]
  let θs : Fin 2 → Measure X := ![θ[|B], θ[|Bᶜ]]
  have hw0 : ∀ i, 0 ≤ w i := by
    intro i
    fin_cases i <;> simp [w, measureReal_nonneg]
  have hw1 : ∑ i, w i = 1 := by
    simp [w, Fin.sum_univ_two, measureReal_add_measureReal_compl hB, probReal_univ]
  have hθs : ∀ i, w i ≠ 0 → IsProbabilityMeasure (θs i) := by
    intro i hi
    fin_cases i
    · refine cond_isProbabilityMeasure fun h => hi ?_
      simp [w, measureReal_def, h]
    · refine cond_isProbabilityMeasure fun h => hi ?_
      simp [w, measureReal_def, h]
  have hθ : θ = ∑ i, ENNReal.ofReal (w i) • θs i := by
    ext A hA
    rw [Fin.sum_univ_two, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    simp only [w, θs, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
    rw [ofReal_measureReal, ofReal_measureReal, mul_comm (θ B), mul_comm (θ Bᶜ),
      cond_add_cond_compl_eq hB]
  have h := ent_le_sum_ent_add_of_ne_zero hw0 hw1 hθs hθ hf hfin
  have h2 := sum_negMulLog_le_log_card hw0 hw1
  simp only [Fin.sum_univ_two, Fintype.card_fin, Nat.cast_ofNat] at h h2
  simp only [w, θs, Matrix.cons_val_zero, Matrix.cons_val_one] at h h2
  linarith

end Mixture

end FractalGeometry.Rapaport.Analytic
