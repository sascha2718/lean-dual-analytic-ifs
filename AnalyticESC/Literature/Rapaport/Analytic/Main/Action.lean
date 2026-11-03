module

public import AnalyticESC.Literature.Rapaport.Analytic.Main.Statements
public import AnalyticESC.Literature.Rapaport.Analytic.Main.EntropyTools

@[expose] public section

/-!
# The action of measures on words on the self-conformal measure

For a measure `ξ` on `(Fin N)^ℕ` and a length `m`, the measure
`wordAct φ θ ξ m = ∑_{|w| = m} ξ[w] φ_w θ` on `ℝ`. For `θ = μ` it is Rapaport's
`(Π_m ξ).μ` of Section 4 of A. Rapaport, *Dimension of self-conformal measures associated to an
exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2: the image of `ξ × μ` under
`(η, y) ↦ φ_{η|_m}(y)`.

## Main declarations

* `pre m ω = ω|_m`, the prefix labelling, with `pre m ⁻¹' {w} = [w]`.
* `wordAct φ θ ξ m` and its linearity in `ξ` (`wordAct_add`, `wordAct_smul`, `wordAct_sum`).
* `wordAct_compl_I`, `isProbabilityMeasure_wordAct`: `wordAct` is a probability measure on `I`.
* `selfConformal_eq_wordAct`: `μ = (Π_m β).μ`, that is `μ = ∑_{|w| = m} β[w] φ_w μ`.
* `selfConformal_eq_lintegral_wordAct_fibre`: `μ = ∫ (Π_m β_x).μ dμ(x)`.
* `measurable_wordAct_fibre`: measurability of `x ↦ (Π_m β_x).μ (s)`.
* `wordAct_append_of_shift`: for `ζ` carried by `σ^{-n}[u]`,
  `(Π_{n+n'} ζ).μ = ∑_{|v| = n} ζ[v] φ_v (φ_u μ)`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Main.Action`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic.SectionFour

open MeasureTheory ProbabilityTheory Set Filter Topology FractalGeometry.SelfConformal
open FractalGeometry.Rapaport.Analytic
open scoped ENNReal

variable {N : ℕ} {φ : Fin N → ℝ → ℝ}

/-- The defining equation of `wordMap`. -/
theorem wordMap_def {n : ℕ} (u : Fin n → Fin N) :
    wordMap φ u = AnalyticESC.realComp φ (List.ofFn u) := rfl

/-! ### Prefixes and cylinders -/

/-- The prefix `ω|_m`, as a word `Fin m → Fin N`. -/
def pre (m : ℕ) (ω : ℕ → Fin N) : Fin m → Fin N := fun k => ω k

/-- The prefix map is measurable. -/
theorem measurable_pre (m : ℕ) : Measurable (pre (N := N) m) :=
  measurable_pi_iff.2 fun k => measurable_pi_apply (k : ℕ)

/-- The fibre of the prefix labelling at `w` is the cylinder `[w]`. -/
theorem pre_preimage_singleton {m : ℕ} (w : Fin m → Fin N) : pre m ⁻¹' {w} = cylinder w := by
  ext ω
  simp only [mem_preimage, mem_singleton_iff, SelfConformal.cylinder, mem_ofPred_eq, pre,
    funext_iff]

/-- `ω` lies in the cylinder of its own prefix. -/
theorem mem_cylinder_pre (m : ℕ) (ω : ℕ → Fin N) : ω ∈ cylinder (pre m ω) := fun _ => rfl

/-- The cylinders of length `m` partition every measurable set. -/
theorem sum_measure_cylinder_inter (ξ : Measure (ℕ → Fin N)) (m : ℕ) {A : Set (ℕ → Fin N)}
    (hA : MeasurableSet A) : ∑ w : Fin m → Fin N, ξ (A ∩ cylinder w) = ξ A := by
  have h := sum_measure_inter_fiber (θ := ξ) (measurable_pre m) Finset.univ
    (fun b _ => Finset.mem_univ b) hA
  simpa only [pre_preimage_singleton] using h

/-- The cylinders of length `m` have total mass `ξ(univ)`. -/
theorem sum_measure_cylinder (ξ : Measure (ℕ → Fin N)) (m : ℕ) :
    ∑ w : Fin m → Fin N, ξ (cylinder w) = ξ univ := by
  simpa using sum_measure_cylinder_inter ξ m MeasurableSet.univ

/-- The cylinder entropy is the entropy of the prefix labelling. -/
theorem cylEntropy_eq_ent (ξ : Measure (ℕ → Fin N)) (m : ℕ) :
    cylEntropy ξ m = ent ξ (pre m) := by
  rw [cylEntropy, ent, tsum_fintype]
  simp only [pre_preimage_singleton]

/-! ### The action -/

/-- The measure `(Π_m ξ).θ = ∑_{|w| = m} ξ[w] φ_w θ` on `ℝ`. -/
noncomputable def wordAct (φ : Fin N → ℝ → ℝ) (θ : Measure ℝ) (ξ : Measure (ℕ → Fin N))
    (m : ℕ) : Measure ℝ :=
  ∑ w : Fin m → Fin N, ξ (cylinder w) • θ.map (wordMap φ w)

/-- The mass of a set under `(Π_m ξ).θ`. -/
theorem wordAct_apply (θ : Measure ℝ) (ξ : Measure (ℕ → Fin N)) (m : ℕ) (s : Set ℝ) :
    wordAct φ θ ξ m s = ∑ w : Fin m → Fin N, ξ (cylinder w) * θ.map (wordMap φ w) s := by
  simp [wordAct]

/-- `(Π_m ξ).θ` is additive in `ξ`. -/
theorem wordAct_add (θ : Measure ℝ) (ξ₁ ξ₂ : Measure (ℕ → Fin N)) (m : ℕ) :
    wordAct φ θ (ξ₁ + ξ₂) m = wordAct φ θ ξ₁ m + wordAct φ θ ξ₂ m := by
  simp only [wordAct, Measure.coe_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- `(Π_m ξ).θ` is homogeneous in `ξ`. -/
theorem wordAct_smul (θ : Measure ℝ) (c : ℝ≥0∞) (ξ : Measure (ℕ → Fin N)) (m : ℕ) :
    wordAct φ θ (c • ξ) m = c • wordAct φ θ ξ m := by
  simp only [wordAct, Measure.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]

/-- `(Π_m 0).θ = 0`. -/
theorem wordAct_zero (θ : Measure ℝ) (m : ℕ) : wordAct φ θ (0 : Measure (ℕ → Fin N)) m = 0 := by
  simp [wordAct]

/-- `(Π_m ξ).θ` is linear in `ξ` for finite combinations. -/
theorem wordAct_sum {ι : Type*} (s : Finset ι) (θ : Measure ℝ) (c : ι → ℝ≥0∞)
    (ξ : ι → Measure (ℕ → Fin N)) (m : ℕ) :
    wordAct φ θ (∑ i ∈ s, c i • ξ i) m = ∑ i ∈ s, c i • wordAct φ θ (ξ i) m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wordAct_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, wordAct_add, wordAct_smul, ih]

variable (hφ : AnalyticESC.RapaportHyp φ)
include hφ

/-- The word maps are almost everywhere measurable for a measure carried by `I`. -/
theorem aemeasurable_wordMap {θ : Measure ℝ} (hθ : θ AnalyticESC.Iᶜ = 0) {m : ℕ}
    (w : Fin m → Fin N) : AEMeasurable (wordMap φ w) θ :=
  aemeasurable_realComp hφ _ hθ

/-- `φ_w θ` is carried by `I` when `θ` is. -/
theorem map_wordMap_compl_I {θ : Measure ℝ} (hθ : θ AnalyticESC.Iᶜ = 0) {m : ℕ}
    (w : Fin m → Fin N) : θ.map (wordMap φ w) AnalyticESC.Iᶜ = 0 := by
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_wordMap hφ hθ w) measurableSet_Icc.compl]
  refine measure_mono_null (fun y hy => ?_) hθ
  intro hyI
  exact hy (mapsTo_realComp hφ _ hyI)

/-- `(Π_m ξ).θ` is carried by `I` when `θ` is. -/
theorem wordAct_compl_I {θ : Measure ℝ} (hθ : θ AnalyticESC.Iᶜ = 0) (ξ : Measure (ℕ → Fin N))
    (m : ℕ) : wordAct φ θ ξ m AnalyticESC.Iᶜ = 0 := by
  rw [wordAct_apply]
  simp [map_wordMap_compl_I hφ hθ]

omit hφ in
/-- `(Π_m ξ).θ` is a probability measure. -/
theorem isProbabilityMeasure_wordAct {θ : Measure ℝ} [IsProbabilityMeasure θ]
    (ξ : Measure (ℕ → Fin N)) [IsProbabilityMeasure ξ] (m : ℕ) :
    IsProbabilityMeasure (wordAct φ θ ξ m) := by
  refine ⟨?_⟩
  rw [wordAct_apply]
  have : ∀ w : Fin m → Fin N, θ.map (wordMap φ w) univ = 1 := fun w => by
    exact measure_univ
  simp only [this, mul_one]
  rw [sum_measure_cylinder, measure_univ]

omit hφ in
/-- `x ↦ (Π_m β_x).θ (s)` is measurable. -/
theorem measurable_wordAct_fibre [NeZero N] {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p)
    (θ : Measure ℝ) (m : ℕ) (s : Set ℝ) :
    Measurable fun x => wordAct φ θ (fibre φ p hp x) m s := by
  simp only [wordAct_apply]
  refine Finset.measurable_sum _ fun w _ => ?_
  exact ((graphMeasure φ p hp).condKernel.measurable_coe (measurableSet_cylinder w)).mul_const _

/-- `μ = ∑_{|w| = m} β[w] φ_w μ`, Rapaport's (2.1) iterated `m` times. -/
theorem selfConformal_eq_wordAct {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p) (m : ℕ) :
    selfConformal φ p hp = wordAct φ (selfConformal φ p hp) (bernoulli p hp) m := by
  ext s hs
  rw [wordAct_apply, selfConformal_apply φ hp hs,
    ← sum_measure_cylinder_inter _ m (measurable_coding φ hs)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hcont : Continuous fun ω => wordMap φ w (coding φ ω) :=
    continuous_realComp_coding hφ (List.ofFn w)
  have hset : coding φ ⁻¹' s ∩ cylinder w =
      cylinder w ∩ shift^[m] ⁻¹' ((fun ω => wordMap φ w (coding φ ω)) ⁻¹' s) := by
    ext ω
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by rwa [coding_eq_of_mem_cylinder hφ h2] at h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [coding_eq_of_mem_cylinder hφ h1], h1⟩
  rw [hset, bernoulli_cylinder_inter_shift_iterate hp w (hcont.measurable hs),
    ← bernoulli_cylinder hp w, wordMap, map_realComp_selfConformal hφ hp,
    Measure.map_apply (continuous_realComp_coding hφ (List.ofFn w)).measurable hs]

/-- `μ = ∫ (Π_m β_x).μ dμ(x)`: the disintegration `β = ∫ β_x dμ(x)` pushed to `ℝ`. -/
theorem selfConformal_eq_lintegral_wordAct_fibre [NeZero N] {p : Fin N → ℝ}
    (hp : AnalyticESC.IsProbVec p) (m : ℕ) (s : Set ℝ) :
    selfConformal φ p hp s =
      ∫⁻ x, wordAct φ (selfConformal φ p hp) (fibre φ p hp x) m s ∂selfConformal φ p hp := by
  have hm : ∀ w : Fin m → Fin N, Measurable fun x => fibre φ p hp x (cylinder w) := fun w =>
    (graphMeasure φ p hp).condKernel.measurable_coe (measurableSet_cylinder w)
  conv_lhs => rw [selfConformal_eq_wordAct hφ hp m]
  simp only [wordAct_apply]
  rw [lintegral_finsetSum _ fun w _ => (hm w).mul_const _]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [lintegral_mul_const _ (hm w), bernoulli_eq_lintegral_fibre φ hp (measurableSet_cylinder w)]

/-! ### Concatenation of words -/

omit hφ in
/-- `φ_{vu} = φ_v ∘ φ_u`. -/
theorem wordMap_append {n n' : ℕ} (v : Fin n → Fin N) (u : Fin n' → Fin N) :
    wordMap φ (Fin.append v u) = wordMap φ v ∘ wordMap φ u := by
  rw [wordMap, List.ofFn_fin_append, realComp_append]
  rfl

omit hφ in
/-- `[vu] = [v] ∩ σ^{-n} [u]`. -/
theorem cylinder_append {n n' : ℕ} (v : Fin n → Fin N) (u : Fin n' → Fin N) :
    cylinder (Fin.append v u) = cylinder v ∩ shift^[n] ⁻¹' cylinder u := by
  ext ω
  simp only [SelfConformal.cylinder, mem_ofPred_eq, mem_inter_iff, mem_preimage,
    shift_iterate_apply]
  constructor
  · intro h
    refine ⟨fun k => ?_, fun k => ?_⟩
    · have := h (Fin.castAdd n' k)
      simpa using this
    · have := h (Fin.natAdd n k)
      simpa [add_comm] using this
  · intro h k
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · simpa using h.1 k
    · simpa [add_comm] using h.2 k

/-- For `ζ` carried by `σ^{-n}[u]`, `(Π_{n+n'} ζ).θ = ∑_{|v| = n} ζ[v] φ_v (φ_u θ)`. -/
theorem wordAct_append_of_shift {θ : Measure ℝ} (hθ : θ AnalyticESC.Iᶜ = 0) {n n' : ℕ}
    (u : Fin n' → Fin N) (ζ : Measure (ℕ → Fin N)) (hζ : ζ (shift^[n] ⁻¹' cylinder u)ᶜ = 0) :
    wordAct φ θ ζ (n + n') =
      ∑ v : Fin n → Fin N, ζ (cylinder v) • (θ.map (wordMap φ u)).map (wordMap φ v) := by
  rw [wordAct, ← (Fin.appendEquiv n n').sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_eq_single u]
  · have hap : (Fin.appendEquiv n n') (v, u) = Fin.append v u := rfl
    rw [hap, cylinder_append, wordMap_append, ← AEMeasurable.map_map_of_aemeasurable
      (aemeasurable_wordMap hφ (map_wordMap_compl_I hφ hθ u) v) (aemeasurable_wordMap hφ hθ u)]
    congr 1
    exact measure_inter_conull hζ
  · intro u' _ hu'
    have hap : (Fin.appendEquiv n n') (v, u') = Fin.append v u' := rfl
    rw [hap, cylinder_append]
    have : ζ (cylinder v ∩ shift^[n] ⁻¹' cylinder u') = 0 := by
      refine measure_mono_null (fun ω hω => ?_) hζ
      intro h'
      exact Set.disjoint_left.1 (disjoint_cylinder hu') hω.2 h'
    simp [this]
  · simp

end FractalGeometry.Rapaport.Analytic.SectionFour
