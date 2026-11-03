module

public import AnalyticESC.Literature.Rapaport.Analytic.Main.Pieces

@[expose] public section

/-!
# Entropy of the pieces: the simple lower bound

Lower bounds for the dyadic entropy of `(Π_{n+n'} ζ).μ` for a measure `ζ` carried by
`σ^{-n}[u]`, used in the proof of Theorem 1.2 of A. Rapaport, *Dimension of self-conformal
measures associated to an exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2,
Section 4: by concavity of entropy and Lemma 2.2 (bi-Lipschitz maps change entropy by a bounded
amount), `H((Π_{n+n'} ζ).μ, 𝒟_{ℓ+L}) ≥ H(μ, 𝒟_ℓ) - O(1)` when the maps `2^L φ_{vu}` have derivative
bounded below (Rapaport's (4.5)).

## Main declarations

* `sum_ent_le_ent_of_ne_zero`: concavity of entropy for finite mixtures with null pieces.
* `wordMapExt`: a continuous extension of `φ_u` from `I` to `ℝ`.
* `ent_map_wordMap_ge`: Lemma 2.2 for `2^L φ_w`.
* `wordAct_append_eq_sum`: `(Π_{n+n'} ζ).θ = ∑_v ζ[v] φ_{vu} θ` for `ζ` carried by `σ^{-n}[u]`.
* `ent_wordAct_ge_of_shift`: the simple lower bound (4.5).
* `map_prod_eq_sum`: the image of `λ × θ` for a measure `λ` on a finite type.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Main.PieceBounds`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic.SectionFour

open MeasureTheory ProbabilityTheory Set Filter Topology FractalGeometry.SelfConformal
open FractalGeometry.Rapaport.Analytic
open scoped ENNReal

variable {N : ℕ} {φ : Fin N → ℝ → ℝ}

/-! ### Concavity with null pieces -/

/-- Concavity of entropy for a finite mixture `θ = ∑ w_i θ_i` in which only the pieces of
positive weight need to be probability measures. -/
theorem sum_ent_le_ent_of_ne_zero {X M : Type*} [MeasurableSpace X] [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] {ι : Type*} [Fintype ι] {θ : Measure X}
    [IsProbabilityMeasure θ] {θs : ι → Measure X} {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hθs : ∀ i, w i ≠ 0 → IsProbabilityMeasure (θs i))
    (hθ : θ = ∑ i, ENNReal.ofReal (w i) • θs i) {f : X → M} (hf : Measurable f)
    (hfin : FiniteLabels θ f) : ∑ i, w i * ent (θs i) f ≤ ent θ f := by
  classical
  set θs' : ι → Measure X := fun i => if w i = 0 then θ else θs i with hθs'
  have hinst : ∀ i, IsProbabilityMeasure (θs' i) := fun i => by
    by_cases h : w i = 0
    · simp only [hθs', h, ite_true]
      infer_instance
    · simp only [hθs', h, ite_false]
      exact hθs i h
  have hθ' : θ = ∑ i, ENNReal.ofReal (w i) • θs' i := by
    rw [hθ]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : w i = 0
    · simp [hθs', h]
    · simp [hθs', h]
  have key := sum_ent_le_ent (θs := θs') hw0 hw1 hθ' hf hfin
  refine le_of_eq_of_le (Finset.sum_congr rfl fun i _ => ?_) key
  by_cases h : w i = 0
  · simp [h]
  · simp [hθs', h]

/-! ### A continuous extension of the word maps -/

/-- The composition of the continuous extensions `φ_i ∘ clampI`: a continuous map on `ℝ` that
agrees with `φ_u` on `I`. -/
noncomputable def wordMapExt (φ : Fin N → ℝ → ℝ) {n : ℕ} (u : Fin n → Fin N) : ℝ → ℝ :=
  AnalyticESC.realComp (extend φ) (List.ofFn u)

/-- The extended word maps are continuous. -/
theorem continuous_wordMapExt (hφ : AnalyticESC.RapaportHyp φ) {n : ℕ} (u : Fin n → Fin N) :
    Continuous (wordMapExt φ u) :=
  continuous_realComp_extend hφ _

/-- The extended word maps agree with `φ_u` on `I`. -/
theorem wordMapExt_eq (hφ : AnalyticESC.RapaportHyp φ) {n : ℕ} (u : Fin n → Fin N) {y : ℝ}
    (hy : y ∈ AnalyticESC.I) : wordMapExt φ u y = wordMap φ u y :=
  realComp_extend hφ _ hy

/-- For a measure carried by `I`, the images under `φ_u` and its extension agree. -/
theorem map_wordMap_eq_map_wordMapExt (hφ : AnalyticESC.RapaportHyp φ) {θ : Measure ℝ}
    (hθ : θ AnalyticESC.Iᶜ = 0) {n : ℕ} (u : Fin n → Fin N) :
    θ.map (wordMap φ u) = θ.map (wordMapExt φ u) := by
  refine Measure.map_congr ?_
  filter_upwards [mem_ae_iff.2 hθ] with y hy
  exact (wordMapExt_eq hφ u hy).symm

/-! ### Lemma 2.2 for the word maps -/

/-- Lemma 2.2 of Rapaport for `2^L φ_w`: if `2^L |φ_w'(0)| ≥ β > 0`, then
`H(φ_w θ, 𝒟_{ℓ+L}) ≥ H(θ, 𝒟_ℓ) - log (2 C / β + 2)` for a probability measure `θ` on `I`, where
`C` is the distortion constant. -/
theorem ent_map_wordMap_ge (hφ : AnalyticESC.RapaportHyp φ) {θ : Measure ℝ}
    [IsProbabilityMeasure θ] (hθ : θ AnalyticESC.Iᶜ = 0) {m : ℕ} (w : Fin m → Fin N)
    (ℓ L : ℕ) {β : ℝ} (hβ : 0 < β) (hw : β ≤ 2 ^ L * |deriv (wordMap φ w) 0|) :
    ent θ (cellIdx ℓ) - Real.log (2 * distConst φ / β + 2) ≤
      ent (θ.map (wordMap φ w)) (cellIdx (ℓ + L)) := by
  have hC := distConst_pos (φ := φ)
  have hd0 : 0 < |deriv (wordMap φ w) 0| := by
    have h2 : (0 : ℝ) < 2 ^ L := by positivity
    by_contra h
    have : |deriv (wordMap φ w) 0| = 0 := le_antisymm (not_lt.1 h) (abs_nonneg _)
    rw [this, mul_zero] at hw
    linarith
  rw [map_wordMap_eq_map_wordMapExt hφ hθ,
    ent_map_of_aemeasurable (continuous_wordMapExt hφ w).aemeasurable]
  have hI : ∀ᵐ y ∂θ, y ∈ AnalyticESC.I := mem_ae_iff.2 hθ
  set r : ℝ := distConst φ / |deriv (wordMap φ w) 0| / 2 ^ (ℓ + L) with hr
  have hr0 : 0 ≤ r := by positivity
  have key := ent_cellIdx_comp_le (θ := θ) (F := id) (g := cellIdx (ℓ + L) ∘ wordMapExt φ w)
    measurable_id ((measurable_cellIdx _).comp (continuous_wordMapExt hφ w).measurable) ℓ
    (finiteLabels_cellIdx_comp (a := 0) (b := 1) ℓ hI)
    (finiteLabels_cellIdx_comp (a := 0) (b := 1) _ (by
      filter_upwards [hI] with y hy
      rw [wordMapExt_eq hφ w hy]
      exact mapsTo_realComp hφ _ hy))
    measurableSet_Icc hθ hr0 (fun y hy y' hy' h => by
      have h1 := abs_sub_lt_of_cellIdx_eq h
      simp only [wordMapExt_eq hφ w hy, wordMapExt_eq hφ w hy'] at h1
      have h2 := distConst_inv_mul_le_abs_realComp_sub hφ (List.ofFn w) hy hy'
        SelfConformal.zero_mem_I
      simp only [id]
      rw [hr, div_div, le_div_iff₀ (by positivity)]
      have h3 : (distConst φ)⁻¹ * |deriv (wordMap φ w) 0| * |y - y'| < 1 / 2 ^ (ℓ + L) :=
        h2.trans_lt h1
      rw [lt_div_iff₀ (by positivity)] at h3
      have h4 : |y - y'| * (|deriv (wordMap φ w) 0| * 2 ^ (ℓ + L)) =
          distConst φ * ((distConst φ)⁻¹ * |deriv (wordMap φ w) 0| * |y - y'| * 2 ^ (ℓ + L)) := by
        field_simp
      rw [h4]
      nlinarith)
  have herr : Real.log (2 ^ ℓ * (2 * r) + 2) ≤ Real.log (2 * distConst φ / β + 2) := by
    refine Real.log_le_log (by positivity) ?_
    have : 2 ^ ℓ * (2 * r) = 2 * distConst φ / (2 ^ L * |deriv (wordMap φ w) 0|) := by
      rw [hr, pow_add]
      field_simp
    rw [this]
    gcongr
  simp only [Function.comp_id] at key
  linarith

/-! ### Measures carried by a shifted cylinder -/

/-- For `ζ` carried by `σ^{-n}[u]`, `(Π_{n+n'} ζ).θ = ∑_{|v| = n} ζ[v] φ_{vu} θ`. -/
theorem wordAct_append_eq_sum {θ : Measure ℝ} {n n' : ℕ} (u : Fin n' → Fin N)
    (ζ : Measure (ℕ → Fin N)) (hζ : ζ (shift^[n] ⁻¹' cylinder u)ᶜ = 0) :
    wordAct φ θ ζ (n + n') =
      ∑ v : Fin n → Fin N, ζ (cylinder v) • θ.map (wordMap φ (Fin.append v u)) := by
  rw [wordAct, ← (Fin.appendEquiv n n').sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_eq_single u]
  · have hap : (Fin.appendEquiv n n') (v, u) = Fin.append v u := rfl
    rw [hap, cylinder_append]
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

/-- The simple lower bound (Rapaport's (4.5)): for a probability measure `ζ` carried by
`σ^{-n}[u]` such that `2^L |φ_{vu}'(0)| ≥ β` whenever `ζ[v] > 0`,
`H((Π_{n+n'} ζ).μ, 𝒟_{ℓ+L}) ≥ H(μ, 𝒟_ℓ) - log (2 C / β + 2)`. -/
theorem ent_wordAct_ge_of_shift (hφ : AnalyticESC.RapaportHyp φ) {θ : Measure ℝ}
    [IsProbabilityMeasure θ] (hθ : θ AnalyticESC.Iᶜ = 0) {n n' : ℕ} (u : Fin n' → Fin N)
    (ζ : Measure (ℕ → Fin N)) [IsProbabilityMeasure ζ]
    (hζ : ζ (shift^[n] ⁻¹' cylinder u)ᶜ = 0) (ℓ L : ℕ) {β : ℝ} (hβ : 0 < β)
    (hw : ∀ v : Fin n → Fin N, ζ (cylinder v) ≠ 0 →
      β ≤ 2 ^ L * |deriv (wordMap φ (Fin.append v u)) 0|) :
    ent θ (cellIdx ℓ) - Real.log (2 * distConst φ / β + 2) ≤
      ent (wordAct φ θ ζ (n + n')) (cellIdx (ℓ + L)) := by
  have hprob := isProbabilityMeasure_wordAct (φ := φ) (θ := θ) ζ (n + n')
  set w : (Fin n → Fin N) → ℝ := fun v => ζ.real (cylinder v) with hw_def
  have hw0 : ∀ v, 0 ≤ w v := fun v => measureReal_nonneg
  have hw1 : ∑ v, w v = 1 := by
    have h := sum_measure_cylinder ζ n
    simp only [hw_def, measureReal_def]
    rw [← ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _), h, measure_univ,
      ENNReal.toReal_one]
  have hmix : wordAct φ θ ζ (n + n') =
      ∑ v, ENNReal.ofReal (w v) • θ.map (wordMap φ (Fin.append v u)) := by
    rw [wordAct_append_eq_sum u ζ hζ]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [hw_def, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hconc := sum_ent_le_ent_of_ne_zero hw0 hw1 (fun v _ => inferInstance) hmix
    (measurable_cellIdx (ℓ + L)) (finiteLabels_cellIdx (wordAct_compl_I hφ hθ ζ _) _)
  refine le_trans ?_ hconc
  calc ent θ (cellIdx ℓ) - Real.log (2 * distConst φ / β + 2)
      = ∑ v, w v * (ent θ (cellIdx ℓ) - Real.log (2 * distConst φ / β + 2)) := by
        rw [← Finset.sum_mul, hw1, one_mul]
    _ ≤ ∑ v, w v * ent (θ.map (wordMap φ (Fin.append v u))) (cellIdx (ℓ + L)) := by
        refine Finset.sum_le_sum fun v _ => ?_
        by_cases hv : ζ (cylinder v) = 0
        · simp [hw_def, measureReal_def, hv]
        · exact mul_le_mul_of_nonneg_left
            (ent_map_wordMap_ge hφ hθ (Fin.append v u) ℓ L hβ (hw v hv)) (hw0 v)

/-! ### Images of product measures with a finite factor -/

/-- For a measure `λ` on a finite type, the image of `λ × θ` under `F` is the mixture
`∑_v λ{v} F(v, ·)θ`. -/
theorem map_prod_eq_sum {V : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] (lam : Measure V) [IsFiniteMeasure lam] (θ : Measure ℝ)
    [SFinite θ] {F : V × ℝ → ℝ} (hF : Measurable F) :
    (lam.prod θ).map F = ∑ v, lam {v} • θ.map (fun y => F (v, y)) := by
  ext s hs
  rw [Measure.map_apply hF hs, Measure.prod_apply (hF hs), lintegral_fintype]
  simp only [Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hm : Measurable fun y => F (v, y) := hF.comp measurable_prodMk_left
  rw [Measure.map_apply hm hs, mul_comm]
  rfl

end FractalGeometry.Rapaport.Analytic.SectionFour
