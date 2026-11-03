module

public import AnalyticESC.Literature.Rapaport.Analytic.Setup
public import AnalyticESC.Literature.Rapaport.Analytic.ProductEntropy
public import AnalyticESC.Literature.Rapaport.Analytic.PolyBounds

@[expose] public section

/-!
# Linearisation of the action of polynomials

Lemmas 3.8 and 3.9 of A. Rapaport, *Dimension of self-conformal measures associated to an
exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2, and the two elementary entropy
bounds used with them in Section 3.4 (entropy of a convolution and of a rescaling).

## Main declarations

* `sum_pairAvg_le`: Lemma 3.8, the multiscale lower bound for `ν.θ` through components.
* `linearisation`: Lemma 3.9 together with the rescaling (3.11): at small scales, `ν.θ` is close
  in entropy to `(S_{p'(x)⁻¹} ν).x ∗ θ`.
* `dyadicEntropy_le_conv`: `H(θ, 𝒟_n) ≤ H(ξ ∗ θ, 𝒟_n) + O(1)`.
* `dyadicEntropy_le_map_mul`: `H(ξ, 𝒟_n) ≤ H(c ξ, 𝒟_n) + O(1 + log |c|⁻¹)`.
* `actPoint_map_scale`, `ae_actPoint_mem_Icc`: the measures `(S_c ν).x` and their supports.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Linearisation`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic

open MeasureTheory ProbabilityTheory Set Filter Topology FractalGeometry.SelfConformal
open scoped ENNReal MeasureTheory

/-- The scaling `S_c` of `𝒫_k` is measurable. -/
theorem measurable_scale {k : ℕ} (c : ℝ) : Measurable (Poly.scale (k := k) c) :=
  (continuous_const_smul c).measurable

/-- `(S_c ν).x` is the image of `ν.x` under `y ↦ c y`. -/
theorem actPoint_map_scale {k : ℕ} (ρ : Measure (Poly k)) (c x : ℝ) :
    actPoint (ρ.map (Poly.scale c)) x = (actPoint ρ x).map fun y => c * y := by
  rw [actPoint, actPoint, Measure.map_map (Poly.measurable_eval_left x) (measurable_scale c),
    Measure.map_map (measurable_const_mul c) (Poly.measurable_eval_left x)]
  congr 1
  funext q
  simp [Poly.scale]

/-- `ν.x` is carried by `[p(x) - (k+1) r, p(x) + (k+1) r]` when `ν` is carried by the `r`-cube
about `p` and `x ∈ I`. -/
theorem ae_actPoint_mem_Icc {k : ℕ} {ρ : Measure (Poly k)} {p : Poly k} {r : ℝ}
    (hρ : ∀ᵐ q ∂ρ, ∀ j, |q j - p j| ≤ r) {x : ℝ} (hx : x ∈ AnalyticESC.I) :
    ∀ᵐ y ∂(actPoint ρ x), y ∈ Icc (Poly.eval p x - (k + 1) * r) (Poly.eval p x + (k + 1) * r) := by
  rw [actPoint]
  refine (ae_map_iff (Poly.measurable_eval_left x).aemeasurable (by exact measurableSet_Icc)).2 ?_
  filter_upwards [hρ] with q hq
  have h := abs_eval_le (q - p) (B := r) (fun j => by simpa using hq j) (abs_le_one_of_mem_I hx)
  rw [Poly.eval_sub, abs_le] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Lemma 3.8 of Rapaport: for `‖q‖ ≤ R` on the support of `ν` and `θ` carried by `I`,
`H(ν.θ, 𝒟_n) ≥ ∑_{i<n} 𝔼(H(ν_{p,i}.θ_{x,i}, 𝒟_{i+m}) / m) - O_{k,R}(n / m + m)`. -/
theorem sum_pairAvg_le (k : ℕ) (R : ℝ) : ∃ C : ℝ, ∀ ν : Measure (Poly k),
    IsProbabilityMeasure ν → (∀ᵐ q ∂ν, ‖q‖ ≤ R) → ∀ θ : Measure ℝ, IsProbabilityMeasure θ →
    θ AnalyticESC.Iᶜ = 0 → ∀ n m : ℕ, 1 ≤ m →
    ∑ i ∈ Finset.range n, pairAvg ν θ i (fun ρ τ => dyadicEntropy (act ρ τ) (i + m) / m) ≤
      dyadicEntropy (act ν θ) n + C * (n / m + m) := by
  classical
  set A : ℝ := Real.log (2 * ((k + 1) * (1 + k * |R|)) + 2) with hAdef
  have hA0 : 0 ≤ A := by
    have : (0 : ℝ) ≤ (k + 1) * (1 + k * |R|) := by positivity
    exact Real.log_nonneg (by linarith)
  have hl2 := Real.log_pos one_lt_two
  refine ⟨max (Real.log 6) A / Real.log 2, ?_⟩
  intro ν hν hνR θ hθ hθI n m hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set F : Poly k × ℝ → ℝ := fun z => Poly.eval z.1 z.2 with hFdef
  have hFm : Measurable F := Poly.measurable_eval_uncurry
  have hθIae : ∀ᵐ x ∂θ, x ∈ AnalyticESC.I := ae_mem_of_compl_null hθI
  have hSae := ae_prod_of_ae hνR hθIae
  set S : Set (Poly k × ℝ) := {z | ‖z.1‖ ≤ R ∧ z.2 ∈ AnalyticESC.I} with hSdef
  have hSm : MeasurableSet S := by
    rw [hSdef, Set.ofPred_and]
    exact (measurableSet_le (by fun_prop) measurable_const).inter
      (measurable_snd measurableSet_Icc)
  have hSθ : (ν.prod θ) Sᶜ = 0 := ae_iff.1 hSae
  have hFb : ∀ᵐ z ∂(ν.prod θ), F z ∈ Icc (-((k + 1) * |R|)) ((k + 1) * |R|) := by
    filter_upwards [hSae] with z hz
    exact abs_le.1 (abs_eval_le z.1 (fun j => (abs_apply_le_norm z.1 j).trans
      (hz.1.trans (le_abs_self R))) (abs_le_one_of_mem_I hz.2))
  have hr := refining_cellIdx_comp hFm hFb
  have hms := hr.abs_sum_cent_sub_le n m
  have hfν : ∀ i, FiniteLabels ν (cellIdxVec i) := fun i =>
    finiteLabels_cellIdxVec_comp_of_norm_le (F := id) i hνR
  have hfθ : ∀ i, FiniteLabels θ (cellIdx i) := fun i =>
    finiteLabels_cellIdx_comp (F := id) i hθIae
  -- the component labelling `g_i = (𝒟_i^{𝒫_k}, 𝒟_i)`
  have hgm : ∀ i, Measurable fun z : Poly k × ℝ => (cellIdxVec i z.1, cellIdx i z.2) :=
    fun i => ((measurable_cellIdxVec i).comp measurable_fst).prodMk
      ((measurable_cellIdx i).comp measurable_snd)
  have hgf : ∀ i, FiniteLabels (ν.prod θ) fun z : Poly k × ℝ => (cellIdxVec i z.1, cellIdx i z.2) :=
    fun i => (hfν i).prodLabel (hfθ i)
  -- the level bound `H(f_{i+m} ∣ g_i) ≤ H(f_{i+m} ∣ f_i) + A`
  have hlev : ∀ i, cent (ν.prod θ) (cellIdx (i + m) ∘ F)
      (fun z : Poly k × ℝ => (cellIdxVec i z.1, cellIdx i z.2)) ≤
      cent (ν.prod θ) (cellIdx (i + m) ∘ F) (cellIdx i ∘ F) + A := by
    intro i
    have h1 := cent_le_of_factor (θ := ν.prod θ) (f := cellIdx (i + m) ∘ F)
      (f' := fun z => ((cellIdx i ∘ F) z, (cellIdx (i + m) ∘ F) z))
      (g := fun z : Poly k × ℝ => (cellIdxVec i z.1, cellIdx i z.2))
      ((hr.meas i).prodMk (hr.meas (i + m))) (hgm i) ((hr.fin i).pair (hr.fin (i + m)))
      (hgf i) Prod.snd rfl
    have h2 := cent_pair_left (θ := ν.prod θ) (cellIdx i ∘ F) (cellIdx (i + m) ∘ F)
      (fun z : Poly k × ℝ => (cellIdxVec i z.1, cellIdx i z.2))
    have h3 := cent_pair_right_le (θ := ν.prod θ) (f := cellIdx (i + m) ∘ F)
      (g := cellIdx i ∘ F) (h := fun z : Poly k × ℝ => (cellIdxVec i z.1, cellIdx i z.2))
      (hr.meas _) (hr.meas _) (hgm i) (hr.fin _) (hr.fin _) (hgf i)
    have h4 := cent_cellIdx_comp_le (θ := ν.prod θ) hFm (hgm i) i (hr.fin i) (hgf i) hSm hSθ
      (r := (k + 1) * (1 + k * |R|) / 2 ^ i) (by positivity) fun z hz z' hz' hzz => by
        simp only [Prod.mk.injEq] at hzz
        have hc1 : ∀ j, |(z.1 - z'.1) j| ≤ 1 / 2 ^ i := fun j => by
          have := abs_sub_lt_of_cellIdx_eq (congrFun hzz.1 j)
          simpa using this.le
        have e1 := abs_eval_le (z.1 - z'.1) hc1 (abs_le_one_of_mem_I hz.2)
        have e2 := abs_eval_sub_le z'.1 (B := |R|) (fun j => (abs_apply_le_norm z'.1 j).trans
          (hz'.1.trans (le_abs_self R))) (abs_le_one_of_mem_I hz'.2)
          (abs_le_one_of_mem_I hz.2)
        have e3 := (abs_sub_lt_of_cellIdx_eq hzz.2).le
        rw [Poly.eval_sub] at e1
        have e4 : |F z - F z'| ≤ |Poly.eval z.1 z.2 - Poly.eval z'.1 z.2| +
            |Poly.eval z'.1 z.2 - Poly.eval z'.1 z'.2| := abs_sub_le _ _ _
        have hk : (0 : ℝ) ≤ (k + 1) * (k * |R|) := by positivity
        calc |F z - F z'| ≤ |Poly.eval z.1 z.2 - Poly.eval z'.1 z.2| +
              |Poly.eval z'.1 z.2 - Poly.eval z'.1 z'.2| := e4
          _ ≤ (k + 1) * (1 / 2 ^ i) + (k + 1) * (k * |R|) * (1 / 2 ^ i) := by
              gcongr
              exact e2.trans (mul_le_mul_of_nonneg_left e3 hk)
          _ = (k + 1) * (1 + k * |R|) / 2 ^ i := by ring
    have he : (2 : ℝ) ^ i * (2 * ((k + 1) * (1 + k * |R|) / 2 ^ i)) + 2 =
        2 * ((k + 1) * (1 + k * |R|)) + 2 := by field_simp
    rw [he] at h4
    linarith
  -- the component averages as conditional entropies
  have hpa : ∀ i, pairAvg ν θ i (fun ρ τ => dyadicEntropy (act ρ τ) (i + m) / m) =
      cent (ν.prod θ) (cellIdx (i + m) ∘ F)
        (fun z : Poly k × ℝ => (cellIdxVec i z.1, cellIdx i z.2)) / (Real.log 2 * m) := by
    intro i
    rw [cent_eq_cavg (hr.meas _) (hgm i) (hr.fin _) (hgf i),
      cavg_prod (measurable_cellIdxVec i) (measurable_cellIdx i) (hfν i) (hfθ i), pairAvg]
    have e1 : (fun ρ => cavg θ (cellIdx i) fun τ => dyadicEntropy (act ρ τ) (i + m) / m) =
        fun ρ => (Real.log 2 * m)⁻¹ *
          cavg θ (cellIdx i) fun τ => ent (ρ.prod τ) (cellIdx (i + m) ∘ F) := by
      funext ρ
      rw [← cavg_const_mul (hfθ i)]
      congr 1
      funext τ
      rw [dyadicEntropy_eq_ent, act, ent_map hFm (measurable_cellIdx _)]
      field_simp
    rw [e1, cavg_const_mul (hfν i), div_eq_inv_mul]
  -- summing over the levels
  have hsum : ∑ i ∈ Finset.range n, pairAvg ν θ i
      (fun ρ τ => dyadicEntropy (act ρ τ) (i + m) / m) ≤
      (∑ i ∈ Finset.range n, cent (ν.prod θ) (cellIdx (i + m) ∘ F) (cellIdx i ∘ F) + n * A) /
        (Real.log 2 * m) := by
    simp_rw [hpa]
    rw [← Finset.sum_div]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    calc ∑ i ∈ Finset.range n, cent (ν.prod θ) (cellIdx (i + m) ∘ F)
          (fun z : Poly k × ℝ => (cellIdxVec i z.1, cellIdx i z.2))
        ≤ ∑ i ∈ Finset.range n, (cent (ν.prod θ) (cellIdx (i + m) ∘ F) (cellIdx i ∘ F) + A) :=
          Finset.sum_le_sum fun i _ => hlev i
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have hent0 : 0 ≤ ent (ν.prod θ) (cellIdx 0 ∘ F) := ent_nonneg _
  have hentn : ent (ν.prod θ) (cellIdx n ∘ F) = Real.log 2 * dyadicEntropy (act ν θ) n := by
    rw [dyadicEntropy_eq_ent, act, ent_map hFm (measurable_cellIdx _)]
    field_simp
  rw [abs_le] at hms
  have hmax1 : Real.log 6 ≤ max (Real.log 6) A := le_max_left _ _
  have hmax2 : A ≤ max (Real.log 6) A := le_max_right _ _
  refine hsum.trans ?_
  rw [div_le_iff₀ (by positivity)]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have e : (dyadicEntropy (act ν θ) n + max (Real.log 6) A / Real.log 2 * (n / m + m)) *
      (Real.log 2 * m) = Real.log 2 * dyadicEntropy (act ν θ) n * m +
        max (Real.log 6) A * n + max (Real.log 6) A * m * m := by
    field_simp
    ring
  rw [e]
  have h6 : m * m * Real.log 6 ≤ max (Real.log 6) A * m * m := by
    have := mul_le_mul_of_nonneg_left hmax1 (by positivity : (0 : ℝ) ≤ m * m)
    linarith
  have hA' : n * A ≤ max (Real.log 6) A * n := by
    have := mul_le_mul_of_nonneg_left hmax2 hn0
    linarith
  have hent : m * (ent (ν.prod θ) (cellIdx n ∘ F) - ent (ν.prod θ) (cellIdx 0 ∘ F)) ≤
      Real.log 2 * dyadicEntropy (act ν θ) n * m := by
    rw [hentn]
    nlinarith
  linarith [hms.2]

/-- Lemma 3.9 of Rapaport with the rescaling (3.11): if `ν` is carried by the `2^{-i}`-cube
about `p` and `θ` by `[x - 2^{-i}, x + 2^{-i}] ∩ I`, then at scales `i ≥ m + K` the entropy of
`(S_{p'(x)⁻¹} ν).x ∗ θ` at level `i + m` exceeds that of `ν.θ` by at most a constant. -/
theorem linearisation (k : ℕ) (R ε : ℝ) (hε : 0 < ε) : ∃ K : ℕ, ∃ C : ℝ, ∀ m i : ℕ,
    m + K ≤ i → ∀ ρ : Measure (Poly k), IsProbabilityMeasure ρ → ∀ τ : Measure ℝ,
    IsProbabilityMeasure τ → ∀ p : Poly k, ‖p‖ ≤ R → ∀ x ∈ AnalyticESC.I,
    ε ≤ |Poly.derivEval p x| → (∀ᵐ q ∂ρ, ∀ j, |q j - p j| ≤ 1 / 2 ^ i) →
    (∀ᵐ y ∂τ, y ∈ AnalyticESC.I ∧ |y - x| ≤ 1 / 2 ^ i) →
    dyadicEntropy (actPoint (ρ.map (Poly.scale (Poly.derivEval p x)⁻¹)) x ∗ τ) (i + m) ≤
      dyadicEntropy (act ρ τ) (i + m) + C := by
  classical
  set K₁ : ℝ := (k + 1) * (k * 1) + (k + 1) * (k * (k * |R|)) with hK₁
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt K₁ (by norm_num : (1 : ℝ) < 2)
  refine ⟨K, Real.log (6 * ε⁻¹ + 2) / Real.log 2, ?_⟩
  intro m i hi ρ hρ τ hτ p hp x hx hpx hq hy
  set c : ℝ := (Poly.derivEval p x)⁻¹ with hcdef
  have hpx0 : Poly.derivEval p x ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hpx
    linarith
  have hc : |c| ≤ ε⁻¹ := by
    rw [hcdef, abs_inv]
    exact inv_anti₀ hε hpx
  -- the maps `F (q, y) = q(y)` and `M (q, y) = c q(x) + y`
  set F : Poly k × ℝ → ℝ := fun z => Poly.eval z.1 z.2 with hFdef
  set M : Poly k × ℝ → ℝ := fun z => c * Poly.eval z.1 x + z.2 with hMdef
  have hFm : Measurable F := Poly.measurable_eval_uncurry
  have hMm : Measurable M :=
    ((measurable_const_mul c).comp ((Poly.measurable_eval_left x).comp measurable_fst)).add
      measurable_snd
  have hmeasM : actPoint (ρ.map (Poly.scale c)) x ∗ τ = (ρ.prod τ).map M := by
    have hg : Measurable fun q : Poly k => c * Poly.eval q x :=
      (measurable_const_mul c).comp (Poly.measurable_eval_left x)
    rw [actPoint_map_scale, actPoint, Measure.map_map (measurable_const_mul c)
      (Poly.measurable_eval_left x), Measure.conv]
    have h1 : (ρ.map ((fun y => c * y) ∘ fun q => Poly.eval q x)).prod τ =
        (ρ.prod τ).map (Prod.map ((fun y => c * y) ∘ fun q => Poly.eval q x) id) := by
      conv_lhs => rw [← Measure.map_id (μ := τ)]
      exact Measure.map_prod_map ρ τ hg measurable_id
    rw [h1, Measure.map_map (g := fun z : ℝ × ℝ => z.1 + z.2)
      (f := Prod.map ((fun y => c * y) ∘ fun q => Poly.eval q x) id)
      (measurable_fst.add measurable_snd)
      (((measurable_const_mul c).comp (Poly.measurable_eval_left x)).prodMap measurable_id)]
    rfl
  -- the set of full measure on which the estimates hold
  set S : Set (Poly k × ℝ) := {z | (∀ j, |z.1 j - p j| ≤ 1 / 2 ^ i) ∧
    (z.2 ∈ AnalyticESC.I ∧ |z.2 - x| ≤ 1 / 2 ^ i)} with hSdef
  have hSae : ∀ᵐ z ∂(ρ.prod τ), z ∈ S := ae_prod_of_ae hq hy
  have hSm : MeasurableSet S := by
    rw [hSdef, Set.ofPred_and, Set.ofPred_forall, Set.ofPred_and]
    refine MeasurableSet.inter (MeasurableSet.iInter fun j => measurableSet_le ?_
      measurable_const) (MeasurableSet.inter (measurable_snd measurableSet_Icc)
      (measurableSet_le (by fun_prop) measurable_const))
    exact (((PiLp.continuous_apply 2 _ j).comp continuous_fst).sub continuous_const).abs.measurable
  have hSθ : (ρ.prod τ) Sᶜ = 0 := ae_iff.1 hSae
  -- coefficient and value bounds on `S`
  have h2i : (1 : ℝ) / 2 ^ i ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have hcoef : ∀ z ∈ S, ∀ j, |z.1 j| ≤ |R| + 1 := fun z hz j => by
    have h1 := hz.1 j
    have h2 := (abs_apply_le_norm p j).trans (hp.trans (le_abs_self R))
    calc |z.1 j| = |(z.1 j - p j) + p j| := by ring_nf
      _ ≤ |z.1 j - p j| + |p j| := abs_add_le _ _
      _ ≤ 1 + |R| := by linarith
      _ = |R| + 1 := by ring
  have hFb : ∀ᵐ z ∂(ρ.prod τ), F z ∈ Icc (-((k + 1) * (|R| + 1))) ((k + 1) * (|R| + 1)) := by
    filter_upwards [hSae] with z hz
    exact abs_le.1 (abs_eval_le z.1 (hcoef z hz) (abs_le_one_of_mem_I hz.2.1))
  have hMb : ∀ᵐ z ∂(ρ.prod τ), M z ∈ Icc (-(ε⁻¹ * ((k + 1) * (|R| + 1)) + 1))
      (ε⁻¹ * ((k + 1) * (|R| + 1)) + 1) := by
    filter_upwards [hSae] with z hz
    have h1 := abs_eval_le z.1 (hcoef z hz) (abs_le_one_of_mem_I hx)
    have h2 : |c * Poly.eval z.1 x| ≤ ε⁻¹ * ((k + 1) * (|R| + 1)) := by
      rw [abs_mul]
      exact mul_le_mul hc h1 (abs_nonneg _) (by positivity)
    have h3 := abs_le_one_of_mem_I hz.2.1
    refine abs_le.1 ?_
    calc |M z| ≤ |c * Poly.eval z.1 x| + |z.2| := abs_add_le _ _
      _ ≤ ε⁻¹ * ((k + 1) * (|R| + 1)) + 1 := by linarith
  -- the linearisation error
  have hlin : ∀ z ∈ S, |F z - (Poly.eval z.1 x + Poly.derivEval p x * (z.2 - x))| ≤
      1 / 2 ^ (i + m) := by
    intro z hz
    have hy1 := hz.2.1
    have hyx : |z.2 - x| ≤ 1 / 2 ^ i := hz.2.2
    have e : F z - (Poly.eval z.1 x + Poly.derivEval p x * (z.2 - x)) =
        (Poly.eval (z.1 - p) z.2 - Poly.eval (z.1 - p) x) +
          (Poly.eval p z.2 - Poly.eval p x - Poly.derivEval p x * (z.2 - x)) := by
      simp only [hFdef, Poly.eval_sub]
      ring
    have e1 := abs_eval_sub_le (z.1 - p) (B := 1 / 2 ^ i) (fun j => by simpa using hz.1 j)
      (abs_le_one_of_mem_I hx) (abs_le_one_of_mem_I hy1)
    have e2 := abs_eval_sub_sub_le p (B := |R|)
      (fun j => (abs_apply_le_norm p j).trans (hp.trans (le_abs_self R))) hx hy1
    have hyx2 : |z.2 - x| ^ 2 ≤ (1 / 2 ^ i) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hyx 2
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h3 : |F z - (Poly.eval z.1 x + Poly.derivEval p x * (z.2 - x))| ≤
        K₁ * (1 / 2 ^ i) ^ 2 := by
      rw [e]
      refine (abs_add_le _ _).trans ?_
      have e1' : |Poly.eval (z.1 - p) z.2 - Poly.eval (z.1 - p) x| ≤
          (k + 1) * (k * 1) * (1 / 2 ^ i) ^ 2 := by
        calc _ ≤ (k + 1) * (k * (1 / 2 ^ i)) * |z.2 - x| := e1
          _ ≤ (k + 1) * (k * (1 / 2 ^ i)) * (1 / 2 ^ i) := by gcongr
          _ = (k + 1) * (k * 1) * (1 / 2 ^ i) ^ 2 := by ring
      have e2' : |Poly.eval p z.2 - Poly.eval p x - Poly.derivEval p x * (z.2 - x)| ≤
          (k + 1) * (k * (k * |R|)) * (1 / 2 ^ i) ^ 2 := by
        calc _ ≤ (k + 1) * (k * (k * |R|)) * |z.2 - x| ^ 2 := e2
          _ ≤ (k + 1) * (k * (k * |R|)) * (1 / 2 ^ i) ^ 2 := by gcongr
      rw [hK₁]
      linarith
    refine h3.trans ?_
    have hpow : (2 : ℝ) ^ K * 2 ^ (i + m) ≤ 2 ^ i * 2 ^ i := by
      rw [← pow_add, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hK' : K₁ ≤ 2 ^ K := hK.le
    calc K₁ * (1 / 2 ^ i) ^ 2 ≤ 2 ^ K * (1 / 2 ^ i) ^ 2 := by gcongr
      _ = 2 ^ K / (2 ^ i * 2 ^ i) := by ring
      _ ≤ 1 / 2 ^ (i + m) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
        exact hpow
  -- commensurability of the labellings of `M` and `F`
  have key := ent_cellIdx_comp_le (θ := ρ.prod τ) (F := M) (g := cellIdx (i + m) ∘ F) hMm
    ((measurable_cellIdx _).comp hFm) (i + m) (finiteLabels_cellIdx_comp _ hMb)
    (finiteLabels_cellIdx_comp _ hFb) hSm hSθ (r := 3 * ε⁻¹ / 2 ^ (i + m)) (by positivity)
    fun z hz z' hz' hzz => by
      have h1 := abs_sub_lt_of_cellIdx_eq hzz
      have h2 := hlin z hz
      have h3 := hlin z' hz'
      have hL : |(Poly.eval z.1 x + Poly.derivEval p x * (z.2 - x)) -
          (Poly.eval z'.1 x + Poly.derivEval p x * (z'.2 - x))| ≤ 3 / 2 ^ (i + m) := by
        have e : (Poly.eval z.1 x + Poly.derivEval p x * (z.2 - x)) -
            (Poly.eval z'.1 x + Poly.derivEval p x * (z'.2 - x)) =
            -(F z - (Poly.eval z.1 x + Poly.derivEval p x * (z.2 - x))) + (F z - F z') +
              (F z' - (Poly.eval z'.1 x + Poly.derivEval p x * (z'.2 - x))) := by ring
        rw [e]
        refine (abs_add_three _ _ _).trans ?_
        rw [abs_neg]
        have h1' : |F z - F z'| ≤ 1 / 2 ^ (i + m) := h1.le
        have h3' : (3 : ℝ) / 2 ^ (i + m) =
            1 / 2 ^ (i + m) + 1 / 2 ^ (i + m) + 1 / 2 ^ (i + m) := by ring
        rw [h3']
        linarith
      have he : M z - M z' = c * ((Poly.eval z.1 x + Poly.derivEval p x * (z.2 - x)) -
          (Poly.eval z'.1 x + Poly.derivEval p x * (z'.2 - x))) := by
        simp only [hMdef, hcdef]
        field_simp
        ring
      rw [he, abs_mul]
      calc |c| * _ ≤ ε⁻¹ * (3 / 2 ^ (i + m)) := mul_le_mul hc hL (abs_nonneg _) (by positivity)
        _ = 3 * ε⁻¹ / 2 ^ (i + m) := by ring
  have he : (2 : ℝ) ^ (i + m) * (2 * (3 * ε⁻¹ / 2 ^ (i + m))) + 2 = 6 * ε⁻¹ + 2 := by
    field_simp
    ring
  rw [he] at key
  rw [hmeasM, dyadicEntropy_eq_ent, dyadicEntropy_eq_ent, act, ent_map hMm (measurable_cellIdx _),
    ent_map Poly.measurable_eval_uncurry (measurable_cellIdx _), ← add_div]
  exact div_le_div_of_nonneg_right key (Real.log_pos one_lt_two).le

/-- The entropy of a convolution is at least that of a factor, up to a constant:
`H(θ, 𝒟_n) ≤ H(ξ ∗ θ, 𝒟_n) + 3`. -/
theorem dyadicEntropy_le_conv (ξ τ : Measure ℝ) [IsProbabilityMeasure ξ]
    [IsProbabilityMeasure τ] {a b a' b' : ℝ} (hξ : ∀ᵐ x ∂ξ, x ∈ Icc a b)
    (hτ : ∀ᵐ x ∂τ, x ∈ Icc a' b') (n : ℕ) :
    dyadicEntropy τ n ≤ dyadicEntropy (ξ ∗ τ) n + 3 := by
  classical
  have hadd : Measurable fun z : ℝ × ℝ => z.1 + z.2 := measurable_fst.add measurable_snd
  have hc := measurable_cellIdx n
  have hfξ : FiniteLabels ξ (cellIdx n ∘ id) := finiteLabels_cellIdx_comp n hξ
  have hfτ : FiniteLabels τ (cellIdx n ∘ id) := finiteLabels_cellIdx_comp n hτ
  have hΓ := ae_prod_of_ae hξ hτ
  have hfS : FiniteLabels (ξ.prod τ) (cellIdx n ∘ fun z : ℝ × ℝ => z.1 + z.2) :=
    finiteLabels_cellIdx_comp n (a := a + a') (b := b + b') (by
      filter_upwards [hΓ] with z hz
      exact ⟨by linarith [hz.1.1, hz.2.1], by linarith [hz.1.2, hz.2.2]⟩)
  have hfA : FiniteLabels (ξ.prod τ) (fun z : ℝ × ℝ => cellIdx n z.1) :=
    finiteLabels_cellIdx_comp n (F := Prod.fst) (a := a) (b := b) (by
      filter_upwards [hΓ] with z hz
      exact hz.1)
  have hfY : FiniteLabels (ξ.prod τ) (fun z : ℝ × ℝ => cellIdx n z.2) :=
    finiteLabels_cellIdx_comp n (F := Prod.snd) (a := a') (b := b') (by
      filter_upwards [hΓ] with z hz
      exact hz.2)
  -- `H(ξ × τ, Y ∣ A) = H(τ, 𝒟_n)` by independence
  have hYA : cent (ξ.prod τ) (fun z : ℝ × ℝ => cellIdx n z.2) (fun z => cellIdx n z.1) =
      ent τ (cellIdx n) := by
    unfold cent
    rw [ent_pair_comm, ent_prod hc hc hfξ hfτ, ent_comp_fst hc]
    ring
  -- given the cells of `a + y` and of `a`, the cell of `y` takes at most two values
  have hfib := cent_le_cent_add_log_of_fiber_card (θ := ξ.prod τ)
    (f := fun z : ℝ × ℝ => cellIdx n z.2) (g := cellIdx n ∘ fun z : ℝ × ℝ => z.1 + z.2)
    (h := fun z : ℝ × ℝ => cellIdx n z.1) (hc.comp measurable_snd) (hc.comp hadd)
    (hc.comp measurable_fst) hfY hfS hfA (N := 2) fun sa => by
      refine ⟨Finset.Icc (sa.1 - sa.2 - 1) (sa.1 - sa.2), ?_, fun z hz => ?_⟩
      · simp only [Int.card_Icc]
        omega
      · simp only [Prod.ext_iff, Function.comp_apply] at hz
        have h1 := cellIdx_le n (z.1 + z.2)
        have h2 := lt_cellIdx_add_one n (z.1 + z.2)
        have h3 := cellIdx_le n z.1
        have h4 := lt_cellIdx_add_one n z.1
        rw [hz.1] at h1 h2
        rw [hz.2] at h3 h4
        have h5 := cellIdx_le n z.2
        have h6 := lt_cellIdx_add_one n z.2
        have e : (2 : ℝ) ^ n * (z.1 + z.2) = 2 ^ n * z.1 + 2 ^ n * z.2 := by ring
        rw [e] at h1 h2
        rw [Finset.mem_Icc]
        constructor
        · have : ((sa.1 - sa.2 - 1 : ℤ) : ℝ) < (cellIdx n z.2 : ℝ) + 1 := by
            push_cast
            linarith
          have : sa.1 - sa.2 - 1 < cellIdx n z.2 + 1 := by exact_mod_cast this
          omega
        · have : (cellIdx n z.2 : ℝ) < ((sa.1 - sa.2 : ℤ) : ℝ) + 1 := by
            push_cast
            linarith
          have : cellIdx n z.2 < sa.1 - sa.2 + 1 := by exact_mod_cast this
          omega
  have hle := cent_le_ent (θ := ξ.prod τ) (f := cellIdx n ∘ fun z : ℝ × ℝ => z.1 + z.2)
    (g := fun z : ℝ × ℝ => cellIdx n z.1) (hc.comp hadd) (hc.comp measurable_fst) hfS hfA
  rw [hYA] at hfib
  rw [dyadicEntropy_eq_ent, dyadicEntropy_eq_ent, Measure.conv, ent_map hadd hc]
  have hlog : Real.log 2 ≤ 3 * Real.log 2 := by
    have := Real.log_pos one_lt_two
    linarith
  have hl2 := Real.log_pos one_lt_two
  rw [div_add' _ _ _ hl2.ne', div_le_div_iff_of_pos_right hl2]
  push_cast at hfib
  linarith

/-- Rescaling by `c` with `|c|⁻¹ ≤ A` decreases the dyadic entropy by at most
`log₂ (4 A + 2)`. -/
theorem dyadicEntropy_le_map_mul {ξ : Measure ℝ} [IsProbabilityMeasure ξ] {a b : ℝ}
    (hξ : ∀ᵐ x ∂ξ, x ∈ Icc a b) {c A : ℝ} (hc : c ≠ 0) (hA : |c|⁻¹ ≤ A) (n : ℕ) :
    dyadicEntropy ξ n ≤
      dyadicEntropy (ξ.map fun y => c * y) n + Real.log (4 * A + 2) / Real.log 2 := by
  have hA0 : 0 < A := (inv_pos.2 (abs_pos.2 hc)).trans_le hA
  have hmc : Measurable fun y : ℝ => c * y := measurable_const_mul c
  rw [dyadicEntropy_eq_ent, dyadicEntropy_eq_ent, ent_map hmc (measurable_cellIdx n), ← add_div]
  refine div_le_div_of_nonneg_right ?_ (Real.log_pos one_lt_two).le
  have hfin1 : FiniteLabels ξ (cellIdx n ∘ id) := finiteLabels_cellIdx_comp n hξ
  have hfin2 : FiniteLabels ξ (cellIdx n ∘ fun y => c * y) :=
    finiteLabels_cellIdx_comp n (a := -(|c| * (|a| + |b|))) (b := |c| * (|a| + |b|)) (by
      filter_upwards [hξ] with y hy
      have h1 : |y| ≤ |a| + |b| := abs_le.2 ⟨by linarith [hy.1, neg_abs_le a, abs_nonneg b],
        by linarith [hy.2, le_abs_self b, abs_nonneg a]⟩
      have h2 : |c * y| ≤ |c| * (|a| + |b|) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      exact abs_le.1 h2)
  have key := ent_cellIdx_comp_le (θ := ξ) (F := id) (g := cellIdx n ∘ fun y => c * y)
    measurable_id ((measurable_cellIdx n).comp hmc) n hfin1 hfin2 MeasurableSet.univ (by simp)
    (r := A / 2 ^ n) (by positivity) fun y _ y' _ hyy => by
      have h1 := abs_sub_lt_of_cellIdx_eq hyy
      rw [← mul_sub, abs_mul] at h1
      have hc0 : 0 < |c| := abs_pos.2 hc
      simp only [id]
      calc |y - y'| = |c|⁻¹ * (|c| * |y - y'|) := by field_simp
        _ ≤ A * (1 / 2 ^ n) := mul_le_mul hA h1.le (by positivity) hA0.le
        _ = A / 2 ^ n := by ring
  have he : (2 : ℝ) ^ n * (2 * (A / 2 ^ n)) + 2 = 2 * A + 2 := by field_simp
  rw [he] at key
  calc ent ξ (cellIdx n) = ent ξ (cellIdx n ∘ id) := rfl
    _ ≤ ent ξ (cellIdx n ∘ fun y => c * y) + Real.log (2 * A + 2) := key
    _ ≤ ent ξ (cellIdx n ∘ fun y => c * y) + Real.log (4 * A + 2) := by
        gcongr
        linarith

end FractalGeometry.Rapaport.Analytic
