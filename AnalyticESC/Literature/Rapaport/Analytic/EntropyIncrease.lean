module

public import AnalyticESC.Literature.Rapaport.Analytic.Linearisation
public import AnalyticESC.Literature.Rapaport.Analytic.UniformEntropyDimension
public import AnalyticESC.Literature.Rapaport.Analytic.PolyEntropy
public import AnalyticESC.Literature.Rapaport.Analytic.SelfConformalStructure

@[expose] public section

/-!
# Entropy increase for measures on polynomials

Theorem 3.1 of A. Rapaport, *Dimension of self-conformal measures associated to an exponentially
separated analytic IFS on ℝ*, arXiv:2412.16753v2, with the proof of Section 3.4: if `dim μ < 1`,
then for `ν` on `𝒫_k` with `‖q‖ ≤ ε⁻¹`, `|q'| ≥ ε` on `I` and `H(ν, 𝒟_n) ≥ ε n`, and for
`ψ : I → I` with `ε ≤ |ψ'| ≤ ε⁻¹`, `H(ν.(ψμ), 𝒟_n) / n ≥ dim μ + ρ`.

The proof averages over the level-`i` components `ν_{p,i}` and `(ψμ)_{x,i}`. Lemma 3.8 bounds
`H(ν.(ψμ), 𝒟_n)` below by the average of `H(ν_{p,i}.(ψμ)_{x,i}, 𝒟_{i+m}) / m`. By Lemma 3.9 each
term is at least `H(ξ ∗ (ψμ)_{x,i}, 𝒟_{i+m}) / m` up to `O(1/m)`, with
`ξ = (S_{p'(x)⁻¹} ν_{p,i}).x`. This is at least `dim μ - O(δ)` when the component of `ψμ` has
almost full entropy (Proposition 3.3), and at least `dim μ + ρ - O(δ)` when moreover its
components at finer scales are not of full entropy (Corollary 3.7) and `ξ` has positive entropy
(Lemma 3.10), by Hochman's theorem (Theorem 3.2).

## Main declarations

* `component_bound`: the bound for one pair of components.
* `pairAvg_ge_of_forall`: averaging the bounds over the components.
* `level_bound`, `final_arith`: the bound at one level and the final estimate.
* `entropyIncrease_of_structure`: Theorem 3.1 for a measure with the structure `SCStructure`.
* `entropyIncreasePoly`: Theorem 3.1 for the self-conformal measure, `EntropyIncreasePoly`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.EntropyIncrease`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic

open MeasureTheory ProbabilityTheory Set Filter Topology FractalGeometry.SelfConformal
open scoped ENNReal MeasureTheory

/-! ### The bound for one pair of components -/

section Components

variable {k : ℕ}

/-- The bound of Section 3.4 for one pair of level-`i` components `ρ` of `ν` and `τ` of `ψμ`:
with `e₁ = 1` when `H(τ, 𝒟_{i+m}) / m > d - δ` and `e₂ = 1` when the components of `τ` at the
levels `i ≤ j ≤ i + m` satisfy the hypothesis of Hochman's theorem,
`(d - 2δ) e₁ + ρ_H (τ{x : H(ρ.x, 𝒟_{i+m}) / m > ε₀} - (1 - e₁) - (1 - e₂)) ≤ H(ρ.τ, 𝒟_{i+m}) / m`.
-/
theorem component_bound {ρ : Measure (Poly k)} [IsProbabilityMeasure ρ] {τ : Measure ℝ}
    [IsProbabilityMeasure τ] {i m l : ℕ} {c : Fin (k + 1) → ℤ} {c' : ℤ}
    {d δ ρH ε ε'' ε₀ η CL : ℝ} (hε : 0 < ε) (hm : 1 ≤ m) (hρH : 0 < ρH)
    (hε''0 : 0 < ε'') (hε''1 : ε'' ≤ 1) (hε''ε : ε'' ≤ ε / (2 * (k + 1))) (hε''ε₀ : ε'' ≤ ε₀ / 2)
    (hCL : CL + 3 ≤ δ * m)
    (hCs : Real.log (4 * (k * (k + 1) * ε⁻¹) + 2) / Real.log 2 ≤ ε₀ / 2 * m)
    (hρc : ∀ᵐ q ∂ρ, cellIdxVec i q = c ∧ ‖q‖ ≤ ε⁻¹ ∧
      ∀ x ∈ AnalyticESC.I, ε ≤ |Poly.derivEval q x|)
    (hτc : ∀ᵐ y ∂τ, cellIdx i y = c' ∧ y ∈ AnalyticESC.I)
    (hlin : ∀ p : Poly k, ‖p‖ ≤ ε⁻¹ → ∀ x ∈ AnalyticESC.I, ε ≤ |Poly.derivEval p x| →
      (∀ᵐ q ∂ρ, ∀ j, |q j - p j| ≤ 1 / 2 ^ i) →
      (∀ᵐ y ∂τ, y ∈ AnalyticESC.I ∧ |y - x| ≤ 1 / 2 ^ i) →
      dyadicEntropy (actPoint (ρ.map (Poly.scale (Poly.derivEval p x)⁻¹)) x ∗ τ) (i + m) ≤
        dyadicEntropy (act ρ τ) (i + m) + CL)
    (hHG : ∀ ξ : Measure ℝ, IsProbabilityMeasure ξ →
      (∃ a : ℝ, ξ (Set.Icc a (a + ε''⁻¹ / 2 ^ i))ᶜ = 0) →
      (∃ b : ℝ, τ (Set.Icc b (b + ε''⁻¹ / 2 ^ i))ᶜ = 0) →
      ε'' < dyadicEntropy ξ (i + m) / m →
      1 - η < levelProb τ i m
        (fun j x => dyadicEntropy (component τ j x) (j + l) / l < 1 - ε'') →
      dyadicEntropy τ (i + m) / m + ρH ≤ dyadicEntropy (ξ ∗ τ) (i + m) / m) :
    (d - 2 * δ) * (if d - δ < dyadicEntropy τ (i + m) / m then 1 else 0) +
      ρH * (τ.real {x | ε₀ < dyadicEntropy (actPoint ρ x) (i + m) / m} -
        (1 - (if d - δ < dyadicEntropy τ (i + m) / m then 1 else 0)) -
        (1 - (if 1 - η < levelProb τ i m
          (fun j x => dyadicEntropy (component τ j x) (j + l) / l < 1 - ε'') then 1 else 0))) ≤
      dyadicEntropy (act ρ τ) (i + m) / m := by
  classical
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hG0 : 0 ≤ dyadicEntropy (act ρ τ) (i + m) / m := by
    refine div_nonneg ?_ hm0.le
    rw [dyadicEntropy_eq_ent]
    exact div_nonneg (ent_nonneg _) (Real.log_nonneg (by norm_num))
  have hτle : τ.real {x | ε₀ < dyadicEntropy (actPoint ρ x) (i + m) / m} ≤ 1 := measureReal_le_one
  have hτnn : 0 ≤ τ.real {x | ε₀ < dyadicEntropy (actPoint ρ x) (i + m) / m} := measureReal_nonneg
  -- a representative polynomial `p` of the component `ρ`
  obtain ⟨p, hpc, hpR, hpd⟩ := hρc.exists
  have hcube : ∀ᵐ q ∂ρ, ∀ j, |q j - p j| ≤ 1 / 2 ^ i := by
    filter_upwards [hρc] with q hq j
    exact (abs_sub_lt_of_cellIdx_eq (congrFun (hq.1.trans hpc.symm) j)).le
  -- the bound at a point `x` of the cell of `τ`
  have hpoint : ∀ x, cellIdx i x = c' → x ∈ AnalyticESC.I →
      dyadicEntropy (actPoint (ρ.map (Poly.scale (Poly.derivEval p x)⁻¹)) x ∗ τ) (i + m) ≤
        dyadicEntropy (act ρ τ) (i + m) + CL := by
    intro x hxc hxI
    refine hlin p hpR x hxI (hpd x hxI) hcube ?_
    filter_upwards [hτc] with y hy
    exact ⟨hy.2, (abs_sub_lt_of_cellIdx_eq (hy.1.trans hxc.symm)).le⟩
  -- the support of `τ`
  have hτsupp : ∀ᵐ y ∂τ, y ∈ Icc ((c' : ℝ) / 2 ^ i) ((c' : ℝ) / 2 ^ i + 1 / 2 ^ i) := by
    filter_upwards [hτc] with y hy
    have h := (mem_cell_iff i c' y).2 hy.1
    rw [cell, mem_Ico] at h
    refine ⟨h.1, h.2.le.trans (le_of_eq ?_)⟩
    ring
  -- the support of `ξ = (S_{p'(x)⁻¹} ρ).x`
  have hξsupp : ∀ x ∈ AnalyticESC.I, ∀ᵐ y ∂(actPoint (ρ.map
      (Poly.scale (Poly.derivEval p x)⁻¹)) x), y ∈ Icc
        ((Poly.derivEval p x)⁻¹ * Poly.eval p x - |(Poly.derivEval p x)⁻¹| * ((k + 1) / 2 ^ i))
        ((Poly.derivEval p x)⁻¹ * Poly.eval p x +
          |(Poly.derivEval p x)⁻¹| * ((k + 1) / 2 ^ i)) := by
    intro x hxI
    rw [actPoint_map_scale]
    have hmeas : Measurable fun y : ℝ => (Poly.derivEval p x)⁻¹ * y := measurable_const_mul _
    refine (ae_map_iff hmeas.aemeasurable (by exact measurableSet_Icc)).2 ?_
    filter_upwards [ae_actPoint_mem_Icc hcube hxI] with y hy
    have hy' : |y - Poly.eval p x| ≤ (k + 1) * (1 / 2 ^ i) := by
      rw [abs_le]
      constructor <;> linarith [hy.1, hy.2]
    have : |(Poly.derivEval p x)⁻¹ * y - (Poly.derivEval p x)⁻¹ * Poly.eval p x| ≤
        |(Poly.derivEval p x)⁻¹| * ((k + 1) / 2 ^ i) := by
      rw [← mul_sub, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [div_eq_mul_one_div]
      exact hy'
    rw [abs_le] at this
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  -- a point of the cell of `τ` in `I`
  obtain ⟨x₀, hx₀c, hx₀I⟩ := hτc.exists
  -- the convolution bound gives the case `e₁ = 1`
  have hE1 : d - δ < dyadicEntropy τ (i + m) / m →
      d - 2 * δ ≤ dyadicEntropy (act ρ τ) (i + m) / m := by
    intro h1
    have hconv := dyadicEntropy_le_conv _ τ (hξsupp x₀ hx₀I) hτsupp (i + m)
    have h2 := hpoint x₀ hx₀c hx₀I
    have h3 : dyadicEntropy τ (i + m) ≤ dyadicEntropy (act ρ τ) (i + m) + δ * m := by linarith
    have h4 : dyadicEntropy τ (i + m) / m ≤ dyadicEntropy (act ρ τ) (i + m) / m + δ := by
      rw [div_le_iff₀ hm0, add_mul, div_mul_cancel₀ _ hm0.ne']
      linarith
    linarith
  -- Hochman's theorem gives the case `e₁ = e₂ = 1` with a good point
  have hE2 : d - δ < dyadicEntropy τ (i + m) / m →
      1 - η < levelProb τ i m
        (fun j x => dyadicEntropy (component τ j x) (j + l) / l < 1 - ε'') →
      0 < τ.real {x | ε₀ < dyadicEntropy (actPoint ρ x) (i + m) / m} →
      d - 2 * δ + ρH ≤ dyadicEntropy (act ρ τ) (i + m) / m := by
    intro h1 h2 h3
    -- a good point of the cell of `τ` in `I`
    have hne : ({x | ε₀ < dyadicEntropy (actPoint ρ x) (i + m) / m} ∩
        {y | cellIdx i y = c' ∧ y ∈ AnalyticESC.I}).Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      have h0 : τ {x | ε₀ < dyadicEntropy (actPoint ρ x) (i + m) / m} = 0 := by
        have hle : τ {x | ε₀ < dyadicEntropy (actPoint ρ x) (i + m) / m} ≤
            τ {y | cellIdx i y = c' ∧ y ∈ AnalyticESC.I}ᶜ := by
          refine measure_mono fun y hy hy' => ?_
          have : y ∈ ({x | ε₀ < dyadicEntropy (actPoint ρ x) (i + m) / m} ∩
              {y | cellIdx i y = c' ∧ y ∈ AnalyticESC.I}) := ⟨hy, hy'⟩
          rw [hne] at this
          exact this
        have hz : τ {y | cellIdx i y = c' ∧ y ∈ AnalyticESC.I}ᶜ = 0 := ae_iff.1 hτc
        exact le_antisymm (hle.trans hz.le) (zero_le)
      rw [measureReal_def, h0, ENNReal.toReal_zero] at h3
      exact lt_irrefl 0 h3
    obtain ⟨x, hxgood, hxc, hxI⟩ := hne
    set c₀ : ℝ := (Poly.derivEval p x)⁻¹
    have hpx : ε ≤ |Poly.derivEval p x| := hpd x hxI
    have hpx0 : Poly.derivEval p x ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hpx
      linarith
    have hc₀ : |c₀| ≤ ε⁻¹ := by
      rw [abs_inv]
      exact inv_anti₀ hε hpx
    -- the support condition for `ξ`
    have hξ1 : ∃ a : ℝ, (actPoint (ρ.map (Poly.scale c₀)) x)
        (Set.Icc a (a + ε''⁻¹ / 2 ^ i))ᶜ = 0 := by
      refine ⟨c₀ * Poly.eval p x - |c₀| * ((k + 1) / 2 ^ i), ?_⟩
      have h := hξsupp x hxI
      rw [ae_iff] at h
      have hk : 0 < (k : ℝ) + 1 := by positivity
      have h2i : (0 : ℝ) < 2 ^ i := by positivity
      have hε'' : 2 * ((k : ℝ) + 1) * ε⁻¹ ≤ ε''⁻¹ := by
        rw [le_inv_comm₀ (by positivity) hε''0, mul_inv, inv_inv]
        calc ε'' ≤ ε / (2 * (k + 1)) := hε''ε
          _ = (2 * ((k : ℝ) + 1))⁻¹ * ε := by ring
      have hL : 2 * (|c₀| * ((k + 1) / 2 ^ i)) ≤ ε''⁻¹ / 2 ^ i :=
        calc 2 * (|c₀| * ((k + 1) / 2 ^ i)) = (2 * (k + 1) * |c₀|) / 2 ^ i := by ring
          _ ≤ (2 * (k + 1) * ε⁻¹) / 2 ^ i := by gcongr
          _ ≤ ε''⁻¹ / 2 ^ i := by gcongr
      have hsub : (Set.Icc (c₀ * Poly.eval p x - |c₀| * ((k + 1) / 2 ^ i))
          (c₀ * Poly.eval p x - |c₀| * ((k + 1) / 2 ^ i) + ε''⁻¹ / 2 ^ i))ᶜ ⊆
          {y | y ∉ Icc (c₀ * Poly.eval p x - |c₀| * ((k + 1) / 2 ^ i))
            (c₀ * Poly.eval p x + |c₀| * ((k + 1) / 2 ^ i))} :=
        fun y hy hy' => hy ⟨hy'.1, by linarith [hy'.2]⟩
      exact measure_mono_null hsub h
    have hτ1 : ∃ b : ℝ, τ (Set.Icc b (b + ε''⁻¹ / 2 ^ i))ᶜ = 0 := by
      refine ⟨(c' : ℝ) / 2 ^ i, ?_⟩
      have h := hτsupp
      rw [ae_iff] at h
      have hL : 1 / 2 ^ i ≤ ε''⁻¹ / 2 ^ i := by
        gcongr
        exact one_le_inv₀ hε''0 |>.2 hε''1
      have hsub : (Set.Icc ((c' : ℝ) / 2 ^ i) ((c' : ℝ) / 2 ^ i + ε''⁻¹ / 2 ^ i))ᶜ ⊆
          {y | y ∉ Icc ((c' : ℝ) / 2 ^ i) ((c' : ℝ) / 2 ^ i + 1 / 2 ^ i)} :=
        fun y hy hy' => hy ⟨hy'.1, by linarith [hy'.2]⟩
      exact measure_mono_null hsub h
    -- the entropy condition for `ξ`
    have hξent : ε'' < dyadicEntropy (actPoint (ρ.map (Poly.scale c₀)) x) (i + m) / m := by
      have hA : |c₀|⁻¹ ≤ k * (k + 1) * ε⁻¹ := by
        rw [abs_inv, inv_inv]
        refine (abs_derivEval_le p hxI).trans ?_
        exact mul_le_mul_of_nonneg_left hpR (by positivity)
      have hc0 : c₀ ≠ 0 := inv_ne_zero hpx0
      have hsc := dyadicEntropy_le_map_mul (ae_actPoint_mem_Icc hcube hxI) hc0 hA (i + m)
      rw [← actPoint_map_scale] at hsc
      have hgood : ε₀ < dyadicEntropy (actPoint ρ x) (i + m) / m := hxgood
      rw [lt_div_iff₀ hm0] at hgood
      rw [lt_div_iff₀ hm0]
      nlinarith
    have hHG' := hHG _ inferInstance hξ1 hτ1 hξent h2
    have hpt := hpoint x hxc hxI
    have hCL' : CL ≤ δ * m := by linarith
    have h5 : dyadicEntropy (actPoint (ρ.map (Poly.scale c₀)) x ∗ τ) (i + m) / m ≤
        dyadicEntropy (act ρ τ) (i + m) / m + δ := by
      rw [div_le_iff₀ hm0, add_mul, div_mul_cancel₀ _ hm0.ne']
      linarith
    linarith
  -- the case analysis
  by_cases h1 : d - δ < dyadicEntropy τ (i + m) / m
  · by_cases h2 : 1 - η < levelProb τ i m
        (fun j x => dyadicEntropy (component τ j x) (j + l) / l < 1 - ε'')
    · simp only [h1, h2, ↓reduceIte, sub_self, sub_zero, mul_one]
      rcases eq_or_lt_of_le hτnn with h0 | hpos
      · rw [← h0, mul_zero, add_zero]
        exact hE1 h1
      · have := hE2 h1 h2 hpos
        nlinarith
    · simp only [h1, h2, ↓reduceIte, sub_self, sub_zero, mul_one]
      have := hE1 h1
      nlinarith
  · simp only [h1, ↓reduceIte, mul_zero, zero_add]
    have : (if 1 - η < levelProb τ i m
        (fun j x => dyadicEntropy (component τ j x) (j + l) / l < 1 - ε'') then (1 : ℝ) else 0)
          ≤ 1 := by split_ifs <;> norm_num
    nlinarith

/-- Averaging the bounds of `component_bound` over the level-`i` components of `ν` and `θ`. -/
theorem pairAvg_ge_of_forall {ν : Measure (Poly k)} [IsProbabilityMeasure ν] {θ : Measure ℝ}
    [IsProbabilityMeasure θ] {i : ℕ} (hfν : FiniteLabels ν (cellIdxVec i))
    (hfθ : FiniteLabels θ (cellIdx i)) {G : Measure (Poly k) → Measure ℝ → ℝ}
    {e₁ e₂ : Measure ℝ → ℝ} {good : Measure (Poly k) → Set ℝ} {a b : ℝ} (hb : 0 ≤ b)
    (h : ∀ c, ν (cellIdxVec i ⁻¹' {c}) ≠ 0 → ∀ c', θ (cellIdx i ⁻¹' {c'}) ≠ 0 →
      a * e₁ (comp θ (cellIdx i) c') + b * ((comp θ (cellIdx i) c').real
        (good (comp ν (cellIdxVec i) c)) - (1 - e₁ (comp θ (cellIdx i) c')) -
          (1 - e₂ (comp θ (cellIdx i) c'))) ≤
        G (comp ν (cellIdxVec i) c) (comp θ (cellIdx i) c')) :
    a * cavg θ (cellIdx i) e₁ + b * (cavg ν (cellIdxVec i) (fun ρ => θ.real (good ρ)) -
      (1 - cavg θ (cellIdx i) e₁) - (1 - cavg θ (cellIdx i) e₂)) ≤ pairAvg ν θ i G := by
  have hmθ := measurable_cellIdx i
  have hmν := measurable_cellIdxVec (k := k) i
  have hinner : ∀ c, ν (cellIdxVec i ⁻¹' {c}) ≠ 0 →
      b * θ.real (good (comp ν (cellIdxVec i) c)) +
        ((a + b) * cavg θ (cellIdx i) e₁ + b * cavg θ (cellIdx i) e₂ - 2 * b) ≤
      cavg θ (cellIdx i) (fun τ => G (comp ν (cellIdxVec i) c) τ) := by
    intro c hc
    have h1 := cavg_mono hfθ
      (F := fun τ => (a + b) * e₁ τ + b * τ.real (good (comp ν (cellIdxVec i) c)) +
        b * e₂ τ + (-2 * b)) (G := fun τ => G (comp ν (cellIdxVec i) c) τ)
      (fun c' hc' => by have := h c hc c' hc'; linarith)
    rw [cavg_affine3 hmθ hfθ] at h1
    have h2 := measureReal_le_cavg hmθ hfθ (good (comp ν (cellIdxVec i) c))
    nlinarith
  have h3 := cavg_mono hfν
    (F := fun ρ => b * θ.real (good ρ) + 0 * θ.real (good ρ) + 0 * θ.real (good ρ) +
      ((a + b) * cavg θ (cellIdx i) e₁ + b * cavg θ (cellIdx i) e₂ - 2 * b))
    (G := fun ρ => cavg θ (cellIdx i) (fun τ => G ρ τ))
    (fun c hc => by have := hinner c hc; simp only [zero_mul, add_zero]; exact this)
  rw [cavg_affine3 hmν hfν] at h3
  have he : pairAvg ν θ i G = cavg ν (cellIdxVec i) (fun ρ => cavg θ (cellIdx i) fun τ => G ρ τ) :=
    rfl
  rw [he]
  linarith

end Components

/-! ### Theorem 3.1 -/

section Theorem31

variable {k : ℕ}

/-- The final arithmetic of Section 3.4. -/
theorem final_arith {n m K : ℕ} {H d δ ρH ε₀ ε₇ C₈ Bsum A2sum : ℝ} (hn : (0 : ℝ) < n)
    (hm : (0 : ℝ) < m) (hρH : 0 < ρH) (hε₀ : 0 < ε₀)
    (hsum : n * (d - 3 * δ) + ρH * (Bsum - n * δ - n + A2sum) - (m + K) * (1 + ρH) ≤
      H + C₈ * (n / m + m))
    (hB : ε₀ * n < Bsum) (hA2 : (1 - ε₇) * n < A2sum) (hδ : δ ≤ ε₀ / 4)
    (hδρ : δ ≤ ρH * ε₀ / 48) (hε₇ : ε₇ ≤ ε₀ / 4) (hmC₈ : 16 * |C₈| ≤ ρH * ε₀ * m)
    (hN₃ : 16 * (((m : ℝ) + K) * (1 + ρH) + |C₈| * m) / (ρH * ε₀) ≤ n) :
    d + ρH * ε₀ / 4 ≤ H / n := by
  have hC1 : C₈ * (n / m) ≤ ρH * ε₀ * n / 16 := by
    have h1 : C₈ * (n / m) ≤ |C₈| * (n / m) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have h3 : |C₈| / m ≤ ρH * ε₀ / 16 := by
      rw [div_le_iff₀ hm]
      linarith
    have h4 : |C₈| * (n / m) = |C₈| / m * n := by ring
    have h5 : |C₈| / m * n ≤ ρH * ε₀ / 16 * n := mul_le_mul_of_nonneg_right h3 hn.le
    linarith
  have hC2 : ((m : ℝ) + K) * (1 + ρH) + |C₈| * m ≤ ρH * ε₀ * n / 16 := by
    rw [div_le_iff₀ (by positivity)] at hN₃
    linarith
  have hC3 : C₈ * m ≤ |C₈| * m := mul_le_mul_of_nonneg_right (le_abs_self _) hm.le
  have hgain : ρH * (ε₀ * n / 2) ≤ ρH * (Bsum - n * δ - n + A2sum) := by
    have h1 : n * δ ≤ n * (ε₀ / 4) := mul_le_mul_of_nonneg_left hδ hn.le
    have h2 : n * ε₇ ≤ n * (ε₀ / 4) := mul_le_mul_of_nonneg_left hε₇ hn.le
    have : ε₀ * n / 2 ≤ Bsum - n * δ - n + A2sum := by nlinarith
    exact mul_le_mul_of_nonneg_left this hρH.le
  have h3δ : 3 * δ * n ≤ ρH * ε₀ * n / 16 := by
    have : 3 * δ ≤ ρH * ε₀ / 16 := by linarith
    nlinarith
  rw [le_div_iff₀ hn]
  have e1 : (n : ℝ) * (d - 3 * δ) = n * d - 3 * δ * n := by ring
  have e2 : (d + ρH * ε₀ / 4) * n = n * d + ρH * ε₀ * n / 4 := by ring
  have e3 : C₈ * (n / m + m) = C₈ * (n / m) + C₈ * m := by ring
  have e4 : ρH * (ε₀ * n / 2) = ρH * ε₀ * n / 2 := by ring
  rw [e1, e3] at hsum
  rw [e4] at hgain
  rw [e2]
  have hP : 0 ≤ ρH * ε₀ * n := by positivity
  linarith

/-- The bound at one level `i`, from `component_bound` (for `i ≥ m + K`) and the nonnegativity of
entropy (for `i < m + K`). -/
theorem level_bound {ν : Measure (Poly k)} [IsProbabilityMeasure ν] {θ : Measure ℝ}
    [IsProbabilityMeasure θ] {i m L₀ K : ℕ} {d δ ρH ε ε'' ε₀ ε₇ CL : ℝ} (hd1 : d < 1)
    (hε : 0 < ε) (hm1 : 1 ≤ m) (hδ0 : 0 < δ) (hρH : 0 < ρH) (hε''0 : 0 < ε'') (hε''1 : ε'' ≤ 1)
    (hε''ε : ε'' ≤ ε / (2 * (k + 1))) (hε''ε₀ : ε'' ≤ ε₀ / 2) (hmCL : CL + 3 ≤ δ * m)
    (hmCs : Real.log (4 * (k * (k + 1) * ε⁻¹) + 2) / Real.log 2 ≤ ε₀ / 2 * m)
    (hνgood : ∀ᵐ q ∂ν, ‖q‖ ≤ ε⁻¹ ∧ ∀ x ∈ AnalyticESC.I, ε ≤ |Poly.derivEval q x|)
    (hθIae : ∀ᵐ x ∂θ, x ∈ AnalyticESC.I)
    (hA1i : 1 - δ < cavg θ (cellIdx i)
      (fun τ => if d - δ < dyadicEntropy τ (i + m) / m then 1 else 0))
    (hlin : m + K ≤ i → ∀ ρ : Measure (Poly k), IsProbabilityMeasure ρ → ∀ τ : Measure ℝ,
      IsProbabilityMeasure τ → ∀ p : Poly k, ‖p‖ ≤ ε⁻¹ → ∀ x ∈ AnalyticESC.I,
      ε ≤ |Poly.derivEval p x| → (∀ᵐ q ∂ρ, ∀ j, |q j - p j| ≤ 1 / 2 ^ i) →
      (∀ᵐ y ∂τ, y ∈ AnalyticESC.I ∧ |y - x| ≤ 1 / 2 ^ i) →
      dyadicEntropy (actPoint (ρ.map (Poly.scale (Poly.derivEval p x)⁻¹)) x ∗ τ) (i + m) ≤
        dyadicEntropy (act ρ τ) (i + m) + CL)
    (hHG : 1 ≤ i → ∀ ξ τ : Measure ℝ, IsProbabilityMeasure ξ → IsProbabilityMeasure τ →
      (∃ a : ℝ, ξ (Set.Icc a (a + ε''⁻¹ / 2 ^ i))ᶜ = 0) →
      (∃ b : ℝ, τ (Set.Icc b (b + ε''⁻¹ / 2 ^ i))ᶜ = 0) →
      ε'' < dyadicEntropy ξ (i + m) / m →
      1 - ε₇ < levelProb τ i m
        (fun j x => dyadicEntropy (component τ j x) (j + L₀) / L₀ < 1 - ε'') →
      dyadicEntropy τ (i + m) / m + ρH ≤ dyadicEntropy (ξ ∗ τ) (i + m) / m) :
    d - 3 * δ + ρH * (cavg ν (cellIdxVec i)
        (fun ρ => θ.real {x | ε₀ < dyadicEntropy (actPoint ρ x) (i + m) / m}) - δ -
        (1 - cavg θ (cellIdx i) (fun τ => if 1 - ε₇ < levelProb τ i m
          (fun j x => dyadicEntropy (component τ j x) (j + L₀) / L₀ < 1 - ε'') then 1 else 0))) -
      (if i < m + K then 1 + ρH else 0) ≤
    pairAvg ν θ i (fun ρ τ => dyadicEntropy (act ρ τ) (i + m) / m) := by
  classical
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hνnorm : ∀ᵐ q ∂ν, ‖q‖ ≤ ε⁻¹ := hνgood.mono fun q hq => hq.1
  have hfν : FiniteLabels ν (cellIdxVec i) :=
    finiteLabels_cellIdxVec_comp_of_norm_le (F := id) i hνnorm
  have hfθ : FiniteLabels θ (cellIdx i) := finiteLabels_cellIdx_comp (F := id) i hθIae
  have hA1le := cavg_ind_le_one (measurable_cellIdx i) hfθ
    (fun τ => d - δ < dyadicEntropy τ (i + m) / m)
  have hA2le := cavg_ind_le_one (measurable_cellIdx i) hfθ
    (fun τ => 1 - ε₇ < levelProb τ i m
      (fun j x => dyadicEntropy (component τ j x) (j + L₀) / L₀ < 1 - ε''))
  have hBle : cavg ν (cellIdxVec i)
      (fun ρ => θ.real {x | ε₀ < dyadicEntropy (actPoint ρ x) (i + m) / m}) ≤ 1 :=
    cavg_le_of_le (measurable_cellIdxVec i) hfν fun _ _ => measureReal_le_one
  by_cases hi : i < m + K
  · simp only [hi, ↓reduceIte]
    have h0 : 0 ≤ pairAvg ν θ i (fun ρ τ => dyadicEntropy (act ρ τ) (i + m) / m) :=
      cavg_nonneg hfν fun c hc => cavg_nonneg hfθ fun c' hc' => by
        have := comp_isProbabilityMeasure hc
        have := comp_isProbabilityMeasure hc'
        refine div_nonneg ?_ hm0.le
        rw [dyadicEntropy_eq_ent]
        exact div_nonneg (ent_nonneg _) (Real.log_nonneg (by norm_num))
    nlinarith
  · simp only [hi, ↓reduceIte, sub_zero]
    have hiK : m + K ≤ i := by omega
    have hi1 : 1 ≤ i := by omega
    have hmain := pairAvg_ge_of_forall hfν hfθ (le_of_lt hρH)
      (G := fun ρ τ => dyadicEntropy (act ρ τ) (i + m) / m)
      (e₁ := fun τ => if d - δ < dyadicEntropy τ (i + m) / m then 1 else 0)
      (e₂ := fun τ => if 1 - ε₇ < levelProb τ i m
        (fun j x => dyadicEntropy (component τ j x) (j + L₀) / L₀ < 1 - ε'') then 1 else 0)
      (good := fun ρ => {x | ε₀ < dyadicEntropy (actPoint ρ x) (i + m) / m})
      (a := d - 2 * δ) fun c hc c' hc' => by
        have := comp_isProbabilityMeasure hc
        have := comp_isProbabilityMeasure hc'
        refine component_bound (c := c) (c' := c') hε hm1 hρH hε''0 hε''1 hε''ε
          hε''ε₀ hmCL hmCs ?_ ?_ ?_ ?_
        · filter_upwards [ae_comp_mem (measurable_cellIdxVec i) c,
            (cond_absolutelyContinuous (μ := ν)).ae_le hνgood] with q hq1 hq2
          exact ⟨hq1, hq2⟩
        · filter_upwards [ae_comp_mem (measurable_cellIdx i) c',
            (cond_absolutelyContinuous (μ := θ)).ae_le hθIae] with y hy1 hy2
          exact ⟨hy1, hy2⟩
        · intro p hp x hx hpx hq hy
          exact hlin hiK _ inferInstance _ inferInstance p hp x hx hpx hq hy
        · intro ξ hξ ha hb' he hl
          exact hHG hi1 ξ _ hξ inferInstance ha hb' he hl
    set A := cavg θ (cellIdx i) (fun τ => if d - δ < dyadicEntropy τ (i + m) / m then 1 else 0)
    have hd2 : d - 3 * δ ≤ (d - 2 * δ) * A := by
      rcases le_or_gt 0 d with hd0' | hd0'
      · nlinarith
      · nlinarith
    nlinarith

/-- Rearrangement of the sum of the level bounds in the proof of Theorem 3.1. -/
theorem sum_bracket (n : ℕ) (d δ ρH : ℝ) (B A : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, (d - 3 * δ + ρH * (B i - δ - (1 - A i))) =
      n * (d - 3 * δ) + ρH * (∑ i ∈ Finset.range n, B i - n * δ - n +
        ∑ i ∈ Finset.range n, A i) := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib]
  have h1 : ∑ x ∈ Finset.range n, (1 - A x) = n - ∑ x ∈ Finset.range n, A x := by
    rw [Finset.sum_sub_distrib]
    simp
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [h1]
  ring

/-- The sum of `b` over the levels `i < a` among `i < n` is at most `a b`. -/
theorem sum_ite_lt_le (n a : ℕ) (b : ℝ) (hb : 0 ≤ b) :
    ∑ i ∈ Finset.range n, (if i < a then b else 0) ≤ (a : ℝ) * b := by
  classical
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.range n).filter (fun i => i < a)).card ≤ a := by
    calc ((Finset.range n).filter (fun i => i < a)).card
        ≤ (Finset.range a).card := Finset.card_le_card fun i hi => by
          simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
          exact hi.2
      _ = a := Finset.card_range _
  have : (((Finset.range n).filter (fun i => i < a)).card : ℝ) ≤ a := by exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_right this hb

/-- Theorem 3.1 of Rapaport for a measure `μ` with the structure `SCStructure`, exact
dimensional with dimension `d < 1`, and maps `ψ : I → I` with
`ε |x - y| ≤ |ψ x - ψ y| ≤ ε⁻¹ |x - y|` on `I`. -/
theorem entropyIncrease_of_structure (hHG : HochmanEntropyGrowth) {μ : Measure ℝ}
    (hμ : SCStructure μ) {d : ℝ} (hd : FractalGeometry.IsExactDim μ d) (hd1 : d < 1) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ ν : Measure (Poly k),
      IsProbabilityMeasure ν →
      (∀ᵐ q ∂ν, ‖q‖ ≤ ε⁻¹ ∧ ∀ x ∈ AnalyticESC.I, ε ≤ |Poly.derivEval q x|) →
      ε ≤ dyadicEntropyVec ν n / n →
      ∀ ψ : ℝ → ℝ, MapsTo ψ AnalyticESC.I AnalyticESC.I → BiLipOn ψ ε ε⁻¹ →
      d + ρ ≤ dyadicEntropy (act ν (μ.map ψ)) n / n := by
  classical
  have hμP := hμ.isProb
  have hd0 : 0 < 1 - d := by linarith
  -- Lemma 3.10 and the small balls
  obtain ⟨ε₀, hε₀, h310⟩ := lemma310 k hε
  obtain ⟨δa, hδa, hballs⟩ := small_balls hμ hε (c := 1 / (2 * ((k : ℝ) + 1))) (by positivity)
  obtain ⟨M₆, hM₆⟩ := h310 δa hδa
  -- the parameters of Hochman's theorem
  obtain ⟨ε'', hε''0, hε''1, hε''ε₀, hε''d, hε''ε⟩ : ∃ ε'' : ℝ, 0 < ε'' ∧ ε'' < 1 ∧
      ε'' ≤ ε₀ / 2 ∧ ε'' ≤ (1 - d) / 2 ∧ ε'' ≤ ε / (2 * ((k : ℝ) + 1)) :=
    ⟨min (min (ε₀ / 2) ((1 - d) / 2)) (min (ε / (2 * ((k : ℝ) + 1))) (1 / 2)),
      lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by norm_num)),
      (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt (by norm_num)),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _)⟩
  obtain ⟨η₀, hη₀, hHG1⟩ := hHG ε'' hε''0 hε''1
  obtain ⟨ε₇, hε₇0, hε₇η, hε₇ε₀, hε₇d⟩ : ∃ ε₇ : ℝ, 0 < ε₇ ∧ ε₇ < η₀ ∧ ε₇ ≤ ε₀ / 4 ∧
      ε₇ ≤ (1 - d) / 2 :=
    ⟨min (min (η₀ / 2) (ε₀ / 4)) ((1 - d) / 2),
      lt_min (lt_min (by positivity) (by positivity)) (by positivity),
      (min_le_left _ _).trans_lt ((min_le_left _ _).trans_lt (by linarith)),
      (min_le_left _ _).trans (min_le_right _ _), min_le_right _ _⟩
  obtain ⟨L₀, hL₀, hcor⟩ := cor37 hμ hd hε ε₇ hε₇0
  obtain ⟨ρH, hρH, NH, hNH⟩ := hHG1 L₀ hL₀ ε₇ hε₇0 hε₇η
  -- the error parameter
  obtain ⟨δ, hδ0, hδε₀, hδρ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε₀ / 4 ∧ δ ≤ ρH * ε₀ / 48 :=
    ⟨min (ε₀ / 4) (ρH * ε₀ / 48), lt_min (by positivity) (by positivity), min_le_left _ _,
      min_le_right _ _⟩
  obtain ⟨M₄, hM₄⟩ := prop33 hμ hd hε δ hδ0
  obtain ⟨K, CL, hlin⟩ := linearisation k ε⁻¹ ε hε
  obtain ⟨C₈, hC₈⟩ := sum_pairAvg_le k ε⁻¹
  -- the scale `m`
  obtain ⟨m, hmM₄, hmM₆, hmNH, hm1, hmCL, hmCs, hmC₈⟩ : ∃ m : ℕ, M₄ ≤ m ∧ M₆ ≤ m ∧ NH ≤ m ∧
      1 ≤ m ∧ CL + 3 ≤ δ * m ∧
      Real.log (4 * (k * (k + 1) * ε⁻¹) + 2) / Real.log 2 ≤ ε₀ / 2 * m ∧
      16 * |C₈| ≤ ρH * ε₀ * m := by
    set Cs := Real.log (4 * (k * (k + 1) * ε⁻¹) + 2) / Real.log 2
    obtain ⟨m₀, hm₀⟩ := exists_nat_ge ((|CL| + 3) / δ + 2 * |Cs| / ε₀ +
      16 * |C₈| / (ρH * ε₀))
    refine ⟨max (max (max M₄ M₆) (max NH 1)) m₀, by omega, by omega, by omega, by omega, ?_⟩
    have hm : (m₀ : ℝ) ≤ (max (max (max M₄ M₆) (max NH 1)) m₀ : ℕ) := by
      exact_mod_cast le_max_right _ _
    have h1 : 0 ≤ (|CL| + 3) / δ := by positivity
    have h2 : 0 ≤ 2 * |Cs| / ε₀ := by positivity
    have h3 : 0 ≤ 16 * |C₈| / (ρH * ε₀) := by positivity
    refine ⟨?_, ?_, ?_⟩
    · have : (|CL| + 3) / δ ≤ (max (max (max M₄ M₆) (max NH 1)) m₀ : ℕ) := by linarith
      rw [div_le_iff₀ hδ0] at this
      linarith [le_abs_self CL]
    · have : 2 * |Cs| / ε₀ ≤ (max (max (max M₄ M₆) (max NH 1)) m₀ : ℕ) := by linarith
      rw [div_le_iff₀ hε₀] at this
      linarith [le_abs_self Cs]
    · have : 16 * |C₈| / (ρH * ε₀) ≤ (max (max (max M₄ M₆) (max NH 1)) m₀ : ℕ) := by linarith
      rw [div_le_iff₀ (by positivity)] at this
      linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  obtain ⟨N₂, hN₂⟩ := hM₆ m hmM₆
  obtain ⟨N₁, hN₁⟩ := hcor L₀ le_rfl m
  obtain ⟨N₃, hN₃⟩ := exists_nat_ge (16 * (((m : ℝ) + K) * (1 + ρH) + |C₈| * m) / (ρH * ε₀))
  refine ⟨ρH * ε₀ / 4, by positivity, max (max N₁ N₂) (max N₃ 1), ?_⟩
  intro n hn ν hν hνgood hνent ψ hψI hψL
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : (N₃ : ℝ) ≤ n := by
    exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnpos : (0 : ℝ) < n := by
    have : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
    exact_mod_cast this
  -- a continuous version of `ψ`
  rw [← map_clampToI hμ.compl_I ψ]
  have hψ'c : Continuous (clampToI ψ) := continuous_clampToI hψL.continuousOn
  have hψ'I : MapsTo (clampToI ψ) AnalyticESC.I AnalyticESC.I := mapsTo_clampToI hψI
  have hψ'L : BiLipOn (clampToI ψ) ε ε⁻¹ := hψL.clampToI
  have hθP : IsProbabilityMeasure (μ.map (clampToI ψ)) := inferInstance
  have hθI : (μ.map (clampToI ψ)) AnalyticESC.Iᶜ = 0 := by
    rw [Measure.map_apply hψ'c.measurable measurableSet_Icc.compl]
    have : clampToI ψ ⁻¹' AnalyticESC.Iᶜ = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
        not_not]
      exact clampToI_mem hψI x
    rw [this, measure_empty]
  have hνnorm : ∀ᵐ q ∂ν, ‖q‖ ≤ ε⁻¹ := hνgood.mono fun q hq => hq.1
  have hB := hN₂ n hn2 ν hν hνnorm hνent _ hθP hθI (hballs _ hψ'c hψ'I hψ'L)
  have hA2 := hN₁ n hn1 _ hψ'c hψ'I hψ'L
  have hA1 := fun i => hM₄ m hmM₄ i _ hψ'c hψ'I hψ'L
  generalize μ.map (clampToI ψ) = θ at hθP hθI hB hA2 hA1 ⊢
  have hθIae : ∀ᵐ x ∂θ, x ∈ AnalyticESC.I := ae_mem_of_compl_null hθI
  have h38 := hC₈ ν hν hνnorm θ hθP hθI n m hm1
  have hfθ : ∀ i, FiniteLabels θ (cellIdx i) := fun i =>
    finiteLabels_cellIdx_comp (F := id) i hθIae
  -- the hypothesis of Hochman's theorem from Corollary 3.7
  have hA2' : (1 - ε₇) * n < ∑ i ∈ Finset.range n, cavg θ (cellIdx i) (fun τ =>
      if 1 - ε₇ < levelProb τ i m
        (fun j x => dyadicEntropy (component τ j x) (j + L₀) / L₀ < 1 - ε'') then 1 else 0) := by
    refine hA2.trans_le (Finset.sum_le_sum fun i _ => cavg_mono (hfθ i) fun c' hc' => ?_)
    have := comp_isProbabilityMeasure hc'
    have hmono := levelProb_mono (comp θ (cellIdx i) c') i m
      (P := fun j y => |dyadicEntropy (component (comp θ (cellIdx i) c') j y) (j + L₀) / L₀ - d|
        < ε₇)
      (Q := fun j y => dyadicEntropy (component (comp θ (cellIdx i) c') j y) (j + L₀) / L₀ <
        1 - ε'') fun j y hy => by
          rw [abs_lt] at hy
          linarith [hy.2]
    by_cases h1 : 1 - ε₇ < levelProb (comp θ (cellIdx i) c') i m
        (fun j y => |dyadicEntropy (component (comp θ (cellIdx i) c') j y) (j + L₀) / L₀ - d|
          < ε₇)
    · have h2 := h1.trans_le hmono
      simp only [h1, h2, ↓reduceIte, le_refl]
    · simp only [h1, ↓reduceIte]
      split_ifs <;> norm_num
  -- the bound at each level, and the sum over the levels
  have hlevel := fun i (_ : i ∈ Finset.range n) => level_bound (ν := ν) (θ := θ) (i := i)
    (K := K) (ε₀ := ε₀) hd1 hε hm1 hδ0 hρH hε''0 hε''1.le hε''ε hε''ε₀ hmCL hmCs hνgood hθIae
    (hA1 i) (fun hiK => hlin m i hiK) (fun hi1 => hNH m hmNH i hi1)
  have hsum := Finset.sum_le_sum hlevel
  rw [Finset.sum_sub_distrib] at hsum
  have hb := sum_bracket n d δ ρH
    (fun i => cavg ν (cellIdxVec i)
      (fun ρ => θ.real {x | ε₀ < dyadicEntropy (actPoint ρ x) (i + m) / m}))
    (fun i => cavg θ (cellIdx i) (fun τ => if 1 - ε₇ < levelProb τ i m
      (fun j x => dyadicEntropy (component τ j x) (j + L₀) / L₀ < 1 - ε'') then 1 else 0))
  rw [hb] at hsum
  have hind := sum_ite_lt_le n (m + K) (1 + ρH) (by positivity)
  push_cast at hind
  refine final_arith hnpos hm0 hρH hε₀ ?_ hB hA2' hδε₀ hδρ hε₇ε₀ hmC₈ (hN₃.trans hn3)
  linarith

end Theorem31

/-- Theorem 3.1 of Rapaport (arXiv:2412.16753v2) for the self-conformal measure of a system
satisfying `AnalyticESC.RapaportHyp`, from Hochman's entropy growth theorem. -/
theorem entropyIncreasePoly (hHG : HochmanEntropyGrowth) {N : ℕ} [NeZero N]
    {φ : Fin N → ℝ → ℝ} (hφ : AnalyticESC.RapaportHyp φ) {p : Fin N → ℝ}
    (hp : AnalyticESC.IsProbVec p) : EntropyIncreasePoly φ p hp := by
  intro d hd hd1 k _ ε hε _
  obtain ⟨ρ, hρ, N₀, h⟩ := entropyIncrease_of_structure hHG (scStructure_selfConformal hφ hp) hd
    hd1 k hε
  exact ⟨ρ, hρ, N₀, fun n hn ν hν hνg hνe ψ hψI hψd hψb =>
    h n hn ν hν hνg hνe ψ hψI (biLipOn_of_hasDerivWithinAt hψd hψb)⟩

end FractalGeometry.Rapaport.Analytic
