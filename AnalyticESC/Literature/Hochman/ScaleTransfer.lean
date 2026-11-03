module

public import AnalyticESC.Literature.Hochman.Entropy

@[expose] public section

/-!
# From uniformity at a large scale to uniformity at a small scale

If a level-`q` component `θ_{x,q}` has almost full entropy at a large scale `M`, then for most
levels `q ≤ j < q + M` most of its subcomponents `θ_{y,j}` have almost full entropy at a smaller
scale `m`. Integrated against `θ` and summed over levels, this bounds the mass of components that
are almost uniform at scale `M` by the mass of components that are almost uniform at scale `m`.
This is Hochman's Lemma 3.4 (global entropy from local entropy) applied inside a component,
combined with Markov's inequality, as in his Lemma 3.7 (Hochman, *On self-similar sets with
overlaps and inverse theorems for entropy*, Ann. of Math. 180 (2014), Sections 3.2 and 3.3).

## Main declarations

* `measurableSet_setOf_component`: properties of components define measurable sets.
* `half_le_sum_component_uniform`: the pointwise statement for one component.
* `measureReal_uniform_le`: `θ(H_M(θ_{x,q}) > 1 - a) ≤ (2/M) ∑_{r<M} θ(H_m(θ_{y,q+r}) ≥ 1 - ε)`
  for `a ≤ ε/4` and `4m ≤ εM`.
* `sum_measureReal_uniform_le`: the version summed over the levels `i ≤ q < i + n`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Hochman.ScaleTransfer`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Hochman

open MeasureTheory Set FractalGeometry.SelfConformal
open scoped ENNReal

/-- A property of the level-`n` component defines a measurable set. -/
theorem measurableSet_setOf_component (θ : Measure ℝ) (n : ℕ) (P : Measure ℝ → Prop) :
    MeasurableSet {x | P (component θ n x)} :=
  (measurable_cellIdx n) (MeasurableSet.of_discrete (s := {k | P (componentAt θ n k)}))

/-- The function `x ↦ θ_{x,n}(s)` is integrable. -/
theorem integrable_component_real (θ : Measure ℝ) [IsFiniteMeasure θ] (n : ℕ) (s : Set ℝ) :
    Integrable (fun x => (component θ n x).real s) θ := by
  refine Integrable.of_bound
    (measurable_comp_cellIdx n fun k => (componentAt θ n k).real s).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, Measure.real, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top (component_apply_le_one θ n x s)

/-- The set of points whose level-`j` component has entropy at least `1 - ε` at scale `m`. -/
def uniformSet (θ : Measure ℝ) (ε : ℝ) (m j : ℕ) : Set ℝ :=
  {y | 1 - ε ≤ dyadicEntropy (component θ j y) (j + m) / m}

/-- `uniformSet` is measurable. -/
theorem measurableSet_uniformSet (θ : Measure ℝ) (ε : ℝ) (m j : ℕ) :
    MeasurableSet (uniformSet θ ε m j) :=
  measurableSet_setOf_component θ j fun ρ => 1 - ε ≤ dyadicEntropy ρ (j + m) / m

/-- One level inside a component: for `q ≤ j`, the entropy gained by `θ_{x,q}` from `𝒟_j` to
`𝒟_{j+m}` is at most `m (1 - ε + ε θ_{x,q}(U_j))`, where `U_j` is the set of points whose
level-`j` component of `θ` has entropy at least `1 - ε` at scale `m`. -/
theorem dyadicEntropy_component_add_sub_le (θ : Measure ℝ) [IsFiniteMeasure θ] (ε : ℝ) {m : ℕ}
    (hm : 0 < m) {q j : ℕ} (hqj : q ≤ j) {x : ℝ} (hx : θ (cellOf q x) ≠ 0) :
    dyadicEntropy (component θ q x) (j + m) - dyadicEntropy (component θ q x) j ≤
      m * (1 - ε + ε * (component θ q x).real (uniformSet θ ε m j)) := by
  set ρ := component θ q x
  have hρ : IsProbabilityMeasure ρ := isProbabilityMeasure_componentAt θ hx
  have hρC : ρ (cellOf q x)ᶜ = 0 := componentAt_compl θ q _
  have hρab := componentAt_compl_Icc θ q (cellIdx q x)
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  rw [dyadicEntropy_add_sub_eq_integral ρ hρab j m]
  have hae : ∀ᵐ y ∂ρ, dyadicEntropy (component ρ j y) (j + m) =
      dyadicEntropy (component θ j y) (j + m) := by
    have hmem : ∀ᵐ y ∂ρ, y ∈ cellOf q x := by
      rw [ae_iff]
      exact hρC
    filter_upwards [hmem] with y hy
    rw [component_component θ hqj hy hx]
  rw [integral_congr_ae hae]
  set U := uniformSet θ ε m j
  have hU : MeasurableSet U := measurableSet_uniformSet θ ε m j
  have hbound : ∀ y, dyadicEntropy (component θ j y) (j + m) ≤
      m * (1 - ε) + m * ε * U.indicator 1 y := by
    intro y
    have hle : dyadicEntropy (component θ j y) (j + m) ≤ m :=
      dyadicEntropy_componentAt_le θ j _ m
    by_cases hy : y ∈ U
    · rw [Set.indicator_of_mem hy, Pi.one_apply]
      linarith
    · rw [Set.indicator_of_notMem hy]
      have h : dyadicEntropy (component θ j y) (j + m) / m < 1 - ε := not_le.1 hy
      rw [div_lt_iff₀ hm'] at h
      linarith
  have hint_left : Integrable (fun y => dyadicEntropy (component θ j y) (j + m)) ρ := by
    refine Integrable.of_bound
      (measurable_comp_cellIdx j fun k =>
        dyadicEntropy (componentAt θ j k) (j + m)).aestronglyMeasurable m
      (Filter.Eventually.of_forall fun y => ?_)
    have h0 : 0 ≤ dyadicEntropy (component θ j y) (j + m) :=
      dyadicEntropy_componentAt_nonneg θ j _ _
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact dyadicEntropy_componentAt_le θ j _ m
  have hint_right : Integrable (fun y => m * (1 - ε) + m * ε * U.indicator 1 y) ρ :=
    (integrable_const _).add ((integrable_indicator_iff hU).2 (integrable_const 1).integrableOn
      |>.const_mul _)
  calc ∫ y, dyadicEntropy (component θ j y) (j + m) ∂ρ
      ≤ ∫ y, (m * (1 - ε) + m * ε * U.indicator 1 y) ∂ρ :=
        integral_mono hint_left hint_right hbound
    _ = m * (1 - ε + ε * ρ.real U) := by
        rw [integral_add (integrable_const _)
          (((integrable_indicator_iff hU).2 (integrable_const 1).integrableOn).const_mul _),
          integral_const, integral_const_mul, integral_indicator_one hU, probReal_univ,
          smul_eq_mul, one_mul]
        ring

/-- A component with almost full entropy at scale `M` has, summed over the levels
`q ≤ q + r < q + M`, mass at least `M/2` on the sets `U_{q+r}` of points whose component has
entropy at least `1 - ε` at scale `m`, provided `a ≤ ε/4` and `4m ≤ εM` (Hochman's Lemma 3.4
inside the component). -/
theorem half_le_sum_component_uniform (θ : Measure ℝ) [IsFiniteMeasure θ] {ε a : ℝ}
    (hε : 0 < ε) (ha : a ≤ ε / 4) {m M : ℕ} (hm : 0 < m) (hmM : 4 * (m : ℝ) ≤ ε * M) {q : ℕ}
    {x : ℝ} (hx : θ (cellOf q x) ≠ 0)
    (hH : 1 - a < dyadicEntropy (component θ q x) (q + M) / M) :
    (M : ℝ) / 2 ≤
      ∑ r ∈ Finset.range M, (component θ q x).real (uniformSet θ ε m (q + r)) := by
  set ρ := component θ q x
  have hρ : IsProbabilityMeasure ρ := isProbabilityMeasure_componentAt θ hx
  have hρab := componentAt_compl_Icc θ q (cellIdx q x)
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hM' : (0 : ℝ) < M := by
    by_contra h
    have h0 : (M : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg M)
    rw [h0, mul_zero] at hmM
    linarith
  set A : ℕ → ℝ := fun t => dyadicEntropy ρ (q + t)
  set S := ∑ r ∈ Finset.range M, ρ.real (uniformSet θ ε m (q + r))
  -- each window gains at most `m (1 - ε + ε ρ(U))`
  have hwin : ∀ r ∈ Finset.range M,
      A (r + m) - A r ≤ m * (1 - ε + ε * ρ.real (uniformSet θ ε m (q + r))) := by
    intro r _
    have h := dyadicEntropy_component_add_sub_le θ ε hm (Nat.le_add_right q r) hx
    simp only [A, ← add_assoc]
    exact h
  have hsum_le : ∑ r ∈ Finset.range M, (A (r + m) - A r) ≤ m * (M * (1 - ε) + ε * S) := by
    calc ∑ r ∈ Finset.range M, (A (r + m) - A r)
        ≤ ∑ r ∈ Finset.range M, m * (1 - ε + ε * ρ.real (uniformSet θ ε m (q + r))) :=
          Finset.sum_le_sum hwin
      _ = m * (M * (1 - ε) + ε * S) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, ← Finset.mul_sum]
  -- telescoping: the windows add up to at least `m A(M) - m²`
  have hA0 : A 0 = 0 := by
    simp only [A, add_zero]
    exact dyadicEntropy_eq_zero_of_cell ρ (componentAt_compl θ q _)
  have hwin_eq := ExactOverlaps.Entropy.sum_window_differences A M m
  have hsum_ge : (m : ℝ) * A M - m * m ≤ ∑ r ∈ Finset.range M, (A (r + m) - A r) := by
    rw [hwin_eq]
    have hterm : ∀ s ∈ Finset.range m, A M - m ≤ A (M + s) - A s := by
      intro s hs
      have h1 : A M ≤ A (M + s) := by
        simp only [A, ← add_assoc]
        exact dyadicEntropy_le_add ρ hρab (q + M) s
      have h2 : A s ≤ s := by
        have h := dyadicEntropy_add_sub_le ρ hρab q s
        have h0 : dyadicEntropy ρ q = 0 := by simpa [A] using hA0
        simp only [A]
        linarith
      have h3 : (s : ℝ) ≤ m := by exact_mod_cast (Finset.mem_range.1 hs).le
      linarith
    calc (m : ℝ) * A M - m * m = ∑ s ∈ Finset.range m, (A M - m) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
      _ ≤ _ := Finset.sum_le_sum hterm
  -- combine with `A(M) > (1 - a) M`
  have hAM : (1 - a) * M < A M := by
    have h := hH
    rw [lt_div_iff₀ hM'] at h
    exact h
  have key : (m : ℝ) * ((1 - a) * M - m) < m * (M * (1 - ε) + ε * S) := by
    have := mul_lt_mul_of_pos_left hAM hm'
    nlinarith
  have key' : (1 - a) * M - m < M * (1 - ε) + ε * S := lt_of_mul_lt_mul_left key hm'.le
  have hεS : ε * (M / 2) ≤ ε * S := by nlinarith
  exact le_of_mul_le_mul_left hεS hε

/-- `θ(H_M(θ_{x,q}) > 1 - a) ≤ (2/M) ∑_{r<M} θ(U_{q+r})` for a probability measure `θ`, where
`U_j` is the set of points whose level-`j` component has entropy at least `1 - ε` at scale `m`,
provided `0 < ε`, `a ≤ ε/4`, `a < 1` and `4m ≤ εM` (Hochman's Lemmas 3.4 and 3.7). -/
theorem measureReal_uniform_le (θ : Measure ℝ) [IsProbabilityMeasure θ] {ε a : ℝ}
    (hε : 0 < ε) (ha : a ≤ ε / 4) (ha1 : a < 1) {m M : ℕ} (hm : 0 < m)
    (hmM : 4 * (m : ℝ) ≤ ε * M) (q : ℕ) :
    θ.real {x | 1 - a < dyadicEntropy (component θ q x) (q + M) / M} ≤
      (2 / M) * ∑ r ∈ Finset.range M, θ.real (uniformSet θ ε m (q + r)) := by
  set B := {x | 1 - a < dyadicEntropy (component θ q x) (q + M) / M}
  have hB : MeasurableSet B :=
    measurableSet_setOf_component θ q fun ρ => 1 - a < dyadicEntropy ρ (q + M) / M
  have hM' : (0 : ℝ) < M := by
    by_contra h
    have h0 : (M : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg M)
    rw [h0, mul_zero] at hmM
    have : (0 : ℝ) < m := Nat.cast_pos.2 hm
    linarith
  set h : ℝ → ℝ := fun x =>
    ∑ r ∈ Finset.range M, (component θ q x).real (uniformSet θ ε m (q + r))
  have hint : Integrable h θ :=
    integrable_finsetSum _ fun r _ => integrable_component_real θ q _
  have hint_eq : ∫ x, h x ∂θ = ∑ r ∈ Finset.range M, θ.real (uniformSet θ ε m (q + r)) := by
    rw [integral_finsetSum _ fun r _ => integrable_component_real θ q _]
    exact Finset.sum_congr rfl fun r _ =>
      integral_component_real θ q (measurableSet_uniformSet θ ε m (q + r))
  have hpt : ∀ x, (M : ℝ) / 2 * B.indicator 1 x ≤ h x := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
      have hcell : θ (cellOf q x) ≠ 0 := by
        intro h0
        have hx' : 1 - a < dyadicEntropy (component θ q x) (q + M) / M := hx
        rw [component_eq_componentAt, componentAt_eq_zero θ h0, dyadicEntropy_zero,
          zero_div] at hx'
        linarith
      exact half_le_sum_component_uniform θ hε ha hm hmM hcell hx
    · rw [Set.indicator_of_notMem hx, mul_zero]
      exact Finset.sum_nonneg fun r _ => measureReal_nonneg
  have hmono := integral_mono
    (((integrable_indicator_iff hB).2 (integrable_const 1).integrableOn).const_mul ((M : ℝ) / 2))
    hint hpt
  rw [integral_const_mul, integral_indicator_one hB, hint_eq] at hmono
  rw [div_mul_eq_mul_div, le_div_iff₀ hM']
  linarith

/-- Summed over the levels `i ≤ i + p < i + n`: the total mass of components almost uniform at
scale `M` is at most twice the total mass of components almost uniform at scale `m` over the
levels `i ≤ j ≤ i + n`, plus `2M`. -/
theorem sum_measureReal_uniform_le (θ : Measure ℝ) [IsProbabilityMeasure θ] {ε a : ℝ}
    (hε : 0 < ε) (ha : a ≤ ε / 4) (ha1 : a < 1) {m M : ℕ} (hm : 0 < m)
    (hmM : 4 * (m : ℝ) ≤ ε * M) (i n : ℕ) :
    ∑ p ∈ Finset.range n,
        θ.real {x | 1 - a < dyadicEntropy (component θ (i + p) x) (i + p + M) / M} ≤
      2 * ∑ j ∈ Finset.Icc i (i + n), θ.real (uniformSet θ ε m j) + 2 * M := by
  set u : ℕ → ℝ := fun j => θ.real (uniformSet θ ε m j)
  have hu0 : ∀ j, 0 ≤ u j := fun j => measureReal_nonneg
  have hu1 : ∀ j, u j ≤ 1 := fun j => measureReal_le_one
  have hM' : (0 : ℝ) < M := by
    by_contra h
    have h0 : (M : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg M)
    rw [h0, mul_zero] at hmM
    have : (0 : ℝ) < m := Nat.cast_pos.2 hm
    linarith
  -- each level is bounded through the transfer lemma
  have hstep : ∀ p ∈ Finset.range n,
      θ.real {x | 1 - a < dyadicEntropy (component θ (i + p) x) (i + p + M) / M} ≤
        (2 / M) * ∑ r ∈ Finset.range M, u (i + r + p) := by
    intro p _
    have h := measureReal_uniform_le θ hε ha ha1 hm hmM (i + p)
    refine h.trans_eq ?_
    congr 1
    exact Finset.sum_congr rfl fun r _ => by simp only [u]; ring_nf
  -- the double sum is at most `M` times a sum over `[i, i + n + M)`
  have hinner : ∀ r ∈ Finset.range M,
      ∑ p ∈ Finset.range n, u (i + r + p) ≤ ∑ j ∈ Finset.Ico i (i + n + M), u j := by
    intro r hr
    rw [Finset.mem_range] at hr
    have heq : ∑ p ∈ Finset.range n, u (i + r + p) =
        ∑ j ∈ Finset.Ico (i + r) (i + r + n), u j := by
      rw [Finset.sum_Ico_eq_sum_range, show i + r + n - (i + r) = n by omega]
    rw [heq]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => hu0 j
    intro j hj
    rw [Finset.mem_Ico] at hj ⊢
    omega
  have hsplit : ∑ j ∈ Finset.Ico i (i + n + M), u j ≤
      ∑ j ∈ Finset.Icc i (i + n), u j + M := by
    have hM1 : 1 ≤ M := Nat.cast_pos.1 hM'
    rw [← Finset.sum_Ico_consecutive u (show i ≤ i + n + 1 by omega)
      (show i + n + 1 ≤ i + n + M by omega)]
    have h1 : Finset.Ico i (i + n + 1) = Finset.Icc i (i + n) := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [h1]
    have h2 : ∑ j ∈ Finset.Ico (i + n + 1) (i + n + M), u j ≤ M := by
      calc ∑ j ∈ Finset.Ico (i + n + 1) (i + n + M), u j
          ≤ ∑ j ∈ Finset.Ico (i + n + 1) (i + n + M), (1 : ℝ) :=
            Finset.sum_le_sum fun j _ => hu1 j
        _ = ((i + n + M - (i + n + 1) : ℕ) : ℝ) := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
        _ ≤ M := by exact_mod_cast (by omega : i + n + M - (i + n + 1) ≤ M)
    linarith
  calc ∑ p ∈ Finset.range n,
        θ.real {x | 1 - a < dyadicEntropy (component θ (i + p) x) (i + p + M) / M}
      ≤ ∑ p ∈ Finset.range n, (2 / M) * ∑ r ∈ Finset.range M, u (i + r + p) :=
        Finset.sum_le_sum hstep
    _ = (2 / M) * ∑ r ∈ Finset.range M, ∑ p ∈ Finset.range n, u (i + r + p) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (2 / M) * ∑ r ∈ Finset.range M, ∑ j ∈ Finset.Ico i (i + n + M), u j := by
        gcongr with r hr
        exact hinner r hr
    _ = 2 * ∑ j ∈ Finset.Ico i (i + n + M), u j := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
    _ ≤ 2 * (∑ j ∈ Finset.Icc i (i + n), u j + M) := by gcongr
    _ = _ := by ring

end FractalGeometry.Hochman
