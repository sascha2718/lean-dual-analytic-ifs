module

public import AnalyticESC.Literature.Rapaport.Analytic.Setup
public import AnalyticESC.Literature.Rapaport.Analytic.Young
public import AnalyticESC.Literature.Hochman.Cells

@[expose] public section

/-!
# Uniform entropy dimension of `C¹` images of `μ`

Section 3.2 of A. Rapaport, *Dimension of self-conformal measures associated to an exponentially
separated analytic IFS on ℝ*, arXiv:2412.16753v2: Corollary 3.5, Propositions 3.3 and 3.6 and
Corollary 3.7, for a measure with the structure `SCStructure` and maps `ψ : I → I` with
`ε |x - y| ≤ |ψ x - ψ y| ≤ ε⁻¹ |x - y|`.

Corollary 3.5 is proved directly from the decomposition `μ = ∑_u w_u g_u μ` and the absence of
atoms, by the argument of Lemma 3.4 applied to the neighbourhood of the boundaries of the dyadic
cells. Proposition 3.6 is proved from Proposition 3.3, Hochman's Lemma 3.4 and the upper bound of
(2.9) by a pointwise inequality averaged over the components, and Corollary 3.7 from
Proposition 3.6 by averaging over the levels, using that components of components are components.

## Main declarations

* `exists_forall_measure_closedBall_le`, `small_balls`: small balls have uniformly small mass.
* `boundary_small`: Corollary 3.5.
* `sum_weight_mul_ent_comp_le`: concavity of entropy for the components of a finite mixture.
* `entropy_piece_ge`, `mem_boundary_of_not_single_cell`: the pieces `ψ g_u μ` of the
  decomposition.
* `prop33`: Proposition 3.3.
* `avg_component_entropy_le`, `prop36`: Proposition 3.6.
* `measureReal_component_comp_eq`, `cor37`: Corollary 3.7.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.UniformEntropyDimension`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic

open MeasureTheory ProbabilityTheory Set Filter Topology FractalGeometry.SelfConformal
open scoped ENNReal

/-- A finite measure on `ℝ` carried by `I` without atoms gives uniformly small mass to small
closed balls. -/
theorem exists_forall_measure_closedBall_le {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hI : μ AnalyticESC.Iᶜ = 0) (hμ0 : ∀ x, μ {x} = 0) {c : ℝ≥0∞} (hc : 0 < c) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : ℝ, μ (Metric.closedBall x η) ≤ c := by
  have hr : ∀ t : AnalyticESC.I, ∃ r : ℝ, 0 < r ∧ μ (Metric.ball (t : ℝ) r) ≤ c := by
    intro t
    have h := tendsto_measure_cthickening_of_isClosed (μ := μ) (s := {(t : ℝ)})
      ⟨1, one_pos, measure_ne_top _ _⟩ isClosed_singleton
    rw [hμ0] at h
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), μ (Metric.cthickening r {(t : ℝ)}) < c :=
      (h.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hc)
    obtain ⟨r, hrc, hr0⟩ := (hev.and self_mem_nhdsWithin).exists
    refine ⟨r, hr0, (measure_mono ?_).trans hrc.le⟩
    rw [Metric.cthickening_singleton _ (le_of_lt hr0)]
    exact Metric.ball_subset_closedBall
  choose r hr0 hrc using hr
  obtain ⟨δ₀, hδ₀, hleb⟩ := lebesgue_number_lemma_of_metric (s := AnalyticESC.I)
    (c := fun t : AnalyticESC.I => Metric.ball (t : ℝ) (r t)) isCompact_Icc
    (fun _ => Metric.isOpen_ball) fun x hx =>
      Set.mem_iUnion.2 ⟨⟨x, hx⟩, Metric.mem_ball_self (hr0 _)⟩
  refine ⟨δ₀ / 3, by positivity, fun x => ?_⟩
  by_cases hne : (Metric.closedBall x (δ₀ / 3) ∩ AnalyticESC.I).Nonempty
  · obtain ⟨y, hyx, hyI⟩ := hne
    obtain ⟨t, ht⟩ := hleb y hyI
    refine (measure_mono fun z hz => ht ?_).trans (hrc t)
    rw [Metric.mem_ball]
    rw [Metric.mem_closedBall] at hz hyx
    calc dist z y ≤ dist z x + dist y x := dist_triangle_right _ _ _
      _ ≤ δ₀ / 3 + δ₀ / 3 := add_le_add hz hyx
      _ < δ₀ := by linarith
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    refine (measure_mono_null (fun z hz hzI => ?_) hI).le.trans (zero_le)
    have : z ∈ Metric.closedBall x (δ₀ / 3) ∩ AnalyticESC.I := ⟨hz, hzI⟩
    rw [hne] at this
    exact this

/-- Balls of radius `δ` have uniformly small mass under the images `ψμ`. -/
theorem small_balls {μ : Measure ℝ} (hμ : SCStructure μ) {ε : ℝ} (hε : 0 < ε) {c : ℝ}
    (hc : 0 < c) : ∃ δ : ℝ, 0 < δ ∧ ∀ ψ : ℝ → ℝ, Continuous ψ →
    MapsTo ψ AnalyticESC.I AnalyticESC.I → BiLipOn ψ ε ε⁻¹ →
    ∀ x, (μ.map ψ).real (Metric.closedBall x δ) ≤ c := by
  have := hμ.isProb
  obtain ⟨η, hη, hball⟩ := exists_forall_measure_closedBall_le hμ.compl_I hμ.noAtoms
    (ENNReal.ofReal_pos.2 hc)
  refine ⟨η * ε / 2, by positivity, fun ψ hψc _ hψL x => ?_⟩
  rw [map_measureReal_apply hψc.measurable Metric.isClosed_closedBall.measurableSet]
  have hle : μ (ψ ⁻¹' Metric.closedBall x (η * ε / 2)) ≤ ENNReal.ofReal c := by
    by_cases hne : (ψ ⁻¹' Metric.closedBall x (η * ε / 2) ∩ AnalyticESC.I).Nonempty
    · obtain ⟨y₀, hy₀, hy₀I⟩ := hne
      calc μ (ψ ⁻¹' Metric.closedBall x (η * ε / 2))
          ≤ μ (Metric.closedBall y₀ η ∪ AnalyticESC.Iᶜ) := by
            refine measure_mono fun y hy => ?_
            by_cases hyI : y ∈ AnalyticESC.I
            · left
              rw [Metric.mem_closedBall, Real.dist_eq]
              have h1 := (hψL y hyI y₀ hy₀I).1
              rw [Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq] at hy hy₀
              have h2 : |ψ y - ψ y₀| ≤ η * ε := by
                calc |ψ y - ψ y₀| = |(ψ y - x) - (ψ y₀ - x)| := by ring_nf
                  _ ≤ |ψ y - x| + |ψ y₀ - x| := abs_sub _ _
                  _ ≤ η * ε / 2 + η * ε / 2 := add_le_add hy hy₀
                  _ = η * ε := by ring
              have h3 : ε * |y - y₀| ≤ ε * η := by linarith
              exact le_of_mul_le_mul_left h3 hε
            · exact Or.inr hyI
        _ ≤ μ (Metric.closedBall y₀ η) + μ AnalyticESC.Iᶜ := measure_union_le _ _
        _ ≤ ENNReal.ofReal c := by rw [hμ.compl_I, add_zero]; exact hball y₀
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      refine (measure_mono_null (fun z hz hzI => ?_) hμ.compl_I).le.trans (zero_le)
      have : z ∈ ψ ⁻¹' Metric.closedBall x (η * ε / 2) ∩ AnalyticESC.I := ⟨hz, hzI⟩
      rw [hne] at this
      exact this
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hc.le hle

/-! ### Images of `μ` under the maps of the decomposition -/

/-- Pushing the decomposition `μ = ∑ w_u g_u μ` forward by `ψ`. -/
theorem map_eq_sum_map_comp {μ : Measure ℝ} {K : ℕ} {w : Fin K → ℝ} {g : Fin K → ℝ → ℝ}
    (hμ : μ = ∑ u, ENNReal.ofReal (w u) • μ.map (g u)) (hg : ∀ u, Continuous (g u))
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    μ.map ψ = ∑ u, ENNReal.ofReal (w u) • μ.map (ψ ∘ g u) := by
  ext s hs
  conv_lhs => rw [hμ]
  rw [Measure.map_apply hψ.measurable hs, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Measure.map_apply (hg u).measurable (hψ.measurable hs),
    Measure.map_apply (hψ.comp (hg u)).measurable hs]
  rfl

/-- The lower bi-Lipschitz bound `a |x - y| ≤ |f x - f y|` on `I` controls the dyadic entropy of
`f μ` from below: `H(μ, 𝒟_{n'}) ≤ H(f μ, 𝒟_n) + log (2^{n'+1} / (a 2^n) + 2)` (nats). -/
theorem ent_le_ent_map_of_lower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hI : μ AnalyticESC.Iᶜ = 0) {f : ℝ → ℝ} (hf : Continuous f)
    (hfI : MapsTo f AnalyticESC.I AnalyticESC.I) {a : ℝ} (ha : 0 < a)
    (hlow : ∀ x ∈ AnalyticESC.I, ∀ y ∈ AnalyticESC.I, a * |x - y| ≤ |f x - f y|) (n n' : ℕ) :
    ent μ (cellIdx n') ≤ ent (μ.map f) (cellIdx n) +
      Real.log (2 ^ n' * (2 * (1 / (a * 2 ^ n))) + 2) := by
  have hIae : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1 := ae_mem_of_compl_null hI
  have hfin1 : FiniteLabels μ (cellIdx n' ∘ id) := finiteLabels_cellIdx_comp n' hIae
  have hfin2 : FiniteLabels μ (cellIdx n ∘ f) := finiteLabels_cellIdx_comp n
    (by filter_upwards [hIae] with x hx; exact hfI hx)
  have key := ent_cellIdx_comp_le (θ := μ) (F := id) (g := cellIdx n ∘ f) measurable_id
    ((measurable_cellIdx n).comp hf.measurable) n' hfin1 hfin2 measurableSet_Icc hI
    (r := 1 / (a * 2 ^ n)) (by positivity) fun x hx y hy hxy => by
      have h1 := abs_sub_lt_of_cellIdx_eq hxy
      have h2 := hlow x hx y hy
      simp only [id]
      rw [le_div_iff₀ (by positivity)]
      have : a * |x - y| ≤ 1 / 2 ^ n := h2.trans h1.le
      rw [le_div_iff₀ (by positivity)] at this
      linarith
  rw [ent_map hf.measurable (measurable_cellIdx n)]
  exact key

/-- For a decomposition at level `i + kk` and an admissible `ψ`, the maps `ψ ∘ g_u` are
bi-Lipschitz on `I` with constants `ε C⁻¹ 2^{-(i+kk)}` and `ε⁻¹ C 2^{-(i+kk)}`. -/
theorem biLipOn_comp_decomp {ψ g : ℝ → ℝ} {ε C : ℝ} (hε : 0 < ε) {N : ℕ}
    (hψL : BiLipOn ψ ε ε⁻¹) (hg : BiLipOn g (C⁻¹ / 2 ^ N) (C / 2 ^ N))
    (hgI : MapsTo g AnalyticESC.I AnalyticESC.I) :
    BiLipOn (ψ ∘ g) (ε * (C⁻¹ / 2 ^ N)) (ε⁻¹ * (C / 2 ^ N)) :=
  hψL.comp hg hgI hε.le (inv_pos.2 hε).le

/-! ### Corollary 3.5: the boundaries of dyadic cells carry little mass -/

/-- Corollary 3.5 of Rapaport: the `δ₁ 2^{-i}`-neighbourhood of the boundaries of the level-`i`
dyadic cells has `ψμ`-mass at most `c`. -/
theorem boundary_small {μ : Measure ℝ} (hμ : SCStructure μ) {ε : ℝ} (hε : 0 < ε) {c : ℝ}
    (hc : 0 < c) : ∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ 1 / 4 ∧ ∀ ψ : ℝ → ℝ, Continuous ψ →
    MapsTo ψ AnalyticESC.I AnalyticESC.I → BiLipOn ψ ε ε⁻¹ → ∀ i : ℕ,
    (μ.map ψ).real (⋃ k : ℤ, Metric.closedBall ((k : ℝ) / 2 ^ i) (δ₁ / 2 ^ i)) ≤ c := by
  have := hμ.isProb
  obtain ⟨C, hC, hdec⟩ := hμ.decomp
  obtain ⟨η, hη, hball⟩ := exists_forall_measure_closedBall_le hμ.compl_I hμ.noAtoms
    (ENNReal.ofReal_pos.2 hc)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (4 * C * ε⁻¹) (by norm_num : (1 : ℝ) < 2)
  have hC0 : 0 < C := by linarith
  set δ₁ : ℝ := min (1 / 4) (η * ε / (2 * C * 2 ^ m)) with hδ₁
  refine ⟨δ₁, lt_min (by norm_num) (by positivity), min_le_left _ _,
    fun ψ hψc hψI hψL i => ?_⟩
  obtain ⟨K, w, g, hw0, hw1, hμeq, hg⟩ := hdec (i + m)
  set B := ⋃ k : ℤ, Metric.closedBall ((k : ℝ) / 2 ^ i) (δ₁ / 2 ^ i)
  have hBm : MeasurableSet B :=
    MeasurableSet.iUnion fun k => Metric.isClosed_closedBall.measurableSet
  -- each piece gives mass at most `c` to `B`
  have hpiece : ∀ u, μ ((ψ ∘ g u) ⁻¹' B) ≤ ENNReal.ofReal c := by
    intro u
    obtain ⟨hgc, hgI, hgL⟩ := hg u
    have hL := biLipOn_comp_decomp hε hψL hgL hgI
    by_cases hne : ((ψ ∘ g u) ⁻¹' B ∩ AnalyticESC.I).Nonempty
    · obtain ⟨y₀, hy₀B, hy₀I⟩ := hne
      obtain ⟨k₀, hk₀⟩ := Set.mem_iUnion.1 hy₀B
      have hsub : (ψ ∘ g u) ⁻¹' B ⊆ Metric.closedBall y₀ η ∪ AnalyticESC.Iᶜ := by
        intro y hy
        by_cases hyI : y ∈ AnalyticESC.I
        · left
          obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hy
          rw [Metric.mem_closedBall, Real.dist_eq] at hk hk₀
          obtain ⟨hl, hu⟩ := hL y hyI y₀ hy₀I
          have hyy : |y - y₀| ≤ 1 := by
            rw [abs_le]
            constructor <;> linarith [hyI.1, hyI.2, hy₀I.1, hy₀I.2]
          have h2i : (0 : ℝ) < 2 ^ i := by positivity
          have hbig : ε⁻¹ * (C / 2 ^ (i + m)) ≤ 1 / 4 / 2 ^ i := by
            rw [pow_add]
            have : 4 * C * ε⁻¹ ≤ 2 ^ m := hm.le
            rw [div_div, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
          have hfy : |(ψ ∘ g u) y - (ψ ∘ g u) y₀| ≤ 1 / 4 / 2 ^ i :=
            hu.trans ((mul_le_of_le_one_right (by positivity) hyy).trans hbig)
          -- the two points lie near the same boundary point
          have hkk : k = k₀ := by
            have h3 : |(k : ℝ) / 2 ^ i - (k₀ : ℝ) / 2 ^ i| < 1 / 2 ^ i := by
              have hδ : δ₁ ≤ 1 / 4 := min_le_left _ _
              have e : (k : ℝ) / 2 ^ i - (k₀ : ℝ) / 2 ^ i =
                  -(((ψ ∘ g u) y - k / 2 ^ i)) + ((ψ ∘ g u) y - (ψ ∘ g u) y₀) +
                    ((ψ ∘ g u) y₀ - k₀ / 2 ^ i) := by ring
              rw [e]
              refine (abs_add_three _ _ _).trans_lt ?_
              rw [abs_neg]
              have h4 : δ₁ / 2 ^ i ≤ 1 / 4 / 2 ^ i := by gcongr
              have h5 : (1 : ℝ) / 4 / 2 ^ i + 1 / 4 / 2 ^ i + 1 / 4 / 2 ^ i < 1 / 2 ^ i := by
                have : (0 : ℝ) < 1 / 2 ^ i := by positivity
                calc _ = 3 / 4 * (1 / (2 : ℝ) ^ i) := by ring
                  _ < 1 / 2 ^ i := by linarith
              linarith
            rw [← sub_div, abs_div, abs_of_pos h2i, div_lt_div_iff_of_pos_right h2i] at h3
            have h6 : |((k - k₀ : ℤ) : ℝ)| < 1 := by push_cast; exact h3
            rw [← Int.cast_abs] at h6
            have h7 : |k - k₀| < 1 := by exact_mod_cast h6
            have h8 : |k - k₀| = 0 := by have := abs_nonneg (k - k₀); omega
            have := abs_eq_zero.1 h8
            omega
          rw [hkk] at hk
          have hfy2 : |(ψ ∘ g u) y - (ψ ∘ g u) y₀| ≤ 2 * (δ₁ / 2 ^ i) := by
            have e : (ψ ∘ g u) y - (ψ ∘ g u) y₀ =
                ((ψ ∘ g u) y - k₀ / 2 ^ i) - ((ψ ∘ g u) y₀ - k₀ / 2 ^ i) := by ring
            rw [e]
            refine (abs_sub _ _).trans ?_
            linarith
          rw [Metric.mem_closedBall, Real.dist_eq]
          have ha : 0 < ε * (C⁻¹ / 2 ^ (i + m)) := by positivity
          have h9 : ε * (C⁻¹ / 2 ^ (i + m)) * |y - y₀| ≤ 2 * (δ₁ / 2 ^ i) := hl.trans hfy2
          have hδ2 : δ₁ ≤ η * ε / (2 * C * 2 ^ m) := min_le_right _ _
          have h10 : 2 * (δ₁ / 2 ^ i) ≤ ε * (C⁻¹ / 2 ^ (i + m)) * η := by
            rw [pow_add]
            have : 2 * δ₁ ≤ η * ε / (C * 2 ^ m) := by
              have := mul_le_mul_of_nonneg_left hδ2 (by norm_num : (0 : ℝ) ≤ 2)
              calc 2 * δ₁ ≤ 2 * (η * ε / (2 * C * 2 ^ m)) := this
                _ = η * ε / (C * 2 ^ m) := by field_simp
            calc 2 * (δ₁ / 2 ^ i) = 2 * δ₁ / 2 ^ i := by ring
              _ ≤ η * ε / (C * 2 ^ m) / 2 ^ i := by gcongr
              _ = ε * (C⁻¹ / (2 ^ i * 2 ^ m)) * η := by field_simp
          exact le_of_mul_le_mul_left (h9.trans h10) ha
        · exact Or.inr hyI
      calc μ ((ψ ∘ g u) ⁻¹' B) ≤ μ (Metric.closedBall y₀ η ∪ AnalyticESC.Iᶜ) := measure_mono hsub
        _ ≤ μ (Metric.closedBall y₀ η) + μ AnalyticESC.Iᶜ := measure_union_le _ _
        _ ≤ ENNReal.ofReal c := by rw [hμ.compl_I, add_zero]; exact hball y₀
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      refine (measure_mono_null (fun z hz hzI => ?_) hμ.compl_I).le.trans (zero_le)
      have : z ∈ (ψ ∘ g u) ⁻¹' B ∩ AnalyticESC.I := ⟨hz, hzI⟩
      rw [hne] at this
      exact this
  -- summing over the pieces
  have hθ := map_eq_sum_map_comp hμeq (fun u => (hg u).1) hψc
  have hle : (μ.map ψ) B ≤ ENNReal.ofReal c := by
    rw [hθ, Measure.coe_finsetSum, Finset.sum_apply]
    calc ∑ u, (ENNReal.ofReal (w u) • μ.map (ψ ∘ g u)) B
        = ∑ u, ENNReal.ofReal (w u) * μ ((ψ ∘ g u) ⁻¹' B) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Measure.smul_apply, smul_eq_mul,
            Measure.map_apply (hψc.comp (hg u).1).measurable hBm]
      _ ≤ ∑ u, ENNReal.ofReal (w u) * ENNReal.ofReal c :=
          Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hpiece u) (zero_le)
      _ = ENNReal.ofReal c := by
          rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun u _ => hw0 u, hw1,
            ENNReal.ofReal_one, one_mul]
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hc.le hle

/-! ### Proposition 3.3 -/

/-- Concavity of entropy for the components of a finite mixture:
`∑_u (w_u θ_u(D) / θ(D)) H((θ_u)_D, g) ≤ H(θ_D, g)` for a cell `D = f⁻¹{c}`. -/
theorem sum_weight_mul_ent_comp_le {X : Type*} [MeasurableSpace X] {θ : Measure X}
    [IsProbabilityMeasure θ] {K : ℕ} {w : Fin K → ℝ} {θs : Fin K → Measure X}
    [∀ u, IsProbabilityMeasure (θs u)] (hw0 : ∀ u, 0 ≤ w u)
    (hθ : θ = ∑ u, ENNReal.ofReal (w u) • θs u) {L : Type*} [MeasurableSpace L]
    [MeasurableSingletonClass L] {f : X → L} (hf : Measurable f) {c : L}
    (hc : θ (f ⁻¹' {c}) ≠ 0) {M : Type*} [MeasurableSpace M] [MeasurableSingletonClass M]
    [Countable M] {g : X → M} (hg : Measurable g) (hgfin : FiniteLabels (comp θ f c) g) :
    ∑ u, (w u * (θs u).real (f ⁻¹' {c}) / θ.real (f ⁻¹' {c})) * ent (comp (θs u) f c) g ≤
      ent (comp θ f c) g := by
  classical
  have hD := hf (measurableSet_singleton c)
  set D := f ⁻¹' {c}
  have ht : 0 < θ.real D := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hc (measure_ne_top _ _)
  have := comp_isProbabilityMeasure hc (f := f)
  set θs' : Fin K → Measure X := fun u => if (θs u) D = 0 then comp θ f c else comp (θs u) f c
  have hθs' : ∀ u, IsProbabilityMeasure (θs' u) := fun u => by
    by_cases hu : (θs u) D = 0
    · simp only [θs', hu, ↓reduceIte]
      infer_instance
    · simp only [θs', hu, ↓reduceIte]
      exact comp_isProbabilityMeasure hu
  set w' : Fin K → ℝ := fun u => w u * (θs u).real D / θ.real D
  have hw'0 : ∀ u, 0 ≤ w' u := fun u => div_nonneg (mul_nonneg (hw0 u) measureReal_nonneg) ht.le
  -- the mixture identity for real masses
  have hreal : ∀ A, MeasurableSet A →
      θ.real (D ∩ A) = ∑ u, w u * (θs u).real (D ∩ A) := by
    intro A hA
    have h := congrArg (fun ν : Measure X => (ν (D ∩ A)).toReal) hθ
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul] at h
    rw [measureReal_def, h, ENNReal.toReal_sum fun u _ => ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top (measure_ne_top _ _)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw0 u)]
    rfl
  have hw'1 : ∑ u, w' u = 1 := by
    have := hreal Set.univ MeasurableSet.univ
    simp only [Set.inter_univ] at this
    simp only [w', ← Finset.sum_div, ← this]
    exact div_self ht.ne'
  have hmix : comp θ f c = ∑ u, ENNReal.ofReal (w' u) • θs' u := by
    ext A hA
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    have hfin : ∀ u, (ENNReal.ofReal (w' u) • θs' u) A ≠ ⊤ := fun u => by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    rw [← ENNReal.ofReal_toReal (measure_ne_top (comp θ f c) A),
      ← ENNReal.ofReal_toReal (ENNReal.sum_ne_top.2 fun u _ => hfin u),
      ENNReal.toReal_sum fun u _ => hfin u]
    congr 1
    have h1 : (comp θ f c A).toReal = θ.real (D ∩ A) / θ.real D := comp_real_apply hf c A
    rw [h1, hreal A hA, Finset.sum_div]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw'0 u)]
    by_cases hu : (θs u) D = 0
    · have h0 : (θs u).real (D ∩ A) = 0 := by
        rw [measureReal_def, measure_mono_null Set.inter_subset_left hu, ENNReal.toReal_zero]
      have h0' : (θs u).real D = 0 := by rw [measureReal_def, hu, ENNReal.toReal_zero]
      simp [w', h0, h0']
    · simp only [θs', hu, ↓reduceIte]
      have h2 : ((comp (θs u) f c) A).toReal = (θs u).real (D ∩ A) / (θs u).real D :=
        comp_real_apply hf c A
      rw [h2]
      have h3 : 0 < (θs u).real D := by
        rw [measureReal_def]
        exact ENNReal.toReal_pos hu (measure_ne_top _ _)
      simp only [w']
      field_simp
  have hconc := sum_ent_le_ent hw'0 hw'1 hmix hg hgfin
  refine le_of_eq_of_le (Finset.sum_congr rfl fun u _ => ?_) hconc
  by_cases hu : (θs u) D = 0
  · have h0' : (θs u).real D = 0 := by rw [measureReal_def, hu, ENNReal.toReal_zero]
    simp [w', h0']
  · simp only [θs', hu, ↓reduceIte, w']

/-- A component of `ψμ` inside a single cell, at a scale `2^{-(i+kk)}`, has entropy at least
`m (d - δ')` at level `i + m`, for `m` large. -/
theorem entropy_piece_ge {μ : Measure ℝ} [IsProbabilityMeasure μ] (hI : μ AnalyticESC.Iᶜ = 0)
    {d δ' C ε : ℝ} (hδ' : 0 ≤ δ') (hC : 1 ≤ C) (hε : 0 < ε) {NY kk i m : ℕ}
    (hY : ∀ n ≥ NY, (d - δ' / 2) * n ≤ dyadicEntropy μ n) (hm : kk + NY ≤ m)
    (hmM : kk * (|d| + 1) + Real.log (2 * C / ε + 2) / Real.log 2 ≤ m * (δ' / 2))
    {f : ℝ → ℝ} (hf : Continuous f) (hfI : MapsTo f AnalyticESC.I AnalyticESC.I)
    (hlow : ∀ x ∈ AnalyticESC.I, ∀ y ∈ AnalyticESC.I,
      ε * (C⁻¹ / 2 ^ (i + kk)) * |x - y| ≤ |f x - f y|) :
    m * (d - δ') ≤ dyadicEntropy (μ.map f) (i + m) := by
  have hl2 := Real.log_pos one_lt_two
  have hC0 : 0 < C := by linarith
  have h1 := ent_le_ent_map_of_lower hI hf hfI (by positivity) hlow (i + m) (m - kk)
  have he : (2 : ℝ) ^ (m - kk) * (2 * (1 / (ε * (C⁻¹ / 2 ^ (i + kk)) * 2 ^ (i + m)))) + 2 =
      2 * C / ε + 2 := by
    have hpow : (2 : ℝ) ^ (m - kk) * 2 ^ (i + kk) = 2 ^ (i + m) := by
      rw [← pow_add]
      congr 1
      omega
    field_simp
    rw [← hpow]
    ring
  rw [he] at h1
  have h2 := hY (m - kk) (by omega)
  rw [dyadicEntropy_eq_ent] at h2
  rw [dyadicEntropy_eq_ent, le_div_iff₀ hl2]
  rw [le_div_iff₀ hl2] at h2
  have hmk : ((m - kk : ℕ) : ℝ) = m - kk := by
    rw [Nat.cast_sub (by omega)]
  rw [hmk] at h2
  have h3 : Real.log (2 * C / ε + 2) ≤ (m * (δ' / 2) - kk * (|d| + 1)) * Real.log 2 :=
    (div_le_iff₀ hl2).1 (by linarith)
  have hk0 : (0 : ℝ) ≤ kk := Nat.cast_nonneg kk
  have key : m * (d - δ') ≤ (d - δ' / 2) * (m - kk) - (m * (δ' / 2) - kk * (|d| + 1)) := by
    nlinarith [mul_nonneg hk0 (sub_nonneg.2 (le_abs_self d)), mul_nonneg hk0 hδ']
  have := mul_le_mul_of_nonneg_right key hl2.le
  linarith

/-- An image `f(I)` of small diameter which is not contained in a single level-`i` cell lies in
the `δ₁ 2^{-i}`-neighbourhood of the boundaries of the cells. -/
theorem mem_boundary_of_not_single_cell {f : ℝ → ℝ} (hf : Continuous f) {b : ℝ}
    (hup : ∀ x ∈ AnalyticESC.I, ∀ y ∈ AnalyticESC.I, |f x - f y| ≤ b * |x - y|) {i : ℕ}
    {δ₁ : ℝ} (hb : b ≤ δ₁ / 2 ^ i)
    (hnot : ¬ ∃ c, ∀ y ∈ AnalyticESC.I, cellIdx i (f y) = c) :
    ∀ y ∈ AnalyticESC.I, f y ∈ ⋃ k : ℤ, Metric.closedBall ((k : ℝ) / 2 ^ i) (δ₁ / 2 ^ i) := by
  push Not at hnot
  have h0 : (0 : ℝ) ∈ AnalyticESC.I := ⟨le_rfl, zero_le_one⟩
  obtain ⟨y₁, hy₁, hne⟩ := hnot (cellIdx i (f 0))
  have h2i : (0 : ℝ) < 2 ^ i := by positivity
  -- a boundary point in the image
  have hbd : ∃ k : ℤ, ∃ y₃ ∈ AnalyticESC.I, f y₃ = k / 2 ^ i := by
    have hsub : Set.uIcc 0 y₁ ⊆ AnalyticESC.I := Set.uIcc_subset_Icc h0 hy₁
    have hivt := intermediate_value_uIcc (a := 0) (b := y₁) hf.continuousOn
    have hlt := lt_cellIdx_add_one i (f 0)
    have hle := cellIdx_le i (f 0)
    have hlt1 := lt_cellIdx_add_one i (f y₁)
    have hle1 := cellIdx_le i (f y₁)
    rcases lt_or_gt_of_ne hne with h | h
    · refine ⟨cellIdx i (f 0), ?_⟩
      have h3 : ((cellIdx i (f y₁) : ℤ) : ℝ) + 1 ≤ cellIdx i (f 0) := by exact_mod_cast h
      have hmem : (cellIdx i (f 0) : ℝ) / 2 ^ i ∈ Set.uIcc (f 0) (f y₁) := by
        rw [Set.mem_uIcc]
        right
        constructor
        · rw [le_div_iff₀ h2i]; linarith
        · rw [div_le_iff₀ h2i]; linarith
      obtain ⟨y₃, hy₃, hfy₃⟩ := hivt hmem
      exact ⟨y₃, hsub hy₃, hfy₃⟩
    · refine ⟨cellIdx i (f y₁), ?_⟩
      have h3 : ((cellIdx i (f 0) : ℤ) : ℝ) + 1 ≤ cellIdx i (f y₁) := by exact_mod_cast h
      have hmem : (cellIdx i (f y₁) : ℝ) / 2 ^ i ∈ Set.uIcc (f 0) (f y₁) := by
        rw [Set.mem_uIcc]
        left
        constructor
        · rw [le_div_iff₀ h2i]; linarith
        · rw [div_le_iff₀ h2i]; linarith
      obtain ⟨y₃, hy₃, hfy₃⟩ := hivt hmem
      exact ⟨y₃, hsub hy₃, hfy₃⟩
  obtain ⟨k, y₃, hy₃, hfy₃⟩ := hbd
  intro y hy
  refine Set.mem_iUnion.2 ⟨k, ?_⟩
  rw [Metric.mem_closedBall, Real.dist_eq, ← hfy₃]
  have hyy : |y - y₃| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hy.1, hy.2, hy₃.1, hy₃.2]
  have hb0 : 0 ≤ b := by
    have := hup 0 h0 1 ⟨zero_le_one, le_rfl⟩
    have h1 : |(0 : ℝ) - 1| = 1 := by norm_num
    rw [h1, mul_one] at this
    exact (abs_nonneg _).trans this
  calc |f y - f y₃| ≤ b * |y - y₃| := hup y hy y₃ hy₃
    _ ≤ b * 1 := mul_le_mul_of_nonneg_left hyy hb0
    _ ≤ δ₁ / 2 ^ i := by linarith

/-- The image `f μ` of a probability measure carried by `I` gives full mass to every measurable
set containing `f(I)`. -/
theorem map_eq_one_of_image_subset {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hI : μ AnalyticESC.Iᶜ = 0) {f : ℝ → ℝ} (hf : Measurable f) {A : Set ℝ}
    (hA : MeasurableSet A) (hfA : ∀ y ∈ AnalyticESC.I, f y ∈ A) : μ.map f A = 1 := by
  rw [Measure.map_apply hf hA]
  refine le_antisymm prob_le_one ?_
  rw [← measure_univ (μ := μ)]
  calc μ univ ≤ μ (f ⁻¹' A ∪ AnalyticESC.Iᶜ) :=
        measure_mono fun y _ => by
          by_cases hy : y ∈ AnalyticESC.I
          · exact Or.inl (hfA y hy)
          · exact Or.inr hy
    _ ≤ μ (f ⁻¹' A) + μ AnalyticESC.Iᶜ := measure_union_le _ _
    _ = μ (f ⁻¹' A) := by rw [hI, add_zero]

/-- Proposition 3.3 of Rapaport: for `m` large, at every level `i` all but a `δ`-fraction of the
components `(ψμ)_{x,i}` have `H((ψμ)_{x,i}, 𝒟_{i+m}) / m > dim μ - δ`. -/
theorem prop33 {μ : Measure ℝ} (hμ : SCStructure μ) {d : ℝ}
    (hd : FractalGeometry.IsExactDim μ d) {ε : ℝ} (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ i : ℕ, ∀ ψ : ℝ → ℝ, Continuous ψ →
    MapsTo ψ AnalyticESC.I AnalyticESC.I → BiLipOn ψ ε ε⁻¹ →
    1 - δ < cavg (μ.map ψ) (cellIdx i)
      (fun τ => if d - δ < dyadicEntropy τ (i + m) / m then 1 else 0) := by
  classical
  have := hμ.isProb
  have hl2 := Real.log_pos one_lt_two
  obtain ⟨C, hC, hdec⟩ := hμ.decomp
  have hC0 : 0 < C := by linarith
  set δ' : ℝ := min (δ / 2) (δ / (2 * (|d| + 1))) with hδ'def
  have hδ'0 : 0 < δ' := lt_min (by positivity) (by positivity)
  have hδ'δ : δ' ≤ δ / 2 := min_le_left _ _
  have hδ'd : δ' * (|d| + 1) ≤ δ / 2 := by
    have : δ' ≤ δ / (2 * (|d| + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  obtain ⟨δ₁, hδ₁, -, hbdry⟩ := boundary_small hμ hε (c := δ' * δ' / 2) (by positivity)
  obtain ⟨kk, hkk⟩ := pow_unbounded_of_one_lt (ε⁻¹ * C / δ₁) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨NY, hNY⟩ := young_lower hμ.compl_I hd (η := δ' / 2) (by positivity)
  obtain ⟨M₀, hM₀⟩ := exists_nat_ge
    ((kk * (|d| + 1) + Real.log (2 * C / ε + 2) / Real.log 2) / (δ' / 2))
  refine ⟨max (max (kk + NY) M₀) 1, fun m hm i ψ hψc hψI hψL => ?_⟩
  have hm1 : kk + NY ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm1' : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1'
  have hmM : kk * (|d| + 1) + Real.log (2 * C / ε + 2) / Real.log 2 ≤ m * (δ' / 2) := by
    have h1 : (M₀ : ℝ) ≤ m := by
      exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
    have h2 := hM₀.trans h1
    rwa [div_le_iff₀ (by positivity)] at h2
  obtain ⟨K, w, g, hw0, hw1, hμeq, hg⟩ := hdec (i + kk)
  have hθeq := map_eq_sum_map_comp hμeq (fun u => (hg u).1) hψc
  set θ := μ.map ψ with hθdef
  set f : Fin K → ℝ → ℝ := fun u => ψ ∘ g u with hfdef
  have hfc : ∀ u, Continuous (f u) := fun u => hψc.comp (hg u).1
  have hfI : ∀ u, MapsTo (f u) AnalyticESC.I AnalyticESC.I := fun u => hψI.comp (hg u).2.1
  have hfL : ∀ u, BiLipOn (f u) (ε * (C⁻¹ / 2 ^ (i + kk))) (ε⁻¹ * (C / 2 ^ (i + kk))) :=
    fun u => biLipOn_comp_decomp hε hψL (hg u).2.2 (hg u).2.1
  have hfθ : θ = ∑ u, ENNReal.ofReal (w u) • μ.map (f u) := hθeq
  have hθP : IsProbabilityMeasure θ := inferInstance
  have hθI : θ AnalyticESC.Iᶜ = 0 := by
    rw [hθdef, Measure.map_apply hψc.measurable measurableSet_Icc.compl]
    exact measure_mono_null (fun y hy hyI => hy (hψI hyI)) hμ.compl_I
  have hIae : ∀ᵐ y ∂θ, y ∈ Icc (0 : ℝ) 1 := ae_mem_of_compl_null hθI
  have hfin : FiniteLabels θ (cellIdx i ∘ id) := finiteLabels_cellIdx_comp i hIae
  -- the pieces not contained in a single cell
  set bad := Finset.univ.filter fun u => ¬ ∃ c, ∀ y ∈ AnalyticESC.I, cellIdx i (f u y) = c
  set B := ⋃ k : ℤ, Metric.closedBall ((k : ℝ) / 2 ^ i) (δ₁ / 2 ^ i)
  have hBm : MeasurableSet B :=
    MeasurableSet.iUnion fun k => Metric.isClosed_closedBall.measurableSet
  have hsmall : ε⁻¹ * (C / 2 ^ (i + kk)) ≤ δ₁ / 2 ^ i := by
    have h1 : ε⁻¹ * C ≤ δ₁ * 2 ^ kk := by
      have := hkk.le
      rw [div_le_iff₀ hδ₁] at this
      linarith
    calc ε⁻¹ * (C / 2 ^ (i + kk)) = (ε⁻¹ * C) / (2 ^ kk * 2 ^ i) := by rw [pow_add]; ring
      _ ≤ (δ₁ * 2 ^ kk) / (2 ^ kk * 2 ^ i) := by gcongr
      _ = δ₁ / 2 ^ i := by field_simp
  have hbadmass : ∑ u ∈ bad, w u ≤ δ' * δ' / 2 := by
    have h1 := hbdry ψ hψc hψI hψL i
    have h2 : θ.real B = ∑ u, w u * (μ.map (f u)).real B := by
      rw [hfθ]
      simp only [measureReal_def, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
        smul_eq_mul]
      rw [ENNReal.toReal_sum fun u _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (measure_ne_top _ _)]
      exact Finset.sum_congr rfl fun u _ => by rw [ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (hw0 u)]
    have h3 : ∀ u ∈ bad, (μ.map (f u)).real B = 1 := fun u hu => by
      rw [measureReal_def, map_eq_one_of_image_subset hμ.compl_I (hfc u).measurable hBm
        (mem_boundary_of_not_single_cell (hfc u) (fun x hx y hy => (hfL u x hx y hy).2)
          hsmall (Finset.mem_filter.1 hu).2), ENNReal.toReal_one]
    calc ∑ u ∈ bad, w u = ∑ u ∈ bad, w u * (μ.map (f u)).real B :=
          Finset.sum_congr rfl fun u hu => by rw [h3 u hu, mul_one]
      _ ≤ ∑ u, w u * (μ.map (f u)).real B :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun u _ _ =>
            mul_nonneg (hw0 u) measureReal_nonneg
      _ = θ.real B := h2.symm
      _ ≤ δ' * δ' / 2 := h1
  -- the entropy of the good pieces
  have hpiece : ∀ u, m * (d - δ') ≤ dyadicEntropy (μ.map (f u)) (i + m) := fun u =>
    entropy_piece_ge hμ.compl_I hδ'0.le hC hε hNY hm1 hmM (hfc u) (hfI u)
      fun x hx y hy => (hfL u x hx y hy).1
  -- the bound for one cell
  have hcell : ∀ c, θ (cellIdx i ⁻¹' {c}) ≠ 0 →
      θ.real (cellIdx i ⁻¹' {c}) - (∑ u ∈ bad, w u * (μ.map (f u)).real (cellIdx i ⁻¹' {c})) / δ'
        ≤ θ.real (cellIdx i ⁻¹' {c}) * (if d - δ < dyadicEntropy (comp θ (cellIdx i) c)
          (i + m) / m then 1 else 0) := by
    intro c hc
    have hτP := comp_isProbabilityMeasure hc (f := cellIdx i)
    set t := θ.real (cellIdx i ⁻¹' {c})
    have ht : 0 < t := ENNReal.toReal_pos hc (measure_ne_top _ _)
    set a := (∑ u ∈ bad, w u * (μ.map (f u)).real (cellIdx i ⁻¹' {c})) / t
    by_cases hac : δ' ≤ a
    · have : t - (∑ u ∈ bad, w u * (μ.map (f u)).real (cellIdx i ⁻¹' {c})) / δ' ≤ 0 := by
        rw [sub_nonpos, le_div_iff₀ hδ'0]
        rw [le_div_iff₀ ht] at hac
        linarith
      refine this.trans (mul_nonneg ht.le ?_)
      split_ifs <;> norm_num
    push Not at hac
    have hgood : d - δ < dyadicEntropy (comp θ (cellIdx i) c) (i + m) / m := by
      have hH0 : 0 ≤ dyadicEntropy (comp θ (cellIdx i) c) (i + m) / m := by
        rw [dyadicEntropy_eq_ent]
        exact div_nonneg (div_nonneg (ent_nonneg _) hl2.le) hm0.le
      by_cases hdδ : d - δ < 0
      · linarith
      push Not at hdδ
      have hdpos : 0 ≤ d - δ' := by linarith
      -- concavity over the pieces
      have hgfin : FiniteLabels (comp θ (cellIdx i) c) (cellIdx (i + m) ∘ id) :=
        finiteLabels_cellIdx_comp (i + m) ((cond_absolutelyContinuous (μ := θ)).ae_le hIae)
      have hconc := sum_weight_mul_ent_comp_le (θs := fun u => μ.map (f u)) hw0 hfθ
        (measurable_cellIdx i) hc (measurable_cellIdx (i + m)) hgfin
      set X := m * (d - δ') * Real.log 2
      have hX0 : 0 ≤ X := by positivity
      have hterm : ∀ u, (if u ∈ bad then 0 else
          w u * (μ.map (f u)).real (cellIdx i ⁻¹' {c}) / t) * X ≤
          (w u * (μ.map (f u)).real (cellIdx i ⁻¹' {c}) / t) *
            ent (comp (μ.map (f u)) (cellIdx i) c) (cellIdx (i + m)) := by
        intro u
        have hw' : 0 ≤ w u * (μ.map (f u)).real (cellIdx i ⁻¹' {c}) / t :=
          div_nonneg (mul_nonneg (hw0 u) measureReal_nonneg) ht.le
        by_cases hu : u ∈ bad
        · simp only [hu, ↓reduceIte, zero_mul]
          exact mul_nonneg hw' (ent_nonneg _)
        simp only [hu, ↓reduceIte]
        have hu' : ∃ c', ∀ y ∈ AnalyticESC.I, cellIdx i (f u y) = c' := by
          by_contra h
          exact hu (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
        obtain ⟨c', hc'⟩ := hu'
        by_cases hcc : c' = c
        · subst hcc
          have hone : μ.map (f u) (cellIdx i ⁻¹' {c'}) = 1 :=
            map_eq_one_of_image_subset hμ.compl_I (hfc u).measurable
              (measurable_cellIdx i (measurableSet_singleton _)) fun y hy => hc' y hy
          have hcomp : comp (μ.map (f u)) (cellIdx i) c' = μ.map (f u) := by
            rw [comp, ProbabilityTheory.cond, hone, inv_one, one_smul]
            refine Measure.restrict_eq_self_of_ae_mem ?_
            rw [ae_iff]
            have := prob_compl_eq_one_sub (μ := μ.map (f u))
              (measurable_cellIdx i (measurableSet_singleton c'))
            rw [hone, tsub_self] at this
            exact this
          rw [hcomp]
          refine mul_le_mul_of_nonneg_left ?_ hw'
          have := hpiece u
          rw [dyadicEntropy_eq_ent, le_div_iff₀ hl2] at this
          exact this
        · have hzero : (μ.map (f u)).real (cellIdx i ⁻¹' {c}) = 0 := by
            rw [measureReal_def, Measure.map_apply (hfc u).measurable
              (measurable_cellIdx i (measurableSet_singleton c))]
            have : f u ⁻¹' (cellIdx i ⁻¹' {c}) ⊆ AnalyticESC.Iᶜ := fun y hy hyI => by
              simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy
              exact hcc ((hc' y hyI).symm.trans hy)
            rw [measure_mono_null this hμ.compl_I, ENNReal.toReal_zero]
          simp [hzero]
      have hsum1 : ∑ u, w u * (μ.map (f u)).real (cellIdx i ⁻¹' {c}) / t = 1 := by
        have h := congrArg (fun ν : Measure ℝ => (ν (cellIdx i ⁻¹' {c})).toReal) hfθ
        simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
          smul_eq_mul] at h
        rw [ENNReal.toReal_sum fun u _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (measure_ne_top _ _)] at h
        rw [← Finset.sum_div, div_eq_one_iff_eq ht.ne']
        rw [show t = (θ (cellIdx i ⁻¹' {c})).toReal from rfl, h]
        exact Finset.sum_congr rfl fun u _ => by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw0 u)]
          rfl
      have hsplit : ∑ u, (if u ∈ bad then 0 else
          w u * (μ.map (f u)).real (cellIdx i ⁻¹' {c}) / t) = 1 - a := by
        have h1 : ∑ u, (if u ∈ bad then 0 else
            w u * (μ.map (f u)).real (cellIdx i ⁻¹' {c}) / t) +
            ∑ u ∈ bad, w u * (μ.map (f u)).real (cellIdx i ⁻¹' {c}) / t =
            ∑ u, w u * (μ.map (f u)).real (cellIdx i ⁻¹' {c}) / t := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun u => u ∈ bad)
            (fun u => w u * (μ.map (f u)).real (cellIdx i ⁻¹' {c}) / t)]
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun u => u ∈ bad)
            (fun u => if u ∈ bad then 0 else
              w u * (μ.map (f u)).real (cellIdx i ⁻¹' {c}) / t)]
          have e1 : ∑ x ∈ Finset.univ.filter (fun u => u ∈ bad),
              (if x ∈ bad then (0 : ℝ) else
                w x * (μ.map (f x)).real (cellIdx i ⁻¹' {c}) / t) = 0 :=
            Finset.sum_eq_zero fun x hx => by simp [(Finset.mem_filter.1 hx).2]
          have e2 : ∑ x ∈ Finset.univ.filter (fun u => ¬ u ∈ bad),
              (if x ∈ bad then (0 : ℝ) else
                w x * (μ.map (f x)).real (cellIdx i ⁻¹' {c}) / t) =
              ∑ x ∈ Finset.univ.filter (fun u => ¬ u ∈ bad),
                w x * (μ.map (f x)).real (cellIdx i ⁻¹' {c}) / t :=
            Finset.sum_congr rfl fun x hx => by simp [(Finset.mem_filter.1 hx).2]
          have e3 : Finset.univ.filter (fun u => u ∈ bad) = bad := by
            ext u
            simp
          rw [e1, e2, e3, zero_add, add_comm]
        rw [hsum1] at h1
        have ha : ∑ u ∈ bad, w u * (μ.map (f u)).real (cellIdx i ⁻¹' {c}) / t = a :=
          (Finset.sum_div _ _ _).symm
        linarith
      have hent : (1 - a) * X ≤ ent (comp θ (cellIdx i) c) (cellIdx (i + m)) := by
        have h1 := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) => hterm u
        rw [← Finset.sum_mul, hsplit] at h1
        exact h1.trans (by simpa using hconc)
      rw [dyadicEntropy_eq_ent, div_div, lt_div_iff₀ (by positivity)]
      have h1 : (1 - δ') * X ≤ (1 - a) * X := mul_le_mul_of_nonneg_right (by linarith) hX0
      have h2 : (d - δ) * (Real.log 2 * m) < (1 - δ') * X := by
        have : (d - δ) < (1 - δ') * (d - δ') := by
          have h3 : (1 - δ') * (d - δ') = d - δ' * (1 + d) + δ' * δ' := by ring
          have h4 : δ' * (1 + d) ≤ δ' * (|d| + 1) := by
            have := le_abs_self d
            nlinarith
          nlinarith
        calc (d - δ) * (Real.log 2 * m) < (1 - δ') * (d - δ') * (Real.log 2 * m) :=
              mul_lt_mul_of_pos_right this (by positivity)
          _ = (1 - δ') * X := by ring
      linarith
    simp only [hgood, ↓reduceIte, mul_one]
    have : 0 ≤ (∑ u ∈ bad, w u * (μ.map (f u)).real (cellIdx i ⁻¹' {c})) / δ' :=
      div_nonneg (Finset.sum_nonneg fun u _ => mul_nonneg (hw0 u) measureReal_nonneg) hδ'0.le
    linarith
  -- summing over the cells
  rw [show cavg θ (cellIdx i) _ = cavg θ (cellIdx i ∘ id) _ from rfl, cavg_eq_sum hfin]
  have hS := sum_measureReal_fiber (measurable_cellIdx i) hfin.toFinset
    (fun _ hb => hfin.mem_toFinset.2 hb) (θ := θ)
  have hcells : ∀ u, ∑ c ∈ hfin.toFinset, (μ.map (f u)).real (cellIdx i ⁻¹' {c}) ≤ 1 :=
    fun u => by
      have := sum_measureReal_cell_shift_le (θ := μ.map (f u)) i hfin.toFinset 0
      simpa using this
  have hbadsum : ∑ c ∈ hfin.toFinset,
      (∑ u ∈ bad, w u * (μ.map (f u)).real (cellIdx i ⁻¹' {c})) ≤ ∑ u ∈ bad, w u := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun u _ => by
      rw [← Finset.mul_sum]
      exact mul_le_of_le_one_right (hw0 u) (hcells u)
  have hlow := Finset.sum_le_sum fun c (hc : c ∈ hfin.toFinset) =>
    hcell c (hfin.mem_toFinset.1 hc)
  rw [Finset.sum_sub_distrib, ← Finset.sum_div] at hlow
  have h1 : (∑ c ∈ hfin.toFinset,
      (∑ u ∈ bad, w u * (μ.map (f u)).real (cellIdx i ⁻¹' {c}))) / δ' ≤ δ' / 2 := by
    rw [div_le_iff₀ hδ'0]
    linarith
  have h2 : δ' / 2 < δ := by linarith
  have hS' : ∑ c ∈ hfin.toFinset, θ.real ((cellIdx i ∘ id) ⁻¹' {c}) = 1 := hS
  simp only [Function.comp_id] at hS' ⊢
  linarith

/-! ### Proposition 3.6 -/

/-- The average entropy of the components of `ψμ` is at most `d + 2δ` at large scales. -/
theorem avg_component_entropy_le {μ : Measure ℝ} (hμ : SCStructure μ) {d : ℝ}
    (hd : FractalGeometry.IsExactDim μ d) {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) (l : ℕ)
    (hl : 1 ≤ l) : ∃ N : ℕ, ∀ n ≥ N, ∀ ψ : ℝ → ℝ, Continuous ψ →
    MapsTo ψ AnalyticESC.I AnalyticESC.I → BiLipOn ψ ε ε⁻¹ →
    ∑ j ∈ Finset.range n, cavg (μ.map ψ) (cellIdx j)
      (fun τ => dyadicEntropy τ (j + l) / l) ≤ (d + 2 * δ) * n := by
  have := hμ.isProb
  have hl2 := Real.log_pos one_lt_two
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  obtain ⟨NY, hNY⟩ := young_upper hμ.compl_I hd hδ
  set K₀ : ℝ := Real.log (2 * ε⁻¹ + 2) / Real.log 2 + l * (Real.log 6 / Real.log 2)
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (K₀ / δ)
  refine ⟨max NY N₀, fun n hn ψ hψc hψI hψL => ?_⟩
  have hnY : NY ≤ n := le_trans (le_max_left _ _) hn
  have hn0 : (K₀ / δ : ℝ) ≤ n := hN₀.trans (by exact_mod_cast le_trans (le_max_right _ _) hn)
  set θ := μ.map ψ with hθdef
  have hθI : θ AnalyticESC.Iᶜ = 0 := by
    rw [hθdef, Measure.map_apply hψc.measurable measurableSet_Icc.compl]
    exact measure_mono_null (fun y hy hyI => hy (hψI hyI)) hμ.compl_I
  have hIae : ∀ᵐ y ∂θ, y ∈ Icc (0 : ℝ) 1 := ae_mem_of_compl_null hθI
  have hfin : ∀ j, FiniteLabels θ (cellIdx j) := fun j =>
    finiteLabels_cellIdx_comp (F := id) j hIae
  -- Hochman's Lemma 3.4 for `θ`
  have hms := abs_sum_cavg_cellIdx_sub_le (θ := θ) (F := id) measurable_id hIae n l
  simp only [Function.comp_id] at hms
  rw [abs_le] at hms
  -- `H(θ, 𝒟_n) ≤ H(μ, 𝒟_n) + log (2 ε⁻¹ + 2)`
  have hθμ : ent θ (cellIdx n) ≤ ent μ (cellIdx n) + Real.log (2 * ε⁻¹ + 2) := by
    have hIμ : ∀ᵐ y ∂μ, y ∈ Icc (0 : ℝ) 1 := ae_mem_of_compl_null hμ.compl_I
    have key := ent_cellIdx_comp_le (θ := μ) (F := ψ) (g := cellIdx n) hψc.measurable
      (measurable_cellIdx n) n (finiteLabels_cellIdx_comp n
        (by filter_upwards [hIμ] with y hy; exact hψI hy))
      (finiteLabels_cellIdx_comp (F := id) n hIμ) measurableSet_Icc hμ.compl_I
      (r := ε⁻¹ / 2 ^ n) (by positivity) fun x hx y hy hxy => by
        have h1 := (hψL x hx y hy).2
        have h2 := (abs_sub_lt_of_cellIdx_eq hxy).le
        calc |ψ x - ψ y| ≤ ε⁻¹ * |x - y| := h1
          _ ≤ ε⁻¹ * (1 / 2 ^ n) := mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = ε⁻¹ / 2 ^ n := by ring
    have he : (2 : ℝ) ^ n * (2 * (ε⁻¹ / 2 ^ n)) + 2 = 2 * ε⁻¹ + 2 := by field_simp
    rw [he] at key
    rw [hθdef, ent_map hψc.measurable (measurable_cellIdx n)]
    exact key
  have hμn := hNY n hnY
  rw [dyadicEntropy_eq_ent, div_le_iff₀ hl2] at hμn
  have h0 : 0 ≤ ent θ (cellIdx 0) := ent_nonneg _
  have hsum : ∑ j ∈ Finset.range n, cavg θ (cellIdx j) (fun τ => dyadicEntropy τ (j + l) / l) =
      (∑ j ∈ Finset.range n, cavg θ (cellIdx j) (fun ρ => ent ρ (cellIdx (j + l)))) /
        (l * Real.log 2) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_eq_inv_mul, ← cavg_const_mul (hfin j)]
    congr 1
    funext τ
    rw [dyadicEntropy_eq_ent]
    field_simp
  rw [hsum, div_le_iff₀ (by positivity)]
  have hK : K₀ ≤ δ * n := by rwa [div_le_iff₀ hδ, mul_comm] at hn0
  have hK' : Real.log (2 * ε⁻¹ + 2) + l * Real.log 6 ≤ δ * n * Real.log 2 := by
    have := mul_le_mul_of_nonneg_right hK hl2.le
    have e : K₀ * Real.log 2 = Real.log (2 * ε⁻¹ + 2) + l * Real.log 6 := by
      simp only [K₀]
      field_simp
    linarith
  have hl6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have h1 : ∑ j ∈ Finset.range n, cavg θ (cellIdx j) (fun ρ => ent ρ (cellIdx (j + l))) ≤
      l * ent θ (cellIdx n) + l * l * Real.log 6 := by nlinarith [hms.2]
  have h2 : (l : ℝ) * ent θ (cellIdx n) ≤ l * ((d + δ) * n * Real.log 2 +
      Real.log (2 * ε⁻¹ + 2)) := mul_le_mul_of_nonneg_left (by linarith) hl0.le
  have h3 : (l : ℝ) * (Real.log (2 * ε⁻¹ + 2) + l * Real.log 6) ≤ l * (δ * n * Real.log 2) :=
    mul_le_mul_of_nonneg_left hK' hl0.le
  nlinarith

/-- Proposition 3.6 of Rapaport: for `l` large and `n` large, all but a `δ`-fraction of the
components `(ψμ)_{x,j}`, `0 ≤ j < n`, have entropy within `δ` of `dim μ` at scale `l`. -/
theorem prop36 {μ : Measure ℝ} (hμ : SCStructure μ) {d : ℝ}
    (hd : FractalGeometry.IsExactDim μ d) {ε : ℝ} (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ l ≥ L₀, ∃ N : ℕ, ∀ n ≥ N, ∀ ψ : ℝ → ℝ, Continuous ψ →
    MapsTo ψ AnalyticESC.I AnalyticESC.I → BiLipOn ψ ε ε⁻¹ →
    (1 - δ) * n ≤ ∑ j ∈ Finset.range n, cavg (μ.map ψ) (cellIdx j)
      (fun τ => if |dyadicEntropy τ (j + l) / l - d| < δ then 1 else 0) := by
  classical
  have := hμ.isProb
  set δ₃ : ℝ := min (min (δ / 2) 1) (δ * δ / (2 * (|d| + 4))) with hδ₃def
  have hδ₃0 : 0 < δ₃ := lt_min (lt_min (by positivity) one_pos) (by positivity)
  have hδ₃δ : δ₃ ≤ δ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ₃1 : δ₃ ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ₃d : (|d| + 4) * δ₃ ≤ δ * δ / 2 := by
    have : δ₃ ≤ δ * δ / (2 * (|d| + 4)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  obtain ⟨M₃, hM₃⟩ := prop33 hμ hd hε δ₃ hδ₃0
  refine ⟨max M₃ 1, le_max_right _ _, fun l hl => ?_⟩
  have hl1 : 1 ≤ l := le_trans (le_max_right _ _) hl
  obtain ⟨N, hN⟩ := avg_component_entropy_le hμ hd hε hδ₃0 l hl1
  refine ⟨N, fun n hn ψ hψc hψI hψL => ?_⟩
  set θ := μ.map ψ with hθdef
  have hθI : θ AnalyticESC.Iᶜ = 0 := by
    rw [hθdef, Measure.map_apply hψc.measurable measurableSet_Icc.compl]
    exact measure_mono_null (fun y hy hyI => hy (hψI hyI)) hμ.compl_I
  have hIae : ∀ᵐ y ∂θ, y ∈ Icc (0 : ℝ) 1 := ae_mem_of_compl_null hθI
  have hfin : ∀ j, FiniteLabels θ (cellIdx j) := fun j =>
    finiteLabels_cellIdx_comp (F := id) j hIae
  have hmc := fun j => measurable_cellIdx j
  have hX := hN n hn ψ hψc hψI hψL
  -- the pointwise bound at each level, averaged over the components
  have hlev : ∀ j ∈ Finset.range n,
      (-1 - (|d| + δ₃) / δ) * cavg θ (cellIdx j)
          (fun τ => if dyadicEntropy τ (j + l) / l ≤ d - δ₃ then 1 else 0) +
        (-1 / δ) * cavg θ (cellIdx j) (fun τ => dyadicEntropy τ (j + l) / l) +
        0 * cavg θ (cellIdx j) (fun _ => 0) + (1 + (d - δ₃) / δ) ≤
      cavg θ (cellIdx j) (fun τ => if |dyadicEntropy τ (j + l) / l - d| < δ then 1 else 0) := by
    intro j _
    rw [← cavg_affine3 (hmc j) (hfin j)]
    refine cavg_mono (hfin j) fun c hc => ?_
    have := comp_isProbabilityMeasure hc (f := cellIdx j)
    set X := dyadicEntropy (comp θ (cellIdx j) c) (j + l) / l
    have hX0 : 0 ≤ X := by
      simp only [X]
      rw [dyadicEntropy_eq_ent]
      exact div_nonneg (div_nonneg (ent_nonneg _) (Real.log_nonneg (by norm_num)))
        (Nat.cast_nonneg l)
    have hd' := le_abs_self d
    by_cases h1 : X ≤ d - δ₃
    · have h2 : (if |X - d| < δ then (1 : ℝ) else 0) ≥ 0 := by split_ifs <;> norm_num
      simp only [h1, ↓reduceIte, mul_one, mul_zero, add_zero]
      have : (-1 - (|d| + δ₃) / δ) + (-1 / δ) * X + (1 + (d - δ₃) / δ) =
          (d - |d| - 2 * δ₃ - X) / δ := by field_simp; ring
      rw [this]
      have : (d - |d| - 2 * δ₃ - X) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith)
        hδ.le
      linarith
    · push Not at h1
      simp only [show ¬ X ≤ d - δ₃ from not_le.2 h1, ↓reduceIte, mul_zero, zero_add, add_zero]
      by_cases h3 : |X - d| < δ
      · simp only [h3, ↓reduceIte]
        have : (-1 / δ) * X + (1 + (d - δ₃) / δ) = 1 - (X - d + δ₃) / δ := by
          field_simp; ring
        rw [this]
        have : 0 ≤ (X - d + δ₃) / δ := div_nonneg (by linarith) hδ.le
        linarith
      · simp only [h3, ↓reduceIte]
        have h4 : d + δ ≤ X := by
          rw [abs_lt, not_and_or, not_lt, not_lt] at h3
          rcases h3 with h3 | h3 <;> linarith
        have : (-1 / δ) * X + (1 + (d - δ₃) / δ) = 1 - (X - d + δ₃) / δ := by
          field_simp; ring
        rw [this]
        have : 1 ≤ (X - d + δ₃) / δ := by rw [le_div_iff₀ hδ]; linarith
        linarith
  have hsum := Finset.sum_le_sum hlev
  have hF1 : ∀ j, cavg θ (cellIdx j)
      (fun τ => if dyadicEntropy τ (j + l) / l ≤ d - δ₃ then 1 else 0) ≤ δ₃ := by
    intro j
    have h1 := hM₃ l (le_trans (le_max_left _ _) hl) j ψ hψc hψI hψL
    have h2 : cavg θ (cellIdx j)
        (fun τ => if dyadicEntropy τ (j + l) / l ≤ d - δ₃ then 1 else 0) =
        1 - cavg θ (cellIdx j)
          (fun τ => if d - δ₃ < dyadicEntropy τ (j + l) / l then 1 else 0) := by
      have hadd := cavg_add (hfin j)
        (fun τ => if dyadicEntropy τ (j + l) / l ≤ d - δ₃ then (1 : ℝ) else 0)
        (fun τ => if d - δ₃ < dyadicEntropy τ (j + l) / l then (1 : ℝ) else 0)
      have hone : (fun τ : Measure ℝ =>
          (if dyadicEntropy τ (j + l) / l ≤ d - δ₃ then (1 : ℝ) else 0) +
            (if d - δ₃ < dyadicEntropy τ (j + l) / l then (1 : ℝ) else 0)) = fun _ => 1 := by
        funext τ
        by_cases h : d - δ₃ < dyadicEntropy τ (j + l) / l
        · simp [h, not_le.2 h]
        · simp [h, le_of_not_gt h]
      rw [hone, cavg_const (hmc j) (hfin j)] at hadd
      linarith
    rw [h2]
    linarith
  have hcavg0 : ∀ j, cavg θ (cellIdx j) (fun _ => (0 : ℝ)) = 0 := fun j => by
    simpa using cavg_const (hmc j) (hfin j) 0
  simp only [hcavg0, mul_zero, add_zero, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hF1sum : ∑ j ∈ Finset.range n, cavg θ (cellIdx j)
      (fun τ => if dyadicEntropy τ (j + l) / l ≤ d - δ₃ then 1 else 0) ≤ n * δ₃ := by
    calc _ ≤ ∑ _j ∈ Finset.range n, δ₃ := Finset.sum_le_sum fun j _ => hF1 j
      _ = n * δ₃ := by simp
  have hα : -1 - (|d| + δ₃) / δ ≤ 0 := by
    have : 0 ≤ (|d| + δ₃) / δ := by positivity
    linarith
  have hβ : -1 / δ ≤ 0 := by
    have : 0 < 1 / δ := by positivity
    rw [neg_div]
    linarith
  have h1 := mul_le_mul_of_nonpos_left hF1sum hα
  have h2 := mul_le_mul_of_nonpos_left hX hβ
  have key : (1 - δ) * n ≤ (-1 - (|d| + δ₃) / δ) * (n * δ₃) + (-1 / δ) * ((d + 2 * δ₃) * n) +
      n * (1 + (d - δ₃) / δ) := by
    have e : (-1 - (|d| + δ₃) / δ) * (n * δ₃) + (-1 / δ) * ((d + 2 * δ₃) * n) +
        n * (1 + (d - δ₃) / δ) = n * (1 - δ₃ - (3 * δ₃ + (|d| + δ₃) * δ₃) / δ) := by
      field_simp
      ring
    rw [e]
    have h5 : (3 * δ₃ + (|d| + δ₃) * δ₃) / δ ≤ δ / 2 := by
      rw [div_le_iff₀ hδ]
      nlinarith
    have h6 : 1 - δ ≤ 1 - δ₃ - (3 * δ₃ + (|d| + δ₃) * δ₃) / δ := by linarith
    nlinarith
  linarith

/-! ### Corollary 3.7 -/

/-- A sum over `[i, i + m]` as a sum over `range (m + 1)`. -/
theorem sum_Icc_add_eq_sum_range (f : ℕ → ℝ) (i m : ℕ) :
    ∑ j ∈ Finset.Icc i (i + m), f j = ∑ t ∈ Finset.range (m + 1), f (i + t) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show i + (m + 1) = (i + m) + 1 by ring, Finset.sum_Icc_succ_top (by omega), ih,
      Finset.sum_range_succ (fun t => f (i + t)) (m + 1), ← add_assoc]

/-- Components of components are components: for `i ≤ j` and a level-`i` component
`τ = θ_{f = c}`, the sets defined through the components of `τ` and of `θ` at level `j` have the
same `τ`-mass. -/
theorem measureReal_component_comp_eq {θ : Measure ℝ} [IsFiniteMeasure θ] {i j : ℕ}
    (hij : i ≤ j) {c : ℤ} (hc : θ (cellIdx i ⁻¹' {c}) ≠ 0) (Q : Measure ℝ → Prop) :
    (comp θ (cellIdx i) c).real {y | Q (component (comp θ (cellIdx i) c) j y)} =
      (comp θ (cellIdx i) c).real {y | Q (component θ j y)} := by
  refine measureReal_congr ?_
  rw [Filter.eventuallyEqSet_iff]
  filter_upwards [ae_comp_mem (measurable_cellIdx i) c] with y hy
  have h1 : comp θ (cellIdx i) c = component θ i y := by
    rw [component_eq_comp, hy]
  have hmem : y ∈ cellOf i y := (mem_cell_iff i _ y).2 rfl
  have hx : θ (cellOf i y) ≠ 0 := by rwa [cellOf_eq_preimage, hy]
  rw [h1, FractalGeometry.Hochman.component_component θ hij hmem hx]

/-- Component averages of functions agreeing on the components of positive mass agree. -/
theorem cavg_congr_comp {X : Type*} [MeasurableSpace X] {θ : Measure X} {L : Type*}
    {f : X → L} (hfin : FiniteLabels θ f) {F G : Measure X → ℝ}
    (h : ∀ b, θ (f ⁻¹' {b}) ≠ 0 → F (comp θ f b) = G (comp θ f b)) :
    cavg θ f F = cavg θ f G :=
  le_antisymm (cavg_mono hfin fun b hb => (h b hb).le) (cavg_mono hfin fun b hb => (h b hb).ge)

/-- A component average commutes with finite sums divided by a constant. -/
theorem cavg_sum_div {X : Type*} [MeasurableSpace X] {θ : Measure X} {L : Type*}
    {f : X → L} (hfin : FiniteLabels θ f) {ι : Type*} (T : Finset ι)
    (F : ι → Measure X → ℝ) (a : ℝ) :
    cavg θ f (fun τ => (∑ j ∈ T, F j τ) / a) = (∑ j ∈ T, cavg θ f (F j)) / a := by
  simp only [cavg_eq_sum hfin, Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Corollary 3.7 of Rapaport: for `l` large and `n` large relative to `m` and `l`, for all but a
`δ`-fraction of the pairs `(i, x)`, `0 ≤ i < n`, the components `((ψμ)_{x,i})_{y,j}` with
`i ≤ j ≤ i + m` have entropy within `δ` of `dim μ` at scale `l` with probability `> 1 - δ`. -/
theorem cor37 {μ : Measure ℝ} (hμ : SCStructure μ) {d : ℝ}
    (hd : FractalGeometry.IsExactDim μ d) {ε : ℝ} (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ l ≥ L₀, ∀ m : ℕ, ∃ N₁ : ℕ, ∀ n ≥ N₁, ∀ ψ : ℝ → ℝ, Continuous ψ →
    MapsTo ψ AnalyticESC.I AnalyticESC.I → BiLipOn ψ ε ε⁻¹ →
    (1 - δ) * n < ∑ i ∈ Finset.range n, cavg (μ.map ψ) (cellIdx i) (fun τ =>
      if 1 - δ < levelProb τ i m
        (fun j y => |dyadicEntropy (component τ j y) (j + l) / l - d| < δ) then 1 else 0) := by
  classical
  set δ₁ : ℝ := min (δ * δ / 4) (δ / 4) with hδ₁def
  have hδ₁0 : 0 < δ₁ := lt_min (by positivity) (by positivity)
  have hδ₁δ : δ₁ ≤ δ / 4 := min_le_right _ _
  obtain ⟨L₀, hL₀, h36⟩ := prop36 hμ hd hε δ₁ hδ₁0
  refine ⟨L₀, hL₀, fun l hl m => ?_⟩
  obtain ⟨N, hN⟩ := h36 l hl
  obtain ⟨N', hN'⟩ := exists_nat_ge (2 * (m + 1) / (δ * δ) + 1)
  refine ⟨max N N', fun n hn ψ hψc hψI hψL => ?_⟩
  have := hμ.isProb
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnN' : (2 * (m + 1) / (δ * δ) + 1 : ℝ) ≤ n :=
    hN'.trans (by exact_mod_cast le_trans (le_max_right _ _) hn)
  set θ := μ.map ψ with hθdef
  have hθI : θ AnalyticESC.Iᶜ = 0 := by
    rw [hθdef, Measure.map_apply hψc.measurable measurableSet_Icc.compl]
    exact measure_mono_null (fun y hy hyI => hy (hψI hyI)) hμ.compl_I
  have hIae : ∀ᵐ y ∂θ, y ∈ Icc (0 : ℝ) 1 := ae_mem_of_compl_null hθI
  have hfin : ∀ j, FiniteLabels θ (cellIdx j) := fun j =>
    finiteLabels_cellIdx_comp (F := id) j hIae
  have hmc := fun j => measurable_cellIdx j
  set P : ℕ → ℝ → Prop := fun j y => |dyadicEntropy (component θ j y) (j + l) / l - d| < δ
  set g : ℕ → ℝ := fun j => θ.real {y | P j y} with hgdef
  have hg0 : ∀ j, 0 ≤ g j := fun j => measureReal_nonneg
  have hg1 : ∀ j, g j ≤ 1 := fun j => measureReal_le_one
  -- (a) the masses of the good components at level `j` are bounded by `g j`
  have hga : ∀ j, cavg θ (cellIdx j)
      (fun τ => if |dyadicEntropy τ (j + l) / l - d| < δ₁ then 1 else 0) ≤ g j := by
    intro j
    rw [cavg_eq_sum (hfin j)]
    set S := (hfin j).toFinset
    set S' := S.filter fun c =>
      |dyadicEntropy (comp θ (cellIdx j) c) (j + l) / l - d| < δ₁
    have h1 : ∑ c ∈ S, θ.real (cellIdx j ⁻¹' {c}) *
        (if |dyadicEntropy (comp θ (cellIdx j) c) (j + l) / l - d| < δ₁ then 1 else 0) =
        ∑ c ∈ S', θ.real (cellIdx j ⁻¹' {c}) := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun c _ => by split_ifs <;> simp
    rw [h1, ← measureReal_biUnion_finset (fun a _ b _ hab => Disjoint.preimage _
      (Set.disjoint_singleton.2 hab)) (fun c _ => hmc j (measurableSet_singleton c))]
    refine measureReal_mono (fun y hy => ?_) (measure_ne_top _ _)
    obtain ⟨c, hc, hyc⟩ := Set.mem_iUnion₂.1 hy
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hyc
    have h2 := (Finset.mem_filter.1 hc).2
    show |dyadicEntropy (component θ j y) (j + l) / l - d| < δ
    rw [component_eq_comp, hyc]
    linarith
  -- (b) Proposition 3.6
  have hb : (1 - δ₁) * n ≤ ∑ j ∈ Finset.range n, g j :=
    (hN n hnN ψ hψc hψI hψL).trans (Finset.sum_le_sum fun j _ => hga j)
  -- (c) the level averages of the components at level `i`
  have hc : ∀ i, (∑ t ∈ Finset.range (m + 1), g (i + t)) / (m + 1) ≤
      cavg θ (cellIdx i) (fun τ => levelProb τ i m
        (fun j y => |dyadicEntropy (component τ j y) (j + l) / l - d| < δ)) := by
    intro i
    have e1 : cavg θ (cellIdx i) (fun τ => levelProb τ i m
        (fun j y => |dyadicEntropy (component τ j y) (j + l) / l - d| < δ)) =
        cavg θ (cellIdx i) (fun τ => (∑ j ∈ Finset.Icc i (i + m),
          τ.real {y | |dyadicEntropy (component τ j y) (j + l) / l - d| < δ}) / (m + 1)) := by
      rfl
    rw [e1]
    have e2 : cavg θ (cellIdx i) (fun τ => (∑ j ∈ Finset.Icc i (i + m),
          τ.real {y | |dyadicEntropy (component τ j y) (j + l) / l - d| < δ}) / (m + 1)) =
        cavg θ (cellIdx i) (fun τ => (∑ j ∈ Finset.Icc i (i + m),
          τ.real {y | P j y}) / (m + 1)) := by
      refine cavg_congr_comp (hfin i) fun c hc => ?_
      congr 1
      exact Finset.sum_congr rfl fun j hj =>
        measureReal_component_comp_eq (Finset.mem_Icc.1 hj).1 hc
          (fun τ => |dyadicEntropy τ (j + l) / l - d| < δ)
    rw [e2, cavg_sum_div (hfin i), ← sum_Icc_add_eq_sum_range]
    refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun j _ => ?_) (by positivity)
    exact measureReal_le_cavg (hmc i) (hfin i) _
  -- (d) summing over the levels
  have hshift := abs_sum_sum_shift_sub_le hg0 hg1 n (m + 1)
  rw [abs_le] at hshift
  have hd' : ∑ i ∈ Finset.range n, (∑ t ∈ Finset.range (m + 1), g (i + t)) / (m + 1) ≥
      ∑ i ∈ Finset.range n, g i - (m + 1) := by
    rw [← Finset.sum_div, ge_iff_le, le_div_iff₀ (by positivity)]
    push_cast at hshift
    nlinarith [hshift.1]
  -- (e) Markov's inequality for each component
  have he : ∀ i, 1 - 1 / δ + cavg θ (cellIdx i) (fun τ => levelProb τ i m
        (fun j y => |dyadicEntropy (component τ j y) (j + l) / l - d| < δ)) / δ ≤
      cavg θ (cellIdx i) (fun τ => if 1 - δ < levelProb τ i m
        (fun j y => |dyadicEntropy (component τ j y) (j + l) / l - d| < δ) then 1 else 0) := by
    intro i
    have h1 := cavg_affine3 (hmc i) (hfin i) (fun τ => levelProb τ i m
        (fun j y => |dyadicEntropy (component τ j y) (j + l) / l - d| < δ))
      (fun _ => 0) (fun _ => 0) (1 / δ) 0 0 (1 - 1 / δ)
    have h0 : cavg θ (cellIdx i) (fun _ : Measure ℝ => (0 : ℝ)) = 0 := by
      simpa using cavg_const (hmc i) (hfin i) 0
    rw [h0] at h1
    simp only [mul_zero, add_zero] at h1
    have h2 : 1 - 1 / δ + cavg θ (cellIdx i) (fun τ => levelProb τ i m
        (fun j y => |dyadicEntropy (component τ j y) (j + l) / l - d| < δ)) / δ =
        1 / δ * cavg θ (cellIdx i) (fun τ => levelProb τ i m
          (fun j y => |dyadicEntropy (component τ j y) (j + l) / l - d| < δ)) + (1 - 1 / δ) := by
      ring
    rw [h2, ← h1]
    refine cavg_mono (hfin i) fun c hc => ?_
    have := comp_isProbabilityMeasure hc (f := cellIdx i)
    set τ := comp θ (cellIdx i) c
    set LP := levelProb τ i m
        (fun j y => |dyadicEntropy (component τ j y) (j + l) / l - d| < δ)
    have hLP : LP ≤ 1 := by
      simp only [LP, levelProb]
      rw [div_le_one (by positivity)]
      calc ∑ j ∈ Finset.Icc i (i + m), τ.real _ ≤ ∑ _j ∈ Finset.Icc i (i + m), (1 : ℝ) :=
            Finset.sum_le_sum fun j _ => measureReal_le_one
        _ = m + 1 := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one,
            show i + m + 1 - i = m + 1 by omega]
          push_cast
          ring
    show 1 / δ * LP + (1 - 1 / δ) ≤ if 1 - δ < LP then 1 else 0
    split_ifs with h
    · have : 1 / δ * LP ≤ 1 / δ * 1 := mul_le_mul_of_nonneg_left hLP (by positivity)
      linarith
    · push Not at h
      have : 1 / δ * LP ≤ 1 / δ * (1 - δ) := mul_le_mul_of_nonneg_left h (by positivity)
      have e : 1 / δ * (1 - δ) + (1 - 1 / δ) = 0 := by field_simp; ring
      linarith
  -- (f) the final estimate
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.range n) => he i
  have hsum2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.range n) => hc i
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.sum_div] at hsum
  refine lt_of_lt_of_le ?_ hsum
  have hA : ∑ i ∈ Finset.range n, g i - (m + 1) ≤ ∑ i ∈ Finset.range n,
      cavg θ (cellIdx i) (fun τ => levelProb τ i m
        (fun j y => |dyadicEntropy (component τ j y) (j + l) / l - d| < δ)) := by linarith
  have hfinal : (1 - δ) * n < n * (1 - 1 / δ) + ((1 - δ₁) * n - (m + 1)) / δ := by
    have e : n * (1 - 1 / δ) + ((1 - δ₁) * n - (m + 1)) / δ =
        n - (δ₁ * n + (m + 1)) / δ := by field_simp; ring
    rw [e]
    have h1 : δ₁ * n ≤ δ / 4 * n := mul_le_mul_of_nonneg_right hδ₁δ (Nat.cast_nonneg n)
    have h2 : (m + 1 : ℝ) / δ < 3 * δ / 4 * n := by
      have h3 : 2 * (m + 1) / (δ * δ) < n := by linarith
      rw [div_lt_iff₀ (by positivity)] at h3
      rw [div_lt_iff₀ hδ]
      nlinarith
    have h4 : (δ₁ * n + (m + 1)) / δ = δ₁ * n / δ + (m + 1) / δ := by ring
    have h5 : δ₁ * n / δ ≤ δ * n / 4 := by
      rw [div_le_iff₀ hδ]
      have : δ₁ ≤ δ * δ / 4 := min_le_left _ _
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [h4]
    nlinarith
  have hmono : ((1 - δ₁) * n - (m + 1)) / δ ≤ (∑ i ∈ Finset.range n,
      cavg θ (cellIdx i) (fun τ => levelProb τ i m
        (fun j y => |dyadicEntropy (component τ j y) (j + l) / l - d| < δ))) / δ := by
    gcongr
    linarith
  linarith

end FractalGeometry.Rapaport.Analytic
