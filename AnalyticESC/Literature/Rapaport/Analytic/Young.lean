module

public import AnalyticESC.Literature.Rapaport.Analytic.Dyadic

@[expose] public section

/-!
# Entropy dimension of exact dimensional measures

L.-S. Young, *Dimension, entropy and Lyapunov exponents*, Ergodic Theory Dynam. Systems 2 (1982),
in the form (2.9) of A. Rapaport, *Dimension of self-conformal measures associated to an
exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2: if `θ` is a probability measure
on `I` which is exact dimensional with dimension `d`, then `H(θ, 𝒟_n) / n → d`.

The lower bound uses that a dyadic cell of level `n` meeting the set where
`θ(B(x, 2^{-n})) ≤ 2^{-n(d - η)}` has mass at most `2^{-n(d - η)}`. The upper bound uses that the
cells meeting the set where `θ(B(x, 2^{-n})) ≥ 2^{-n(d + η)}` are at most `4 · 2^{n(d + η)}` in
number, together with almost convexity for the split along their union.

## Main declarations

* `eventually_measureReal_closedBall_le`, `eventually_le_measureReal_closedBall`: the local
  dimension along the scales `2^{-n}`.
* `exists_lt_measureReal_good`: almost sure eventual properties hold uniformly from some `N` on a
  set of measure close to `1`.
* `young_lower`, `young_upper`: `(d - η) n ≤ H(θ, 𝒟_n) ≤ (d + η) n` for `n` large.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Young`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic

open MeasureTheory ProbabilityTheory Set Filter Topology FractalGeometry.SelfConformal
open scoped ENNReal

/-- `2^{-n} → 0⁺`. -/
theorem tendsto_one_div_two_pow_nhdsGT :
    Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => by
    simp only [Set.mem_Ioi]
    positivity⟩
  simp_rw [← one_div_pow]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- `log 2^{-n} = -n log 2`. -/
theorem log_one_div_two_pow (n : ℕ) : Real.log (1 / 2 ^ n) = -(n * Real.log 2) := by
  rw [one_div, Real.log_inv, Real.log_pow]

/-- Along the scales `2^{-n}`, the local dimension gives `θ(B(x, 2^{-n})) ≤ e^{-n log 2 (d - η)}`
eventually. -/
theorem eventually_measureReal_closedBall_le {θ : Measure ℝ} {x : ℝ} {d : ℝ}
    (hx : FractalGeometry.HasLocalDim θ x d) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, θ.real (Metric.closedBall x (1 / 2 ^ n)) ≤
      Real.exp (-(n * Real.log 2) * (d - η)) := by
  have h := hx.comp tendsto_one_div_two_pow_nhdsGT
  filter_upwards [h.eventually (lt_mem_nhds (by linarith : d - η < d)),
    eventually_ge_atTop 1] with n hn hn1
  simp only [Function.comp_apply, log_one_div_two_pow] at hn
  have hneg : -((n : ℝ) * Real.log 2) < 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have := Real.log_pos one_lt_two
    nlinarith
  rw [lt_div_iff_of_neg hneg] at hn
  rcases (measureReal_nonneg (μ := θ) (s := Metric.closedBall x (1 / 2 ^ n))).lt_or_eq with
    hpos | hzero
  · rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.2 (by linarith)
  · rw [← hzero]
    exact (Real.exp_pos _).le

/-- Along the scales `2^{-n}`, the local dimension gives `θ(B(x, 2^{-n})) ≥ e^{-n log 2 (d + η)}`
eventually, at points all of whose balls have positive mass. -/
theorem eventually_le_measureReal_closedBall {θ : Measure ℝ} {x : ℝ} {d : ℝ}
    (hx : FractalGeometry.HasLocalDim θ x d)
    (hpos : ∀ r : ℝ, 0 < r → 0 < θ.real (Metric.closedBall x r)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-(n * Real.log 2) * (d + η)) ≤
      θ.real (Metric.closedBall x (1 / 2 ^ n)) := by
  have h := hx.comp tendsto_one_div_two_pow_nhdsGT
  filter_upwards [h.eventually (gt_mem_nhds (by linarith : d < d + η)),
    eventually_ge_atTop 1] with n hn hn1
  simp only [Function.comp_apply, log_one_div_two_pow] at hn
  have hneg : -((n : ℝ) * Real.log 2) < 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have := Real.log_pos one_lt_two
    nlinarith
  rw [div_lt_iff_of_neg hneg] at hn
  have hp := hpos (1 / 2 ^ n) (by positivity)
  rw [← Real.exp_log hp]
  exact Real.exp_le_exp.2 (by linarith)

/-- An almost surely eventual property holds for all `n ≥ N` on a set of measure `> 1 - η`. -/
theorem exists_lt_measureReal_good {θ : Measure ℝ} [IsProbabilityMeasure θ]
    {P : ℕ → ℝ → Prop} (hP : ∀ᵐ x ∂θ, ∀ᶠ n in atTop, P n x) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, 1 - η < θ.real {x | ∀ n ≥ N, P n x} := by
  set G : ℕ → Set ℝ := fun N => {x | ∀ n ≥ N, P n x}
  have hmono : Monotone G := fun N N' hNN' x hx n hn => hx n (le_trans hNN' hn)
  have hU : θ (⋃ N, G N) = 1 := by
    refine le_antisymm prob_le_one ?_
    have h1 : θ univ ≤ θ (⋃ N, G N) + θ (⋃ N, G N)ᶜ :=
      calc θ univ = θ ((⋃ N, G N) ∪ (⋃ N, G N)ᶜ) := by rw [Set.union_compl_self]
        _ ≤ _ := measure_union_le _ _
    have h2 : θ (⋃ N, G N)ᶜ = 0 := by
      refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hP)
      intro hev
      obtain ⟨N, hN⟩ := eventually_atTop.1 hev
      exact hx (Set.mem_iUnion.2 ⟨N, hN⟩)
    rw [h2, add_zero, measure_univ] at h1
    exact h1
  by_cases h1η : 1 - η < 0
  · exact ⟨0, h1η.trans_le measureReal_nonneg⟩
  push Not at h1η
  have ht := tendsto_measure_iUnion_atTop (μ := θ) hmono
  rw [hU] at ht
  have hlt : ENNReal.ofReal (1 - η) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    linarith
  obtain ⟨N, hN⟩ := (ht.eventually (lt_mem_nhds hlt)).exists
  refine ⟨N, ?_⟩
  have := (ENNReal.ofReal_lt_iff_lt_toReal h1η (measure_ne_top θ (G N))).1 hN
  exact this

/-- The lower bound of (2.9): `(d - η) n ≤ H(θ, 𝒟_n)` for `n` large. -/
theorem young_lower {θ : Measure ℝ} [IsProbabilityMeasure θ] (hI : θ AnalyticESC.Iᶜ = 0)
    {d : ℝ} (hd : FractalGeometry.IsExactDim θ d) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, (d - η) * n ≤ dyadicEntropy θ n := by
  classical
  by_cases hdη : d - η ≤ 0
  · refine ⟨0, fun n _ => ?_⟩
    have : 0 ≤ dyadicEntropy θ n := by
      rw [dyadicEntropy_eq_ent]
      exact div_nonneg (ent_nonneg _) (Real.log_nonneg (by norm_num))
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  push Not at hdη
  have hd0 : 0 < d := by linarith
  have hl2 := Real.log_pos one_lt_two
  set η' : ℝ := η / (2 * d) with hη'
  obtain ⟨N, hN⟩ := exists_lt_measureReal_good (θ := θ)
    (P := fun n x => θ.real (Metric.closedBall x (1 / 2 ^ n)) ≤
      Real.exp (-(n * Real.log 2) * (d - η / 2)))
    (hd.mono fun x hx => eventually_measureReal_closedBall_le hx (by positivity))
    (by positivity : 0 < η')
  set G := {x | ∀ n ≥ N, θ.real (Metric.closedBall x (1 / 2 ^ n)) ≤
      Real.exp (-(n * Real.log 2) * (d - η / 2))}
  refine ⟨N, fun n hn => ?_⟩
  have hθI : ∀ᵐ x ∂θ, x ∈ Icc (0 : ℝ) 1 := ae_mem_of_compl_null hI
  have hfin : FiniteLabels θ (cellIdx n ∘ id) := finiteLabels_cellIdx_comp n hθI
  set S := hfin.toFinset
  set S' := S.filter fun c => (cellIdx n ⁻¹' {c} ∩ G).Nonempty
  have hmc := measurable_cellIdx n
  -- the cells meeting `G` have small mass
  have hsmall : ∀ c ∈ S', θ.real (cellIdx n ⁻¹' {c}) ≤
      Real.exp (-(n * Real.log 2) * (d - η / 2)) := by
    intro c hc
    obtain ⟨x, hxc, hxG⟩ := (Finset.mem_filter.1 hc).2
    refine (measureReal_mono (fun y hy => ?_)).trans (hxG n hn)
    rw [Metric.mem_closedBall, Real.dist_eq]
    exact (abs_sub_lt_of_cellIdx_eq (hy.trans hxc.symm)).le
  -- the cells meeting `G` cover `G` up to a null set
  have hcover : θ.real G ≤ ∑ c ∈ S', θ.real (cellIdx n ⁻¹' {c}) := by
    have h1 : θ G ≤ θ (⋃ c ∈ S', cellIdx n ⁻¹' {c}) + θ {x | cellIdx n x ∉ S} := by
      refine (measure_mono fun x hx => ?_).trans (measure_union_le _ _)
      by_cases hxS : cellIdx n x ∈ S
      · exact Or.inl (Set.mem_biUnion (Finset.mem_filter.2 ⟨hxS, ⟨x, rfl, hx⟩⟩) rfl)
      · exact Or.inr hxS
    have h2 : θ {x | cellIdx n x ∉ S} = 0 := ae_iff.1 hfin.ae_mem
    rw [h2, add_zero] at h1
    have h3 := h1.trans (measure_biUnion_finset_le _ _)
    simp only [measureReal_def]
    rw [← ENNReal.toReal_sum fun _ _ => measure_ne_top _ _]
    exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun _ _ => measure_ne_top _ _) h3
  -- the entropy bound
  have hent : (n * Real.log 2) * (d - η / 2) * θ.real G ≤ ent θ (cellIdx n) := by
    rw [show ent θ (cellIdx n) = ent θ (cellIdx n ∘ id) from rfl, ent_eq_sum hfin]
    calc (n * Real.log 2) * (d - η / 2) * θ.real G
        ≤ (n * Real.log 2) * (d - η / 2) * ∑ c ∈ S', θ.real (cellIdx n ⁻¹' {c}) :=
          mul_le_mul_of_nonneg_left hcover
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hl2.le) (by linarith))
      _ = ∑ c ∈ S', (n * Real.log 2) * (d - η / 2) * θ.real (cellIdx n ⁻¹' {c}) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ c ∈ S', Real.negMulLog (θ.real (cellIdx n ⁻¹' {c})) :=
          Finset.sum_le_sum fun c hc => by
            have hs := hsmall c hc
            rcases (measureReal_nonneg (μ := θ) (s := cellIdx n ⁻¹' {c})).lt_or_eq with
              htp | ht0
            · have h1 := (Real.log_le_iff_le_exp htp).2 hs
              have h2 : (n * Real.log 2) * (d - η / 2) ≤
                  -Real.log (θ.real (cellIdx n ⁻¹' {c})) := by
                linarith
              have h3 := mul_le_mul_of_nonneg_right h2 htp.le
              have h4 : -Real.log (θ.real (cellIdx n ⁻¹' {c})) * θ.real (cellIdx n ⁻¹' {c}) =
                  Real.negMulLog (θ.real (cellIdx n ⁻¹' {c})) := by
                rw [Real.negMulLog]
                ring
              linarith
            · rw [← ht0]
              simp
      _ ≤ ∑ c ∈ S, Real.negMulLog (θ.real ((cellIdx n ∘ id) ⁻¹' {c})) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun c _ _ =>
            Real.negMulLog_nonneg measureReal_nonneg measureReal_le_one
  rw [dyadicEntropy_eq_ent, le_div_iff₀ hl2]
  have hG : 1 - η' < θ.real G := hN
  have hkey : (d - η) ≤ (d - η / 2) * θ.real G := by
    have h1 : (d - η / 2) * (1 - η') ≤ (d - η / 2) * θ.real G :=
      mul_le_mul_of_nonneg_left hG.le (by linarith)
    have h2 : (d - η / 2) * (1 - η') = d - η / 2 - η / 2 + η * η / (4 * d) := by
      rw [hη']
      field_simp
      ring
    have h3 : 0 ≤ η * η / (4 * d) := by positivity
    linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc (d - η) * n * Real.log 2 = (n * Real.log 2) * (d - η) := by ring
    _ ≤ (n * Real.log 2) * ((d - η / 2) * θ.real G) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (n * Real.log 2) * (d - η / 2) * θ.real G := by ring
    _ ≤ ent θ (cellIdx n) := hent

/-- A closed ball of radius `2^{-n}` about `x` lies in the four level-`n` cells with indices
`cellIdx n x - 1, …, cellIdx n x + 2`. -/
theorem closedBall_subset_cells (n : ℕ) (x : ℝ) :
    Metric.closedBall x (1 / 2 ^ n) ⊆
      ⋃ t : Fin 4, cellIdx n ⁻¹' {cellIdx n x + (t : ℤ) - 1} := by
  intro y hy
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hy
  have h2 := two_pow_pos' n
  have hx1 := cellIdx_le n x
  have hx2 := lt_cellIdx_add_one n x
  have hy1 := cellIdx_le n y
  have hy2 := lt_cellIdx_add_one n y
  have e1 : (2 : ℝ) ^ n * (1 / 2 ^ n) = 1 := by field_simp
  have h3 : (2 : ℝ) ^ n * y ≤ 2 ^ n * x + 1 := by nlinarith
  have h4 : (2 : ℝ) ^ n * x - 1 ≤ 2 ^ n * y := by nlinarith
  have h5 : cellIdx n y ≤ cellIdx n x + 2 := by
    have : (cellIdx n y : ℝ) < cellIdx n x + 3 := by linarith
    have : cellIdx n y < cellIdx n x + 3 := by exact_mod_cast this
    omega
  have h6 : cellIdx n x - 1 ≤ cellIdx n y := by
    have : (cellIdx n x : ℝ) - 2 < cellIdx n y := by linarith
    have : cellIdx n x - 2 < cellIdx n y := by exact_mod_cast this
    omega
  refine Set.mem_iUnion.2 ⟨⟨(cellIdx n y - cellIdx n x + 1).toNat, by omega⟩, ?_⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  omega

/-- For a finset `T` of indices, the masses of the cells `T + s` add up to at most `1`. -/
theorem sum_measureReal_cell_shift_le {θ : Measure ℝ} [IsProbabilityMeasure θ] (n : ℕ)
    (T : Finset ℤ) (s : ℤ) : ∑ c ∈ T, θ.real (cellIdx n ⁻¹' {c + s}) ≤ 1 := by
  rw [← measureReal_biUnion_finset]
  · exact measureReal_le_one
  · intro a _ b _ hab
    refine Disjoint.preimage _ (Set.disjoint_singleton.2 ?_)
    intro h
    exact hab (by linarith)
  · intro c _
    exact measurable_cellIdx n (measurableSet_singleton _)

/-- The upper bound of (2.9) for `η ≤ 1`. -/
theorem young_upper_aux {θ : Measure ℝ} [IsProbabilityMeasure θ] (hI : θ AnalyticESC.Iᶜ = 0)
    {d : ℝ} (hd : FractalGeometry.IsExactDim θ d) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ N : ℕ, ∀ n ≥ N, dyadicEntropy θ n ≤ (d + η) * n := by
  classical
  have hl2 := Real.log_pos one_lt_two
  have hsupp : ∀ᵐ x ∂θ, ∀ r : ℝ, 0 < r → 0 < θ.real (Metric.closedBall x r) := by
    filter_upwards [θ.support_mem_ae] with x hx r hr
    have := (Measure.mem_support_iff_forall x).1 hx _ (Metric.closedBall_mem_nhds x hr)
    rw [measureReal_def]
    exact ENNReal.toReal_pos this.ne' (measure_ne_top _ _)
  obtain ⟨N₁, hN₁⟩ := exists_lt_measureReal_good (θ := θ)
    (P := fun n x => Real.exp (-(n * Real.log 2) * (d + η / 2)) ≤
      θ.real (Metric.closedBall x (1 / 2 ^ n)))
    (by filter_upwards [hd, hsupp] with x hx hx'
        exact eventually_le_measureReal_closedBall hx hx' (by positivity))
    (by positivity : 0 < η / 8)
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (8 / η + 1)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : (8 / η + 1 : ℝ) ≤ n := hN₂.trans (by exact_mod_cast le_trans (le_max_right _ _) hn)
  have hn0 : (1 : ℝ) ≤ n := by
    have : 0 ≤ 8 / η := by positivity
    linarith
  set G := {x | ∀ n ≥ N₁, Real.exp (-(n * Real.log 2) * (d + η / 2)) ≤
      θ.real (Metric.closedBall x (1 / 2 ^ n))}
  set e := Real.exp (-(n * Real.log 2) * (d + η / 2))
  have he0 : 0 < e := Real.exp_pos _
  set T := (Finset.Icc (cellIdx n (-1)) (cellIdx n 2)).filter
    fun c => (cellIdx n ⁻¹' {c} ∩ G).Nonempty
  set A := ⋃ c ∈ T, cellIdx n ⁻¹' {c}
  have hAm : MeasurableSet A :=
    Finset.measurableSet_biUnion _ fun c _ => measurable_cellIdx n (measurableSet_singleton c)
  -- points of `G` lie in cells of `T`
  have hGA : G ⊆ A := by
    intro x hx
    have hpos : 0 < θ.real (Metric.closedBall x (1 / 2 ^ n)) := he0.trans_le (hx n hn1)
    have hne : (Metric.closedBall x (1 / 2 ^ n) ∩ AnalyticESC.I).Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      have hsub : Metric.closedBall x (1 / 2 ^ n) ⊆ AnalyticESC.Iᶜ := fun y hy hyI => by
        have : y ∈ Metric.closedBall x (1 / 2 ^ n) ∩ AnalyticESC.I := ⟨hy, hyI⟩
        rw [hne] at this
        exact this
      have : θ (Metric.closedBall x (1 / 2 ^ n)) = 0 := measure_mono_null hsub hI
      rw [measureReal_def, this, ENNReal.toReal_zero] at hpos
      exact lt_irrefl 0 hpos
    obtain ⟨y, hy, hyI⟩ := hne
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hy
    have h1 : (1 : ℝ) / 2 ^ n ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact one_le_pow₀ (by norm_num)
    have hxI : x ∈ Icc (-1 : ℝ) 2 := ⟨by linarith [hyI.1], by linarith [hyI.2]⟩
    exact Set.mem_biUnion (Finset.mem_filter.2 ⟨cellIdx_mem_Icc hxI, ⟨x, rfl, hx⟩⟩) rfl
  -- the number of cells of `T`
  have hcard : (T.card : ℝ) * e ≤ 4 := by
    have h1 : ∀ c ∈ T, e ≤ ∑ t : Fin 4, θ.real (cellIdx n ⁻¹' {c + ((t : ℤ) - 1)}) := by
      intro c hc
      obtain ⟨x, hxc, hxG⟩ := (Finset.mem_filter.1 hc).2
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hxc
      refine (hxG n hn1).trans ((measureReal_mono (closedBall_subset_cells n x)).trans ?_)
      refine (measureReal_iUnion_fintype_le _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hxc, add_sub_assoc]
    calc (T.card : ℝ) * e = ∑ _c ∈ T, e := by simp
      _ ≤ ∑ c ∈ T, ∑ t : Fin 4, θ.real (cellIdx n ⁻¹' {c + ((t : ℤ) - 1)}) :=
          Finset.sum_le_sum h1
      _ = ∑ t : Fin 4, ∑ c ∈ T, θ.real (cellIdx n ⁻¹' {c + ((t : ℤ) - 1)}) := Finset.sum_comm
      _ ≤ ∑ _t : Fin 4, (1 : ℝ) :=
          Finset.sum_le_sum fun t _ => sum_measureReal_cell_shift_le n T _
      _ = 4 := by simp
  -- the two pieces
  have hfin : FiniteLabels θ (cellIdx n ∘ id) := finiteLabels_cellIdx_comp n
    (ae_mem_of_compl_null hI)
  have hsplit := ent_le_two_pieces (θ := θ) (measurable_cellIdx n) hfin hAm
  have hGθ : 1 - η / 8 < θ.real A := hN₁.trans_le (measureReal_mono hGA (measure_ne_top _ _))
  have hAc : θ.real Aᶜ < η / 8 := by
    rw [measureReal_compl hAm, probReal_univ]
    linarith
  have hpA : θ.real A * ent (θ[|A]) (cellIdx n) ≤ Real.log 4 + (n * Real.log 2) * (d + η / 2) := by
    by_cases hA0 : θ A = 0
    · have : 0 < θ.real A := by linarith
      rw [measureReal_def, hA0, ENNReal.toReal_zero] at this
      exact absurd this (lt_irrefl 0)
    have := cond_isProbabilityMeasure hA0 (μ := θ)
    have h1 : ent (θ[|A]) (cellIdx n) ≤ Real.log T.card := by
      refine ent_le_log_of_ae_mem (measurable_cellIdx n) T ?_
      filter_upwards [ae_cond_mem hAm] with x hx
      obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 hx
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hxc
      rw [hxc]
      exact hc
    have hT : 0 < (T.card : ℝ) := by
      rcases Nat.eq_zero_or_pos T.card with h | h
      · exfalso
        have hAe : A = ∅ := by
          rw [Finset.card_eq_zero] at h
          simp [A, h]
        exact hA0 (by rw [hAe, measure_empty])
      · exact_mod_cast h
    have h2 : Real.log T.card ≤ Real.log 4 + (n * Real.log 2) * (d + η / 2) := by
      have h3 : (T.card : ℝ) ≤ 4 / e := by rw [le_div_iff₀ he0]; exact hcard
      calc Real.log T.card ≤ Real.log (4 / e) := Real.log_le_log hT h3
        _ = Real.log 4 + (n * Real.log 2) * (d + η / 2) := by
          rw [Real.log_div (by norm_num) he0.ne', Real.log_exp]
          ring
    have h4 : 0 ≤ ent (θ[|A]) (cellIdx n) := ent_nonneg _
    calc θ.real A * ent (θ[|A]) (cellIdx n) ≤ 1 * ent (θ[|A]) (cellIdx n) :=
          mul_le_mul_of_nonneg_right measureReal_le_one h4
      _ ≤ _ := by linarith
  have hpAc : θ.real Aᶜ * ent (θ[|Aᶜ]) (cellIdx n) ≤ η / 8 * ((n + 1) * Real.log 2) := by
    by_cases hA0 : θ Aᶜ = 0
    · rw [measureReal_def, hA0, ENNReal.toReal_zero, zero_mul]
      positivity
    have := cond_isProbabilityMeasure hA0 (μ := θ)
    have h1 := ent_cellIdx_comp_le_log (θ := θ[|Aᶜ]) (F := id) measurable_id
      (zero_le_one) n ((cond_absolutelyContinuous (μ := θ)).ae_le (ae_mem_of_compl_null hI))
    have h2 : Real.log (2 ^ n * (1 - 0) + 2) ≤ (n + 1) * Real.log 2 := by
      have h3 : (2 : ℝ) ^ n * (1 - 0) + 2 ≤ 2 ^ (n + 1) := by
        have : (2 : ℝ) ≤ 2 ^ n := by
          calc (2 : ℝ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (by exact_mod_cast hn0)
        rw [pow_succ]
        linarith
      calc Real.log (2 ^ n * (1 - 0) + 2) ≤ Real.log (2 ^ (n + 1)) :=
            Real.log_le_log (by positivity) h3
        _ = (n + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
    have h4 : 0 ≤ ent (θ[|Aᶜ]) (cellIdx n) := ent_nonneg _
    have h5 : ent (θ[|Aᶜ]) (cellIdx n) ≤ (n + 1) * Real.log 2 := h1.trans h2
    calc θ.real Aᶜ * ent (θ[|Aᶜ]) (cellIdx n) ≤ η / 8 * ent (θ[|Aᶜ]) (cellIdx n) :=
          mul_le_mul_of_nonneg_right hAc.le h4
      _ ≤ η / 8 * ((n + 1) * Real.log 2) := mul_le_mul_of_nonneg_left h5 (by positivity)
  have hlog8 : Real.log 4 + Real.log 2 = 3 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hent : ent θ (cellIdx n) ≤ Real.log 2 *
      (3 + n * (d + η / 2) + η / 8 * (n + 1)) := by
    have := hsplit
    nlinarith
  rw [dyadicEntropy_eq_ent, div_le_iff₀ hl2]
  have hfin2 : 3 + η / 8 ≤ 3 * η / 8 * n := by
    have : 8 / η + 1 ≤ (n : ℝ) := hn2
    have h8 : 8 ≤ η * (n - 1) := by
      rw [div_add_one hη.ne', div_le_iff₀ hη] at this
      linarith
    nlinarith
  nlinarith

/-- The upper bound of (2.9): `H(θ, 𝒟_n) ≤ (d + η) n` for `n` large. -/
theorem young_upper {θ : Measure ℝ} [IsProbabilityMeasure θ] (hI : θ AnalyticESC.Iᶜ = 0)
    {d : ℝ} (hd : FractalGeometry.IsExactDim θ d) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, dyadicEntropy θ n ≤ (d + η) * n := by
  obtain ⟨N, hN⟩ := young_upper_aux hI hd (lt_min hη one_pos) (min_le_right η 1)
  refine ⟨N, fun n hn => (hN n hn).trans ?_⟩
  have : min η 1 ≤ η := min_le_left _ _
  nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

end FractalGeometry.Rapaport.Analytic
