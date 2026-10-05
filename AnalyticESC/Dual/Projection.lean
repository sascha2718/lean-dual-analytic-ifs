module

public import AnalyticESC.Basic
public import AnalyticESC.Words

@[expose] public section

/-!
# The dual natural projection

Convergence and holomorphy of the series (1.4) defining `H_w`, its uniform bounds, the cocycle
identity for prepended words, the formula (2.7) `H_{v^←} = f_v''/f_v'` for finite words, and
Lemma 2.4 (a), (b): `H_w ∈ C^ω_ε([0,1])` and Hölder dependence on the word.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-! ## The terms of the series -/

theorem dualTerm_of_get?_eq_none {w : Word N} {n : ℕ} (h : w.get? n = none) (z : ℂ) :
    Φ.dualTerm w n z = 0 := by
  simp [dualTerm, h]

theorem dualTerm_of_get?_eq_some {w : Word N} {n : ℕ} {i : Fin N} (h : w.get? n = some i)
    (z : ℂ) :
    Φ.dualTerm w n z =
      Φ.nonlin i (Φ.comp (w.take n).reverse z) * deriv (Φ.comp (w.take n).reverse) z := by
  simp [dualTerm, h]

/-- If `w` has a letter in position `n`, then its prefix of length `n` has length `n`. -/
private theorem length_take_of_get?_eq_some {w : Word N} {n : ℕ} {i : Fin N}
    (h : w.get? n = some i) : (w.take n).length = n := by
  cases w with
  | fin w =>
    simp only [Word.get?_fin] at h
    have := (List.getElem?_eq_some_iff.1 h).1
    simp only [Word.take_fin, List.length_take]
    omega
  | inf w => simp

/-- The terms of (1.4) decay geometrically on `cl B_ε`, uniformly in the word. -/
theorem exists_dualTerm_bound : ∃ C, 0 ≤ C ∧ ∀ (w : Word N) (n : ℕ), ∀ z ∈ closure (nbhd ε),
    ‖Φ.dualTerm w n z‖ ≤ C * Φ.cmax ^ n := by
  obtain ⟨C, hC0, hC⟩ := Φ.exists_nonlin_bound
  refine ⟨C, hC0, fun w n z hz => ?_⟩
  cases h : w.get? n with
  | none =>
    rw [Φ.dualTerm_of_get?_eq_none h, norm_zero]
    exact mul_nonneg hC0 (pow_nonneg Φ.cmax_nonneg n)
  | some i =>
    rw [Φ.dualTerm_of_get?_eq_some h, norm_mul]
    have h1 := hC i _ (Φ.mapsTo_comp_closure (w.take n).reverse hz)
    have h2 := Φ.norm_deriv_comp_le (w.take n).reverse hz
    rw [List.length_reverse, length_take_of_get?_eq_some h] at h2
    exact mul_le_mul h1 h2 (norm_nonneg _) hC0

theorem summable_dualTerm (w : Word N) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    Summable fun n => Φ.dualTerm w n z := by
  obtain ⟨C, -, hC⟩ := Φ.exists_dualTerm_bound
  exact Summable.of_norm_bounded
    ((summable_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left C)
    fun n => hC w n z hz

@[simp] theorem dualProj_nil : Φ.dualProj (.fin []) = 0 := by
  funext z
  simp [dualProj, dualTerm]

/-- For a finite word, `H_a` is the finite sum of its `|a|` terms. -/
theorem dualProj_fin_eq_sum (a : List (Fin N)) (z : ℂ) :
    Φ.dualProj (.fin a) z = ∑ n ∈ Finset.range a.length, Φ.dualTerm (.fin a) n z := by
  refine tsum_eq_sum fun n hn => Φ.dualTerm_of_get?_eq_none ?_ z
  simp only [Finset.mem_range, not_lt] at hn
  simp [hn]

theorem dualProj_singleton (i : Fin N) (z : ℂ) : Φ.dualProj (.fin [i]) z = Φ.nonlin i z := by
  rw [dualProj_fin_eq_sum]
  simp [dualTerm]

/-! ## Bounds -/

/-- The uniform bound `‖H_w‖ ≤ M` on `cl B_ε`. -/
theorem exists_norm_dualProj_le :
    ∃ M, 0 ≤ M ∧ ∀ w : Word N, ∀ z ∈ closure (nbhd ε), ‖Φ.dualProj w z‖ ≤ M := by
  obtain ⟨C, hC0, hC⟩ := Φ.exists_dualTerm_bound
  refine ⟨C * (1 - Φ.cmax)⁻¹,
    mul_nonneg hC0 (inv_nonneg.2 (sub_nonneg.2 Φ.cmax_lt_one.le)), fun w z hz => ?_⟩
  exact tsum_of_norm_bounded
    ((hasSum_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left C) fun n => hC w n z hz

/-! ## Holomorphy and realness -/

theorem differentiableOn_dualTerm (w : Word N) (n : ℕ) :
    DifferentiableOn ℂ (Φ.dualTerm w n) (nbhd ε) := by
  cases h : w.get? n with
  | none =>
    have : Φ.dualTerm w n = fun _ => 0 := funext (Φ.dualTerm_of_get?_eq_none h)
    rw [this]
    exact differentiableOn_const 0
  | some i =>
    have : Φ.dualTerm w n = fun z => Φ.nonlin i (Φ.comp (w.take n).reverse z) *
        deriv (Φ.comp (w.take n).reverse) z := funext (Φ.dualTerm_of_get?_eq_some h)
    rw [this]
    obtain ⟨U, -, hU, -, hnl⟩ := Φ.exists_differentiableOn_nonlin i
    obtain ⟨V, hVo, hV, hc⟩ := Φ.exists_differentiableOn_comp (w.take n).reverse
    refine DifferentiableOn.mul ?_ ?_
    · exact hnl.comp (Φ.differentiableOn_comp _) fun z hz =>
        hU (subset_closure (Φ.mapsTo_comp _ hz))
    · exact (hc.deriv hVo).mono (subset_closure.trans hV)

theorem differentiableOn_dualProj (w : Word N) : DifferentiableOn ℂ (Φ.dualProj w) (nbhd ε) := by
  obtain ⟨C, -, hC⟩ := Φ.exists_dualTerm_bound
  exact Complex.differentiableOn_tsum_of_summable_norm
    ((summable_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left C)
    (fun n => Φ.differentiableOn_dualTerm w n) (isOpen_nbhd ε)
    fun n z hz => hC w n z (subset_closure hz)

/-- Every term of (1.4) is continuous on `cl B_ε`. -/
theorem continuousOn_dualTerm (w : Word N) (n : ℕ) :
    ContinuousOn (Φ.dualTerm w n) (closure (nbhd ε)) := by
  cases h : w.get? n with
  | none =>
    have : Φ.dualTerm w n = fun _ => 0 := funext (Φ.dualTerm_of_get?_eq_none h)
    rw [this]
    exact continuousOn_const
  | some i =>
    have : Φ.dualTerm w n = fun z => Φ.nonlin i (Φ.comp (w.take n).reverse z) *
        deriv (Φ.comp (w.take n).reverse) z := funext (Φ.dualTerm_of_get?_eq_some h)
    rw [this]
    obtain ⟨U, -, hU, -, hnl⟩ := Φ.exists_differentiableOn_nonlin i
    obtain ⟨V, hVo, hV, hc⟩ := Φ.exists_differentiableOn_comp (w.take n).reverse
    exact (hnl.continuousOn.comp (hc.continuousOn.mono hV)
      (fun z hz => hU (Φ.mapsTo_comp_closure _ hz))).mul
      ((hc.deriv hVo).continuousOn.mono hV)

/-- The geometric bound on `cl B_ε` makes (1.4) a uniformly convergent series of continuous
functions there. In particular, `H_w` has the boundary continuity required in Section 2.1. -/
theorem continuousOn_dualProj (w : Word N) :
    ContinuousOn (Φ.dualProj w) (closure (nbhd ε)) := by
  obtain ⟨C, -, hC⟩ := Φ.exists_dualTerm_bound
  exact continuousOn_tsum (Φ.continuousOn_dualTerm w)
    ((summable_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left C) (hC w)

theorem im_dualTerm_ofReal (w : Word N) (n : ℕ) {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) :
    (Φ.dualTerm w n t).im = 0 := by
  cases h : w.get? n with
  | none => simp [Φ.dualTerm_of_get?_eq_none h]
  | some i =>
    rw [Φ.dualTerm_of_get?_eq_some h]
    have h1 : Φ.comp (w.take n).reverse t = ((Φ.comp (w.take n).reverse t).re : ℂ) := by
      apply Complex.ext <;> simp [Φ.im_comp_ofReal _ ht]
    have h2 : ((Φ.comp (w.take n).reverse t).re : ℂ) ∈ nbhd ε := h1 ▸ Φ.mapsTo_comp _ ht
    have h3 := Φ.im_nonlin_ofReal i h2
    rw [← h1] at h3
    simp [Complex.mul_im, h3, Φ.im_deriv_comp_ofReal _ ht]

theorem im_dualProj_ofReal (w : Word N) {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) :
    (Φ.dualProj w t).im = 0 := by
  rw [dualProj, Complex.im_tsum (Φ.summable_dualTerm w (subset_closure ht))]
  simp [Φ.im_dualTerm_ofReal w _ ht]

/-! ## The cocycle identity and (2.7) -/

/-- The cocycle identity: `H_{a w}(z) = H_a(z) + f_{a^←}'(z) · H_w(f_{a^←}(z))`, where
`f_{a^←} = f_{a_{|a|}} ∘ ⋯ ∘ f_{a_1}`. -/
theorem dualProj_prepend (a : List (Fin N)) (w : Word N) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    Φ.dualProj (w.prepend a) z =
      Φ.dualProj (.fin a) z + deriv (Φ.comp a.reverse) z * Φ.dualProj w (Φ.comp a.reverse z) := by
  rw [dualProj_fin_eq_sum]
  unfold dualProj
  rw [← (Φ.summable_dualTerm (w.prepend a) hz).sum_add_tsum_nat_add a.length, ← tsum_mul_left]
  congr 1
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : n < a.length := Finset.mem_range.1 hn
    have hg : (w.prepend a).get? n = (Word.fin a).get? n := Word.get?_prepend_of_lt a w hn'
    have ht : (w.prepend a).take n = (Word.fin a).take n := Word.take_prepend_of_le a w hn'.le
    cases h : (Word.fin a).get? n with
    | none => rw [Φ.dualTerm_of_get?_eq_none (hg.trans h), Φ.dualTerm_of_get?_eq_none h]
    | some i => rw [Φ.dualTerm_of_get?_eq_some (hg.trans h), Φ.dualTerm_of_get?_eq_some h, ht]
  · refine tsum_congr fun m => ?_
    have hg : (w.prepend a).get? (m + a.length) = w.get? m := by
      rw [add_comm]; exact Word.get?_prepend_add a w m
    have ht : (w.prepend a).take (m + a.length) = a ++ w.take m := by
      rw [add_comm]; exact Word.take_prepend_add a w m
    cases h : w.get? m with
    | none =>
      rw [Φ.dualTerm_of_get?_eq_none (hg.trans h), Φ.dualTerm_of_get?_eq_none h, mul_zero]
    | some i =>
      rw [Φ.dualTerm_of_get?_eq_some (hg.trans h), Φ.dualTerm_of_get?_eq_some h, ht,
        List.reverse_append, Φ.deriv_comp_append _ _ hz, Φ.comp_append, Function.comp_apply]
      ring

/-- The second derivative of `f_i ∘ f_v` by the chain rule. -/
theorem deriv_deriv_comp_cons (i : Fin N) (v : List (Fin N)) {z : ℂ}
    (hz : z ∈ closure (nbhd ε)) :
    deriv (deriv (Φ.comp (i :: v))) z =
      deriv (deriv (Φ.f i)) (Φ.comp v z) * deriv (Φ.comp v) z ^ 2 +
        deriv (Φ.f i) (Φ.comp v z) * deriv (deriv (Φ.comp v)) z := by
  obtain ⟨U, hUo, hU, hd⟩ := Φ.exists_differentiableOn_comp v
  have hfi := Φ.differentiableOn_f i
  have ho2 := isOpen_nbhd (2 * ε)
  have hW : IsOpen (U ∩ Φ.comp v ⁻¹' nbhd (2 * ε)) :=
    hd.continuousOn.isOpen_inter_preimage hUo ho2
  have hzW : z ∈ U ∩ Φ.comp v ⁻¹' nbhd (2 * ε) :=
    ⟨hU hz, closure_nbhd_subset_two (Φ.mapsTo_comp_closure v hz)⟩
  have heq : deriv (Φ.comp (i :: v)) =ᶠ[𝓝 z]
      fun u => deriv (Φ.f i) (Φ.comp v u) * deriv (Φ.comp v) u := by
    filter_upwards [hW.mem_nhds hzW] with u hu
    rw [Φ.comp_cons]
    exact deriv_comp u ((hfi _ hu.2).differentiableAt (ho2.mem_nhds hu.2))
      ((hd u hu.1).differentiableAt (hUo.mem_nhds hu.1))
  have hdf : DifferentiableAt ℂ (deriv (Φ.f i)) (Φ.comp v z) :=
    ((hfi.deriv ho2) _ hzW.2).differentiableAt (ho2.mem_nhds hzW.2)
  have hhd : DifferentiableAt ℂ (Φ.comp v) z := (hd z hzW.1).differentiableAt (hUo.mem_nhds hzW.1)
  have hdh : DifferentiableAt ℂ (deriv (Φ.comp v)) z :=
    ((hd.deriv hUo) z hzW.1).differentiableAt (hUo.mem_nhds hzW.1)
  rw [heq.deriv_eq]
  exact ((hdf.hasDerivAt.comp z hhd.hasDerivAt).mul hdh.hasDerivAt).deriv.trans (by rw [Function.comp_apply]; ring)

/-- (2.7): `H_{v^←} = f_v''/f_v'` for a finite word `v`. -/
theorem dualProj_fin_reverse (v : List (Fin N)) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    Φ.dualProj (.fin v.reverse) z = deriv (deriv (Φ.comp v)) z / deriv (Φ.comp v) z := by
  induction v with
  | nil => simp [deriv_id']
  | cons i v ih =>
    have hfin : (Word.fin [i]).prepend v.reverse = Word.fin (i :: v).reverse := by
      rw [List.reverse_cons]; rfl
    rw [← hfin, Φ.dualProj_prepend _ _ hz, ih, List.reverse_reverse, dualProj_singleton,
      Φ.deriv_deriv_comp_cons i v hz, Φ.deriv_comp_cons i v hz, nonlin]
    have h1 : deriv (Φ.f i) (Φ.comp v z) ≠ 0 :=
      (Φ.inClass i).deriv_ne_zero _ (Φ.mapsTo_comp_closure v hz)
    have h2 : deriv (Φ.comp v) z ≠ 0 := Φ.deriv_comp_ne_zero v hz
    field_simp
    ring

/-! ## Lemma 2.4 -/

/-- Uniform bound for `H_w` on `cl B_ε` and the bound `2M c_max^m` for words sharing a prefix of
length `m`. -/
theorem exists_dualProj_bounds :
    ∃ M, 0 ≤ M ∧ (∀ w : Word N, ∀ z ∈ closure (nbhd ε), ‖Φ.dualProj w z‖ ≤ M) ∧
      ∀ (i j : Word N) (m : ℕ), (m : ℕ∞) ≤ i.commonPrefixLength j →
        ∀ z ∈ closure (nbhd ε), ‖Φ.dualProj i z - Φ.dualProj j z‖ ≤ 2 * M * Φ.cmax ^ m := by
  obtain ⟨M, hM0, hM⟩ := Φ.exists_norm_dualProj_le
  refine ⟨M, hM0, hM, fun i j m hm z hz => ?_⟩
  obtain ⟨a, i', j', ha, rfl, rfl⟩ := Word.exists_eq_prepend hm
  rw [Φ.dualProj_prepend a i' hz, Φ.dualProj_prepend a j' hz, add_sub_add_left_eq_sub,
    ← mul_sub, norm_mul]
  have hz' := Φ.mapsTo_comp_closure a.reverse hz
  have h1 := Φ.norm_deriv_comp_le a.reverse hz
  rw [List.length_reverse, ha] at h1
  have h2 : ‖Φ.dualProj i' (Φ.comp a.reverse z) - Φ.dualProj j' (Φ.comp a.reverse z)‖ ≤
      2 * M := by
    calc _ ≤ ‖Φ.dualProj i' (Φ.comp a.reverse z)‖ + ‖Φ.dualProj j' (Φ.comp a.reverse z)‖ :=
          norm_sub_le _ _
      _ ≤ M + M := add_le_add (hM _ _ hz') (hM _ _ hz')
      _ = 2 * M := by ring
  calc _ ≤ Φ.cmax ^ m * (2 * M) :=
        mul_le_mul h1 h2 (norm_nonneg _) (pow_nonneg Φ.cmax_nonneg _)
    _ = 2 * M * Φ.cmax ^ m := by ring

/-- Lemma 2.4, first claim: `H_i ∈ C^ω_ε([0,1])` for `i ∈ Σ`. -/
theorem dualProj_mem_analyticSpace (w : ℕ → Fin N) :
    toNbhd ε (Φ.dualProj (.inf w)) ∈ analyticSpace ε :=
  ⟨Φ.dualProj (.inf w), Φ.differentiableOn_dualProj _,
    Φ.continuousOn_dualProj _,
    fun _ hx => Φ.im_dualProj_ofReal _ (ofReal_mem_nbhd Φ.ε_pos hx), rfl⟩

/-- Lemma 2.4, second claim: `‖H_i - H_j‖_∞ ≤ c_max^{|i ∧ j|} K` on `B_ε` for distinct
`i, j ∈ Σ`. -/
theorem exists_dualProj_holder :
    ∃ K > 0, ∀ i j : ℕ → Fin N, i ≠ j → ∀ z ∈ nbhd ε,
      ‖Φ.dualProj (.inf i) z - Φ.dualProj (.inf j) z‖ ≤
        Φ.cmax ^ ((Word.inf i).commonPrefixLength (.inf j)).toNat * K := by
  obtain ⟨M, hM0, -, hM⟩ := Φ.exists_dualProj_bounds
  refine ⟨2 * M + 1, by linarith, fun i j _ z hz => ?_⟩
  set m := ((Word.inf i).commonPrefixLength (.inf j)).toNat
  have hc : 0 ≤ Φ.cmax ^ m := pow_nonneg Φ.cmax_nonneg m
  calc _ ≤ 2 * M * Φ.cmax ^ m :=
        hM _ _ m (ENat.natCast_toNat_le_self _) z (subset_closure hz)
    _ ≤ Φ.cmax ^ m * (2 * M + 1) := by nlinarith

end IFS

end AnalyticESC
