module

public import AnalyticESC.Conjugation.Koenigs
public import AnalyticESC.Conjugation.Basic

@[expose] public section

/-!
# Compositions and periodic words

Compositions `f_w` along nonempty words lie in the class for a smaller `ε`; their functions
`Ĥ_{f_w}` of (5.1) are dual natural projections of periodic words; and if the dual natural
projections of the constant words agree, then all dual natural projections agree (the remark
after Theorem 1.12).
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace Word

variable {N : ℕ}

/-- An infinite word is its prefix of length `n` followed by its `n`-fold shift. -/
private theorem composite_inf_eq_prepend_ofFn (w : ℕ → Fin N) (n : ℕ) :
    inf w = (inf fun k => w (k + n)).prepend (List.ofFn fun k : Fin n => w k) := by
  show _ = inf fun k => if h : k < (List.ofFn fun k : Fin n => w k).length then _ else _
  congr 1
  funext k
  simp only [List.length_ofFn]
  split_ifs with hk
  · simp
  · congr 1
    omega

/-- A periodic word is its period followed by itself. -/
private theorem composite_inf_periodic_eq_prepend {m : ℕ} (hm : 0 < m) (v : Fin m → Fin N) :
    inf (periodic hm v) = (inf (periodic hm v)).prepend (List.ofFn v) := by
  show _ = inf fun n => if h : n < (List.ofFn v).length then _ else _
  congr 1
  funext n
  simp only [List.length_ofFn]
  split_ifs with hn
  · simp [periodic, Nat.mod_eq_of_lt hn]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + m := ⟨n - m, by omega⟩
    simp [periodic, Nat.add_mod_right]

end Word

/-- `List.ofFn (w ∘ Fin.rev) = (List.ofFn w)^←`. -/
private theorem composite_ofFn_comp_rev {α : Type*} {m : ℕ} (w : Fin m → α) :
    List.ofFn (w ∘ Fin.rev) = (List.ofFn w).reverse := by
  refine List.ext_getElem (by simp) fun n h1 h2 => ?_
  simp only [List.getElem_ofFn, Function.comp_apply, List.getElem_reverse, List.length_ofFn]
  exact congrArg w (Fin.ext (by simp only [Fin.val_rev]; omega))

/-- A bounded solution of `h(z) = R(z) + g'(z) h(g(z))` is unique when `g` maps `S` into itself
with `|g'| ≤ c < 1` on `S`. -/
private theorem composite_eqOn_of_functional_eq {S : Set ℂ} {g R A B : ℂ → ℂ} {c K : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hg : MapsTo g S S) (hgd : ∀ z ∈ S, ‖deriv g z‖ ≤ c)
    (hA : ∀ z ∈ S, A z = R z + deriv g z * A (g z))
    (hB : ∀ z ∈ S, B z = R z + deriv g z * B (g z)) (hK : ∀ z ∈ S, ‖A z - B z‖ ≤ K) :
    ∀ z ∈ S, A z = B z := by
  have key : ∀ n : ℕ, ∀ z ∈ S, ‖A z - B z‖ ≤ c ^ n * K := by
    intro n
    induction n with
    | zero => simpa using hK
    | succ n ih =>
      intro z hz
      rw [hA z hz, hB z hz, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, pow_succ', mul_assoc]
      exact mul_le_mul (hgd z hz) (ih _ (hg hz)) (norm_nonneg _) hc0
  intro z hz
  have hlim : Tendsto (fun n : ℕ => c ^ n * K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const K
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' hlim fun n => key n z hz))

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- Compositions along nonempty words lie in the class for some `ε' > 0`. -/
theorem inClass_comp {w : List (Fin N)} (hw : w ≠ []) :
    InClass (ε / 4) (Φ.comp w) := by
  have hε := Φ.ε_pos
  have hc : Φ.cmax ^ w.length < 1 :=
    pow_lt_one₀ Φ.cmax_nonneg Φ.cmax_lt_one (List.length_pos_iff.2 hw).ne'
  have hsub : nbhd (2 * (ε / 4)) ⊆ nbhd ε := nbhd_mono (by linarith)
  have hcl : closure (nbhd (ε / 4)) ⊆ closure (nbhd ε) := closure_mono (nbhd_mono (by linarith))
  refine ⟨(Φ.differentiableOn_comp w).mono hsub,
    fun x hx => Φ.im_comp_ofReal w (hsub hx), fun x hx => Φ.re_comp_mem_I w hx, ?_,
    fun z hz => Φ.deriv_comp_ne_zero w (hcl hz),
    fun z hz => (Φ.norm_deriv_comp_le w (hcl hz)).trans_lt hc⟩
  intro z hz
  have h1 : z ∈ cthickening (ε / 4) (((↑) : ℝ → ℂ) '' I) :=
    closure_thickening_subset_cthickening _ _ hz
  rw [isCompact_image_I.isClosed.cthickening_eq_biUnion_closedBall (by positivity)] at h1
  obtain ⟨_, ⟨x, hx, rfl⟩, hzx⟩ := mem_iUnion₂.1 h1
  rw [mem_closedBall, dist_eq_norm] at hzx
  have hzε : z ∈ nbhd ε := ball_subset_nbhd hx (by rw [mem_ball, dist_eq_norm]; linarith)
  have h2 := Φ.norm_comp_sub_le w hzε (ofReal_mem_nbhd hε hx)
  rw [Φ.comp_ofReal w hx] at h2
  refine ball_subset_nbhd (Φ.re_comp_mem_I w hx) ?_
  rw [mem_ball, dist_eq_norm]
  calc _ ≤ Φ.cmax ^ w.length * ‖z - x‖ := h2
    _ ≤ Φ.cmax ^ w.length * (ε / 4) :=
        mul_le_mul_of_nonneg_left hzx (pow_nonneg Φ.cmax_nonneg _)
    _ < ε / 4 := mul_lt_of_lt_one_left (by positivity) hc

/-- Compositions along nonempty words lie in the class for some positive radius. -/
theorem exists_inClass_comp {w : List (Fin N)} (hw : w ≠ []) :
    ∃ ε' > 0, InClass ε' (Φ.comp w) :=
  ⟨ε / 4, by linarith [Φ.ε_pos], Φ.inClass_comp hw⟩

/-- Iterates of `f_l` are compositions along repetitions of `l`. -/
private theorem composite_comp_flatten_replicate (l : List (Fin N)) (k : ℕ) :
    Φ.comp (List.replicate k l).flatten = (Φ.comp l)^[k] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, Φ.comp_append, ih, Function.iterate_succ']

/-- `Ĥ_{f_w} = H_{(w^←)^∞}` on `[0,1]`, where `w^←` is the reversed word. -/
theorem hatH_comp_eq_dualProj {m : ℕ} (hm : 0 < m) (w : Fin m → Fin N) :
    ∀ x ∈ I, hatH (Φ.comp (List.ofFn w)) x = Φ.dualProj (.inf (periodic hm (w ∘ Fin.rev))) x := by
  intro x hx
  set f := Φ.comp (List.ofFn w) with hf
  set c := Φ.cmax ^ m with hc
  have hc0 : 0 ≤ c := pow_nonneg Φ.cmax_nonneg m
  have hc1 : c < 1 := pow_lt_one₀ Φ.cmax_nonneg Φ.cmax_lt_one hm.ne'
  obtain ⟨M, hM0, hM⟩ := Φ.exists_norm_dualProj_le
  have hit : ∀ k, f^[k] = Φ.comp (List.replicate k (List.ofFn w)).flatten := fun k =>
    (Φ.composite_comp_flatten_replicate _ k).symm
  have hfm : MapsTo f (closure (nbhd ε)) (closure (nbhd ε)) := Φ.mapsTo_comp_closure _
  have hfd : ∀ z ∈ closure (nbhd ε), ‖deriv f z‖ ≤ c := by
    intro z hz
    have := Φ.norm_deriv_comp_le (List.ofFn w) hz
    rwa [List.length_ofFn] at this
  -- `f''/f' = H_{w^←}` by (2.7)
  have hR : ∀ z ∈ closure (nbhd ε),
      deriv (deriv f) z / deriv f z = Φ.dualProj (.fin (List.ofFn w).reverse) z :=
    fun z hz => (Φ.dualProj_fin_reverse _ hz).symm
  -- the terms of the series (5.1) for `Ĥ_f`
  have hT : ∀ k, ∀ z ∈ closure (nbhd ε),
      ‖deriv (deriv f) (f^[k] z) / deriv f (f^[k] z) * deriv (f^[k]) z‖ ≤ M * c ^ k := by
    intro k z hz
    have hz' : f^[k] z ∈ closure (nbhd ε) := by rw [hit k]; exact Φ.mapsTo_comp_closure _ hz
    have h1 : ‖deriv (f^[k]) z‖ ≤ c ^ k := by
      have := Φ.norm_deriv_comp_le (List.replicate k (List.ofFn w)).flatten hz
      rw [← hit k] at this
      simpa [hc, ← pow_mul, mul_comm] using this
    rw [norm_mul, hR _ hz']
    exact mul_le_mul (hM _ _ hz') h1 (norm_nonneg _) hM0
  have hTs : ∀ z ∈ closure (nbhd ε),
      Summable fun k => deriv (deriv f) (f^[k] z) / deriv f (f^[k] z) * deriv (f^[k]) z :=
    fun z hz => Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hc0 hc1).mul_left M) fun k => hT k z hz
  have hTsucc : ∀ k, ∀ z ∈ closure (nbhd ε),
      deriv (deriv f) (f^[k + 1] z) / deriv f (f^[k + 1] z) * deriv (f^[k + 1]) z =
        deriv f z * (deriv (deriv f) (f^[k] (f z)) / deriv f (f^[k] (f z)) *
          deriv (f^[k]) (f z)) := by
    intro k z hz
    have hd : deriv (f^[k + 1]) z = deriv (f^[k]) (f z) * deriv f z := by
      rw [Function.iterate_succ]
      refine deriv_comp z ?_ (Φ.differentiableAt_comp _ hz)
      rw [hit k]
      exact Φ.differentiableAt_comp _ (hfm hz)
    rw [hd, Function.iterate_succ_apply]
    ring
  -- the functional equations
  have hA : ∀ z ∈ closure (nbhd ε),
      hatH f z = deriv (deriv f) z / deriv f z + deriv f z * hatH f (f z) := by
    intro z hz
    rw [hatH, hatH, (hTs z hz).tsum_eq_zero_add, ← tsum_mul_left]
    congr 1
    · simp
    · exact tsum_congr fun k => hTsucc k z hz
  have hB : ∀ z ∈ closure (nbhd ε),
      Φ.dualProj (.inf (periodic hm (w ∘ Fin.rev))) z =
        deriv (deriv f) z / deriv f z +
          deriv f z * Φ.dualProj (.inf (periodic hm (w ∘ Fin.rev))) (f z) := by
    intro z hz
    have h1 := Φ.dualProj_prepend (List.ofFn (w ∘ Fin.rev)) (.inf (periodic hm (w ∘ Fin.rev))) hz
    rw [← Word.composite_inf_periodic_eq_prepend hm (w ∘ Fin.rev), composite_ofFn_comp_rev,
      List.reverse_reverse] at h1
    rw [hR z hz]
    exact h1
  -- uniqueness of bounded solutions
  have hK : ∀ z ∈ closure (nbhd ε),
      ‖hatH f z - Φ.dualProj (.inf (periodic hm (w ∘ Fin.rev))) z‖ ≤ M * (1 - c)⁻¹ + M := by
    intro z hz
    refine (norm_sub_le _ _).trans (add_le_add ?_ (hM _ z hz))
    exact tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hc0 hc1).mul_left M)
      fun k => hT k z hz
  exact composite_eqOn_of_functional_eq hc0 hc1 hfm hfd hA hB hK _
    (subset_closure (ofReal_mem_nbhd Φ.ε_pos hx))

/-- If `H_{k^∞} = H_{k₀^∞}` on `[0,1]` for every letter `k`, then `H_i = H_{k₀^∞}` on `B_ε`
for every `i ∈ Σ`. -/
private theorem composite_dualProj_inf_eq (k₀ : Fin N)
    (h : ∀ k : Fin N, ∀ x ∈ I,
      Φ.dualProj (.inf fun _ => k) x = Φ.dualProj (.inf fun _ => k₀) x)
    (i : ℕ → Fin N) {z : ℂ} (hz : z ∈ nbhd ε) :
    Φ.dualProj (.inf i) z = Φ.dualProj (.inf fun _ => k₀) z := by
  set G := Φ.dualProj (.inf fun _ => k₀) with hG
  -- the identity theorem: `H_{k^∞} = G` on `B_ε`
  have hk : ∀ k, EqOn (Φ.dualProj (.inf fun _ => k)) G (nbhd ε) := fun k =>
    eqOn_nbhd_of_eqOn_Icc Φ.ε_pos (Φ.differentiableOn_dualProj _) (Φ.differentiableOn_dualProj _)
      zero_lt_one subset_rfl (h k)
  -- `G` is a fixed point of every dual operator on `B_ε`
  have hfix : ∀ k, ∀ z ∈ nbhd ε, G z = deriv (Φ.f k) z * G (Φ.f k z) + Φ.nonlin k z := by
    intro k z hz
    have h1 := Φ.dualProj_prepend [k] (.inf fun _ => k) (subset_closure hz)
    have h2 : (Word.inf fun _ : ℕ => k).prepend [k] = .inf fun _ => k := by
      simpa using (Word.composite_inf_eq_prepend_ofFn (fun _ : ℕ => k) 1).symm
    rw [h2, List.reverse_singleton, dualProj_singleton] at h1
    simp only [comp_cons, comp_nil, Function.comp_id] at h1
    rw [← hk k hz, h1, hk k (Φ.mapsTo_f k hz)]
    ring
  have hcomp : ∀ (a : List (Fin N)), ∀ z ∈ nbhd ε, Φ.dualComp a G z = G z := by
    intro a
    induction a with
    | nil => intro z _; rfl
    | cons k a ih =>
      intro z hz
      show Φ.dualOp k (Φ.dualComp a G) z = G z
      rw [dualOp, ih _ (Φ.mapsTo_f k hz), hfix k z hz]
  obtain ⟨M, hM0, hM⟩ := Φ.exists_norm_dualProj_le
  have key : ∀ n : ℕ, ‖Φ.dualProj (.inf i) z - G z‖ ≤ Φ.cmax ^ n * (M + M) := by
    intro n
    set a := List.ofFn fun k : Fin n => i k
    have hz' := Φ.mapsTo_comp_closure a.reverse (subset_closure hz)
    have h1 := Φ.dualProj_prepend a (.inf fun k => i (k + n)) (subset_closure hz)
    rw [← Word.composite_inf_eq_prepend_ofFn i n] at h1
    have h2 := Φ.dualComp_apply a G hz
    rw [hcomp a z hz] at h2
    rw [h1, h2, add_comm (deriv _ z * G _), add_sub_add_left_eq_sub, ← mul_sub, norm_mul]
    have h3 := Φ.norm_deriv_comp_le a.reverse (subset_closure hz)
    rw [List.length_reverse, List.length_ofFn] at h3
    exact mul_le_mul h3 ((norm_sub_le _ _).trans (add_le_add (hM _ _ hz') (hM _ _ hz')))
      (norm_nonneg _) (pow_nonneg Φ.cmax_nonneg _)
  have hlim : Tendsto (fun n : ℕ => Φ.cmax ^ n * (M + M)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_const
      (M + M)
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' hlim key))

/-- If `H_{k^∞}` is the same for every letter `k`, then `H_i` is the same for every `i ∈ Σ`. -/
theorem dualProj_eq_of_forall_const
    (h : ∀ k l : Fin N, ∀ x ∈ I,
      Φ.dualProj (.inf fun _ => k) x = Φ.dualProj (.inf fun _ => l) x) :
    ∀ i j : ℕ → Fin N, ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x := by
  intro i j x hx
  have hx' := ofReal_mem_nbhd Φ.ε_pos hx
  rw [Φ.composite_dualProj_inf_eq (i 0) (fun k => h k (i 0)) i hx',
    Φ.composite_dualProj_inf_eq (i 0) (fun k => h k (i 0)) j hx']

end IFS

end AnalyticESC
