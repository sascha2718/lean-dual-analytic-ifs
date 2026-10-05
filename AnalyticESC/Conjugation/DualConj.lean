module

public import AnalyticESC.Conjugation.PeriodicPoints

@[expose] public section

/-!
# Theorem 2.3

`Φ` is conjugated to a self-similar system exactly when the attractor of its dual IFS is a
singleton, and sub-conjugated exactly when `F_i` and `F_j` have a common fixed point for distinct
words `i, j` of the same length.
-/

namespace AnalyticESC

open Set Metric Filter Topology
open scoped UniformConvergence

/-- Restrictions agree as soon as the maps agree on `B_ε`. -/
private theorem dualConj_toNbhd_congr {ε : ℝ} {g h : ℂ → ℂ} (hgh : ∀ z ∈ nbhd ε, g z = h z) :
    toNbhd ε g = toNbhd ε h := by
  unfold toNbhd
  congr 1
  funext z
  exact hgh z z.2

/-- The periodic word `i i i ⋯` is fixed by prepending `i`. -/
private theorem prepend_ofFn_periodic {N m : ℕ} (hm : 0 < m) (i : Fin m → Fin N) :
    (Word.inf (periodic hm i)).prepend (List.ofFn i) = .inf (periodic hm i) := by
  simp only [Word.prepend, List.length_ofFn]
  congr 1
  funext n
  split_ifs with hn
  · simp [periodic, Nat.mod_eq_of_lt hn]
  · simp only [periodic]
    congr 2
    exact (Nat.mod_eq_sub_mod (not_lt.1 hn)).symm

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

private theorem dualCompOn_nil' (u : nbhd ε →ᵤ ℂ) : Φ.dualCompOn [] u = u := rfl

private theorem dualCompOn_cons' (i : Fin N) (w : List (Fin N)) (u : nbhd ε →ᵤ ℂ) :
    Φ.dualCompOn (i :: w) u = Φ.dualOpU i (Φ.dualCompOn w u) := rfl

private theorem dualCompOn_toNbhd' (w : List (Fin N)) (g : ℂ → ℂ) :
    Φ.dualCompOn w (toNbhd ε g) = toNbhd ε (Φ.dualComp w g) := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [dualCompOn_cons', ih]; rfl

/-- `F_a H_w = H_{a w}` on `B_ε`. -/
private theorem dualCompOn_toNbhd_dualProj' (a : List (Fin N)) (w : Word N) :
    Φ.dualCompOn a (toNbhd ε (Φ.dualProj w)) = toNbhd ε (Φ.dualProj (w.prepend a)) := by
  rw [dualCompOn_toNbhd']
  refine dualConj_toNbhd_congr fun z hz => ?_
  rw [Φ.dualComp_apply a _ hz, Φ.dualProj_prepend a w (subset_closure hz), add_comm]

/-- `F_i H_{i i i ⋯} = H_{i i i ⋯}`. -/
private theorem dualCompOn_periodic {m : ℕ} (hm : 0 < m) (i : Fin m → Fin N) :
    Φ.dualCompOn (List.ofFn i) (toNbhd ε (Φ.dualProj (.inf (periodic hm i)))) =
      toNbhd ε (Φ.dualProj (.inf (periodic hm i))) := by
  rw [dualCompOn_toNbhd_dualProj', prepend_ofFn_periodic]

private theorem toFun_dualOpU' (i : Fin N) (u : nbhd ε →ᵤ ℂ) (z : nbhd ε) :
    UniformFun.toFun (Φ.dualOpU i u) z =
      deriv (Φ.f i) z * UniformFun.toFun u ⟨Φ.f i z, Φ.mapsTo_f i z.2⟩ + Φ.nonlin i z := rfl

/-- `F_i` contracts the supremum distance by `c_max`. -/
private theorem norm_dualOpU_sub_le' (i : Fin N) {u v : nbhd ε →ᵤ ℂ} {C : ℝ}
    (h : ∀ z, ‖UniformFun.toFun u z - UniformFun.toFun v z‖ ≤ C) (z : nbhd ε) :
    ‖UniformFun.toFun (Φ.dualOpU i u) z - UniformFun.toFun (Φ.dualOpU i v) z‖ ≤ Φ.cmax * C := by
  rw [toFun_dualOpU', toFun_dualOpU', add_sub_add_right_eq_sub, ← mul_sub, norm_mul]
  exact mul_le_mul (Φ.norm_deriv_le_cmax i (subset_closure z.2)) (h _) (norm_nonneg _)
    Φ.cmax_nonneg

/-- `F_w` contracts the supremum distance by `c_max^{|w|}`. -/
private theorem norm_dualCompOn_sub_le' (w : List (Fin N)) {u v : nbhd ε →ᵤ ℂ} {C : ℝ}
    (h : ∀ z, ‖UniformFun.toFun u z - UniformFun.toFun v z‖ ≤ C) (z : nbhd ε) :
    ‖UniformFun.toFun (Φ.dualCompOn w u) z - UniformFun.toFun (Φ.dualCompOn w v) z‖ ≤
      Φ.cmax ^ w.length * C := by
  induction w generalizing z with
  | nil =>
    rw [dualCompOn_nil', dualCompOn_nil', List.length_nil, pow_zero, one_mul]
    exact h z
  | cons i w ih =>
    rw [dualCompOn_cons', dualCompOn_cons', List.length_cons, pow_succ', mul_assoc]
    exact Φ.norm_dualOpU_sub_le' i ih z

/-- A fixed point of `F_a` in `C^ω_ε([0,1])`, for a nonempty word `a`, is bounded on `B_ε`: it
equals `F_a g = f_{a^←}' · (g ∘ f_{a^←}) + H_a`, and `f_{a^←}` maps `B_ε` into the compact
subset `f_{a_{|a|}}(cl B_ε)` of `B_ε`, on which `g` is bounded. -/
private theorem exists_bound_of_dualCompOn_eq {a : List (Fin N)} (ha : a ≠ [])
    {u : nbhd ε →ᵤ ℂ} (hu : u ∈ analyticSpace ε) (hfix : Φ.dualCompOn a u = u) :
    ∃ B, ∀ z, ‖UniformFun.toFun u z‖ ≤ B := by
  obtain ⟨g, hg, -, -, rfl⟩ := hu
  obtain ⟨M, -, hM, -⟩ := Φ.exists_dualProj_bounds
  obtain ⟨k, b, hkb⟩ := List.exists_cons_of_ne_nil (List.reverse_ne_nil_iff.2 ha)
  have hK : IsCompact (Φ.f k '' closure (nbhd ε)) :=
    (isCompact_closure_nbhd ε).image_of_continuousOn
      ((Φ.differentiableOn_f k).continuousOn.mono closure_nbhd_subset_two)
  have hKs : Φ.f k '' closure (nbhd ε) ⊆ nbhd ε := (Φ.inClass k).mapsTo.image_subset
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hg.continuousOn.mono hKs)
  refine ⟨Φ.cmax ^ a.reverse.length * C + M, fun z => ?_⟩
  have hz : (z : ℂ) ∈ closure (nbhd ε) := subset_closure z.2
  rw [← hfix, dualCompOn_toNbhd']
  change ‖Φ.dualComp a g z‖ ≤ _
  rw [Φ.dualComp_apply a g z.2]
  refine (norm_add_le _ _).trans (add_le_add ?_ (hM _ _ hz))
  rw [norm_mul]
  refine mul_le_mul (Φ.norm_deriv_comp_le _ hz) (hC _ ?_) (norm_nonneg _)
    (pow_nonneg Φ.cmax_nonneg _)
  rw [hkb, comp_cons, Function.comp_apply]
  exact mem_image_of_mem _ (Φ.mapsTo_comp_closure b hz)

/-- `F_a` has at most one fixed point in `C^ω_ε([0,1])` for a nonempty word `a`: a fixed point
equals any `H_w` fixed by `F_a`. -/
private theorem eq_toNbhd_dualProj_of_dualCompOn_eq {a : List (Fin N)} (ha : a ≠ [])
    {u : nbhd ε →ᵤ ℂ} (hu : u ∈ analyticSpace ε) (hfix : Φ.dualCompOn a u = u) {w : Word N}
    (hw : Φ.dualCompOn a (toNbhd ε (Φ.dualProj w)) = toNbhd ε (Φ.dualProj w)) :
    u = toNbhd ε (Φ.dualProj w) := by
  obtain ⟨B, hB⟩ := Φ.exists_bound_of_dualCompOn_eq ha hu hfix
  obtain ⟨M, -, hM, -⟩ := Φ.exists_dualProj_bounds
  set v := toNbhd ε (Φ.dualProj w)
  have hc0 : 0 ≤ Φ.cmax ^ a.length := pow_nonneg Φ.cmax_nonneg _
  have hc1 : Φ.cmax ^ a.length < 1 :=
    pow_lt_one₀ Φ.cmax_nonneg Φ.cmax_lt_one (List.length_pos_iff.2 ha).ne'
  have key : ∀ n z, ‖UniformFun.toFun u z - UniformFun.toFun v z‖ ≤
      (Φ.cmax ^ a.length) ^ n * (B + M) := by
    intro n
    induction n with
    | zero =>
      intro z
      rw [pow_zero, one_mul]
      exact (norm_sub_le _ _).trans (add_le_add (hB z) (hM _ _ (subset_closure z.2)))
    | succ n ih =>
      intro z
      rw [← hfix, ← hw, pow_succ', mul_assoc]
      exact Φ.norm_dualCompOn_sub_le' a ih z
  apply UniformFun.toFun.injective
  funext z
  refine sub_eq_zero.1 (norm_le_zero_iff.1 ?_)
  have hlim : Tendsto (fun n : ℕ => (Φ.cmax ^ a.length) ^ n * (B + M)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const (B + M)
  exact ge_of_tendsto' hlim fun n => key n z

/-- Theorem 2.3, first part. -/
theorem theorem_2_3_conj (hN : 0 < N) :
    ConjSelfSimilar Φ.realMaps ↔ ∃ Λ, Φ.IsDualAttractor Λ ∧ ∃ h, Λ = {h} := by
  rw [Φ.conjSelfSimilar_iff]
  constructor
  · intro hall
    refine ⟨_, Φ.isDualAttractor_range hN,
      toNbhd ε (Φ.dualProj (.inf fun _ => ⟨0, hN⟩)), ?_⟩
    ext u
    simp only [mem_range, mem_singleton_iff]
    constructor
    · rintro ⟨w, rfl⟩
      exact dualConj_toNbhd_congr (eqOn_nbhd_of_eqOn_Icc Φ.ε_pos
        (Φ.differentiableOn_dualProj _) (Φ.differentiableOn_dualProj _) zero_lt_one subset_rfl
        (hall _ _))
    · rintro rfl
      exact ⟨_, rfl⟩
  · rintro ⟨Λ, hΛ, h, rfl⟩ i j x hx
    have hu := (Φ.existsUnique_isDualAttractor hN).unique hΛ (Φ.isDualAttractor_range hN)
    have hmem : ∀ w : ℕ → Fin N, toNbhd ε (Φ.dualProj (.inf w)) = h := fun w => by
      have : toNbhd ε (Φ.dualProj (.inf w)) ∈ ({h} : Set (nbhd ε →ᵤ ℂ)) := hu ▸ ⟨w, rfl⟩
      exact this
    exact congrArg (fun u => UniformFun.toFun u ⟨(x : ℂ), ofReal_mem_nbhd Φ.ε_pos hx⟩)
      ((hmem i).trans (hmem j).symm)

/-- Theorem 2.3, second part. -/
theorem theorem_2_3_subconj (hN : 0 < N) :
    Φ.SubConjSelfSimilar ↔
      ∃ (m : ℕ) (i j : Fin m → Fin N), i ≠ j ∧ ∃ h ∈ analyticSpace ε,
        Φ.dualCompOn (List.ofFn i) h = h ∧ Φ.dualCompOn (List.ofFn j) h = h := by
  -- `0 < N` is not needed: distinct words force `0 < m`, hence `0 < N`
  have _ := hN
  rw [Φ.subConjSelfSimilar_iff]
  constructor
  · rintro ⟨m, hm, i, j, hij, heq⟩
    have hij' : toNbhd ε (Φ.dualProj (.inf (periodic hm i))) =
        toNbhd ε (Φ.dualProj (.inf (periodic hm j))) :=
      dualConj_toNbhd_congr (eqOn_nbhd_of_eqOn_Icc Φ.ε_pos (Φ.differentiableOn_dualProj _)
        (Φ.differentiableOn_dualProj _) zero_lt_one subset_rfl heq)
    refine ⟨m, i, j, hij, _, Φ.dualProj_mem_analyticSpace _, Φ.dualCompOn_periodic hm i, ?_⟩
    rw [hij']
    exact Φ.dualCompOn_periodic hm j
  · rintro ⟨m, i, j, hij, h, hh, hi, hj⟩
    have hm : 0 < m := Nat.pos_of_ne_zero fun hm0 => by
      subst hm0
      exact hij (Subsingleton.elim _ _)
    have hne : ∀ k : Fin m → Fin N, List.ofFn k ≠ [] := fun k => by
      rw [Ne, List.ofFn_eq_nil_iff]
      exact hm.ne'
    have e1 := Φ.eq_toNbhd_dualProj_of_dualCompOn_eq (hne i) hh hi (Φ.dualCompOn_periodic hm i)
    have e2 := Φ.eq_toNbhd_dualProj_of_dualCompOn_eq (hne j) hh hj (Φ.dualCompOn_periodic hm j)
    refine ⟨m, hm, i, j, hij, fun x hx => ?_⟩
    exact congrArg (fun u => UniformFun.toFun u ⟨(x : ℂ), ofReal_mem_nbhd Φ.ε_pos hx⟩)
      (e1.symm.trans e2)

end IFS

end AnalyticESC
