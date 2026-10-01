module

public import AnalyticESC.Dual.Projection
public import AnalyticESC.Analysis

@[expose] public section

/-!
# The dual IFS and its attractor

Iterates of the dual operators, Lemma 2.1 (the attractor of the dual IFS), Lemma 2.4 (c)
(`Λ* = {H_i : i ∈ Σ}`), the strong separation of the dual in terms of the dual natural
projection (Lemma 2.5, (a) ⇔ (c)), and the incompatibility of dual strong separation with an
exact coincidence `f_a = f_b`.
-/

namespace AnalyticESC

open Set Metric Filter Topology
open scoped UniformConvergence

/-! ## Restrictions to `B_ε` -/

/-- Restrictions agree as soon as the maps agree on `B_ε`. -/
private theorem toNbhd_congr {ε : ℝ} {g h : ℂ → ℂ} (hgh : ∀ z ∈ nbhd ε, g z = h z) :
    toNbhd ε g = toNbhd ε h := by
  unfold toNbhd
  congr 1
  funext z
  exact hgh z z.2

/-- An extension of a function on `B_ε` to `ℂ`, by zero outside `B_ε`. -/
private noncomputable def extendNbhd {ε : ℝ} (u : nbhd ε →ᵤ ℂ) : ℂ → ℂ :=
  open Classical in fun z => if hz : z ∈ nbhd ε then UniformFun.toFun u ⟨z, hz⟩ else 0

private theorem toNbhd_extendNbhd {ε : ℝ} (u : nbhd ε →ᵤ ℂ) : toNbhd ε (extendNbhd u) = u := by
  apply UniformFun.toFun.injective
  funext z
  simp [toNbhd, extendNbhd]

/-- Convergence of functions on `B_ε` in the topology of uniform convergence, from pointwise
bounds that are uniform on `B_ε` and tend to zero. -/
private theorem tendsto_uniformFun_of_norm_le {ε : ℝ} {ι : Type*} {l : Filter ι}
    {F : ι → nbhd ε →ᵤ ℂ} {f : nbhd ε →ᵤ ℂ} {b : ι → ℝ} (hb : Tendsto b l (𝓝 0))
    (h : ∀ n z, ‖UniformFun.toFun (F n) z - UniformFun.toFun f z‖ ≤ b n) :
    Tendsto F l (𝓝 f) := by
  rw [UniformFun.tendsto_iff_tendstoUniformly, Metric.tendstoUniformly_iff]
  intro δ hδ
  filter_upwards [hb.eventually (gt_mem_nhds hδ)] with n hn z
  rw [dist_comm, dist_eq_norm]
  exact (h n z).trans_lt hn

/-- Words agreeing with `w` on the first `m` letters form a neighbourhood of `w`. -/
private theorem eventually_forall_lt_eq {N : ℕ} (w : ℕ → Fin N) (m : ℕ) :
    ∀ᶠ v in 𝓝 w, ∀ k < m, v k = w k := by
  have : ∀ k, ∀ᶠ v in 𝓝 w, v k = w k := fun k => by
    have h := (continuous_apply k).continuousAt (x := w)
    rw [ContinuousAt, nhds_discrete (Fin N)] at h
    exact tendsto_pure.1 h
  simpa only [← Finset.mem_range, Filter.eventually_all_finset] using fun k _ => this k

/-- Infinite words agreeing on the first `m` letters share a prefix of length `m`. -/
private theorem le_commonPrefixLength_of_forall_lt_eq {N : ℕ} {v w : ℕ → Fin N} {m : ℕ}
    (h : ∀ k < m, v k = w k) : (m : ℕ∞) ≤ (Word.inf v).commonPrefixLength (.inf w) := by
  rw [Word.le_commonPrefixLength_iff]
  intro k hk
  simp [h k hk]

/-- `c_max^n K → 0`. -/
private theorem tendsto_pow_mul_nhds_zero {c K : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    Tendsto (fun n : ℕ => c ^ n * K) atTop (𝓝 0) := by
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const K

namespace Word

variable {N : ℕ}

private theorem prepend_inf (a : List (Fin N)) (w : ℕ → Fin N) :
    (inf w).prepend a = inf fun n => if h : n < a.length then a[n] else w (n - a.length) := rfl

private theorem prepend_nil_eq (w : Word N) : w.prepend [] = w := by
  cases w with
  | fin w => rfl
  | inf w => simp [prepend]

/-- An infinite word is its prefix of length `n` followed by its `n`-fold shift. -/
private theorem inf_eq_prepend_ofFn (w : ℕ → Fin N) (n : ℕ) :
    inf w = (inf fun k => w (k + n)).prepend (List.ofFn fun k : Fin n => w k) := by
  rw [prepend_inf]
  congr 1
  funext k
  simp only [List.length_ofFn]
  split_ifs with hk
  · simp
  · congr 1
    omega

private theorem inf_eq_prepend_singleton (w : ℕ → Fin N) :
    inf w = (inf fun k => w (k + 1)).prepend [w 0] := by
  rw [inf_eq_prepend_ofFn w 1]
  simp

private theorem exists_prepend_singleton_inf (i : Fin N) (w : ℕ → Fin N) :
    ∃ v : ℕ → Fin N, (inf w).prepend [i] = inf v ∧ v 0 = i :=
  ⟨_, prepend_inf [i] w, by simp⟩

end Word

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-! ## Iterates of the dual operators on `ℂ → ℂ` -/

private theorem comp_singleton_eq_f (i : Fin N) : Φ.comp [i] = Φ.f i := by
  simp

/-- `H_i = f_i''/f_i'` for a single letter `i`. -/
private theorem dualProj_fin_singleton_eq_nonlin (i : Fin N) (z : ℂ) :
    Φ.dualProj (.fin [i]) z = Φ.nonlin i z := by
  rw [dualProj, tsum_eq_single 0]
  · simp [dualTerm]
  · intro n hn
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp [dualTerm]

/-- The cocycle identity for a single letter. -/
private theorem dualProj_prepend_singleton (i : Fin N) (w : Word N) {z : ℂ}
    (hz : z ∈ closure (nbhd ε)) :
    Φ.dualProj (w.prepend [i]) z = deriv (Φ.f i) z * Φ.dualProj w (Φ.f i z) + Φ.nonlin i z := by
  rw [Φ.dualProj_prepend [i] w hz, List.reverse_singleton, comp_singleton_eq_f,
    Φ.dualProj_fin_singleton_eq_nonlin i z, add_comm]

/-- `F_w h = f_{w^←}' · (h ∘ f_{w^←}) + H_w` on `B_ε` (Section 2.1). -/
theorem dualComp_apply (w : List (Fin N)) (h : ℂ → ℂ) {z : ℂ} (hz : z ∈ nbhd ε) :
    Φ.dualComp w h z =
      deriv (Φ.comp w.reverse) z * h (Φ.comp w.reverse z) + Φ.dualProj (.fin w) z := by
  induction w generalizing z with
  | nil => simp [dualComp]
  | cons i w ih =>
    have hcl : z ∈ closure (nbhd ε) := subset_closure hz
    have h1 : Φ.dualComp (i :: w) h z = Φ.dualOp i (Φ.dualComp w h) z := rfl
    have h2 : (Word.fin w).prepend [i] = .fin (i :: w) := rfl
    rw [h1, dualOp, ih (Φ.mapsTo_f i hz), List.reverse_cons, Φ.deriv_comp_append _ _ hcl,
      Φ.comp_append, comp_singleton_eq_f, ← h2,
      Φ.dualProj_prepend_singleton i _ hcl, Function.comp_apply]
    ring

theorem dualComp_zero (w : List (Fin N)) {z : ℂ} (hz : z ∈ nbhd ε) :
    Φ.dualComp w 0 z = Φ.dualProj (.fin w) z := by
  rw [Φ.dualComp_apply w 0 hz]
  simp

/-! ## Iterates of the dual operators on functions on `B_ε` -/

/-- `F_w = F_{w₁} ∘ ⋯ ∘ F_{w_k}` acting on functions on `B_ε`. -/
private noncomputable def dualCompU (w : List (Fin N)) : (nbhd ε →ᵤ ℂ) → nbhd ε →ᵤ ℂ :=
  w.foldr (fun i G => Φ.dualOpU i ∘ G) id

@[simp] private theorem dualCompU_nil (u : nbhd ε →ᵤ ℂ) : Φ.dualCompU [] u = u := rfl

@[simp] private theorem dualCompU_cons (i : Fin N) (w : List (Fin N)) (u : nbhd ε →ᵤ ℂ) :
    Φ.dualCompU (i :: w) u = Φ.dualOpU i (Φ.dualCompU w u) := rfl

private theorem dualCompU_append (v w : List (Fin N)) (u : nbhd ε →ᵤ ℂ) :
    Φ.dualCompU (v ++ w) u = Φ.dualCompU v (Φ.dualCompU w u) := by
  induction v with
  | nil => rfl
  | cons i v ih => simp [ih]

private theorem dualOpU_toNbhd (i : Fin N) (h : ℂ → ℂ) :
    Φ.dualOpU i (toNbhd ε h) = toNbhd ε (Φ.dualOp i h) := rfl

private theorem dualCompU_toNbhd (w : List (Fin N)) (h : ℂ → ℂ) :
    Φ.dualCompU w (toNbhd ε h) = toNbhd ε (Φ.dualComp w h) := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [dualCompU_cons, ih, dualOpU_toNbhd]; rfl

private theorem toFun_dualOpU (i : Fin N) (u : nbhd ε →ᵤ ℂ) (z : nbhd ε) :
    UniformFun.toFun (Φ.dualOpU i u) z =
      deriv (Φ.f i) z * UniformFun.toFun u ⟨Φ.f i z, Φ.mapsTo_f i z.2⟩ + Φ.nonlin i z := rfl

/-- `F_i` contracts the supremum distance by `c_max`. -/
private theorem norm_dualOpU_sub_le (i : Fin N) {u v : nbhd ε →ᵤ ℂ} {C : ℝ}
    (h : ∀ z, ‖UniformFun.toFun u z - UniformFun.toFun v z‖ ≤ C) (z : nbhd ε) :
    ‖UniformFun.toFun (Φ.dualOpU i u) z - UniformFun.toFun (Φ.dualOpU i v) z‖ ≤ Φ.cmax * C := by
  rw [toFun_dualOpU, toFun_dualOpU, add_sub_add_right_eq_sub, ← mul_sub, norm_mul]
  exact mul_le_mul (Φ.norm_deriv_le_cmax i (subset_closure z.2)) (h _) (norm_nonneg _)
    Φ.cmax_nonneg

/-- `F_w` contracts the supremum distance by `c_max^{|w|}`. -/
private theorem norm_dualCompU_sub_le (w : List (Fin N)) {u v : nbhd ε →ᵤ ℂ} {C : ℝ}
    (h : ∀ z, ‖UniformFun.toFun u z - UniformFun.toFun v z‖ ≤ C) (z : nbhd ε) :
    ‖UniformFun.toFun (Φ.dualCompU w u) z - UniformFun.toFun (Φ.dualCompU w v) z‖ ≤
      Φ.cmax ^ w.length * C := by
  induction w generalizing z with
  | nil => simpa using h z
  | cons i w ih =>
    rw [dualCompU_cons, dualCompU_cons, List.length_cons, pow_succ', mul_assoc]
    exact Φ.norm_dualOpU_sub_le i ih z

theorem dualOpU_toNbhd_dualProj (i : Fin N) (w : Word N) :
    Φ.dualOpU i (toNbhd ε (Φ.dualProj w)) = toNbhd ε (Φ.dualProj (w.prepend [i])) := by
  rw [dualOpU_toNbhd]
  refine toNbhd_congr fun z hz => ?_
  rw [Φ.dualProj_prepend_singleton i w (subset_closure hz)]
  rfl

private theorem dualCompU_toNbhd_dualProj (a : List (Fin N)) (w : Word N) :
    Φ.dualCompU a (toNbhd ε (Φ.dualProj w)) = toNbhd ε (Φ.dualProj (w.prepend a)) := by
  induction a with
  | nil => rw [dualCompU_nil, Word.prepend_nil_eq]
  | cons i a ih =>
    rw [dualCompU_cons, ih, dualOpU_toNbhd_dualProj, ← Word.prepend_append]
    rfl

/-- `H_w = F_{w|n} H_{σ^n w}` as functions on `B_ε`. -/
private theorem toNbhd_dualProj_inf_eq (w : ℕ → Fin N) (n : ℕ) :
    toNbhd ε (Φ.dualProj (.inf w)) =
      Φ.dualCompU (List.ofFn fun k : Fin n => w k)
        (toNbhd ε (Φ.dualProj (.inf fun k => w (k + n)))) := by
  rw [dualCompU_toNbhd_dualProj, ← Word.inf_eq_prepend_ofFn]

/-! ## The attractor `{H_i : i ∈ Σ}` -/

/-- The coding map `w ↦ H_w` is continuous from `Σ` to the functions on `B_ε`. -/
private theorem continuous_toNbhd_dualProj :
    Continuous fun w : ℕ → Fin N => toNbhd ε (Φ.dualProj (.inf w)) := by
  obtain ⟨M, -, -, hMd⟩ := Φ.exists_dualProj_bounds
  rw [continuous_iff_continuousAt]
  intro w
  rw [ContinuousAt, UniformFun.tendsto_iff_tendstoUniformly, Metric.tendstoUniformly_iff]
  intro δ hδ
  obtain ⟨m, hm⟩ := ((tendsto_pow_mul_nhds_zero Φ.cmax_nonneg Φ.cmax_lt_one
    (K := 2 * M)).eventually (gt_mem_nhds hδ)).exists
  filter_upwards [eventually_forall_lt_eq w m] with v hv z
  have h := hMd (.inf w) (.inf v) m (le_commonPrefixLength_of_forall_lt_eq fun k hk =>
    (hv k hk).symm) z (subset_closure z.2)
  rw [dist_eq_norm]
  calc _ ≤ _ := h
    _ = Φ.cmax ^ m * (2 * M) := by ring
    _ < δ := hm

/-- Lemma 2.4, last claim: `{H_i : i ∈ Σ}` is an attractor of the dual IFS. -/
theorem isDualAttractor_range (hN : 0 < N) :
    Φ.IsDualAttractor (range fun w : ℕ → Fin N => toNbhd ε (Φ.dualProj (.inf w))) := by
  refine ⟨?_, ⟨_, ⟨fun _ => ⟨0, hN⟩, rfl⟩⟩, isCompact_range Φ.continuous_toNbhd_dualProj, ?_⟩
  · rintro _ ⟨w, rfl⟩
    exact Φ.dualProj_mem_analyticSpace w
  · ext u
    simp only [mem_iUnion, mem_image, mem_range]
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨w 0, _, ⟨fun k => w (k + 1), rfl⟩, ?_⟩
      rw [dualOpU_toNbhd_dualProj]
      conv_rhs => rw [Word.inf_eq_prepend_singleton w]
    · rintro ⟨i, _, ⟨w, rfl⟩, rfl⟩
      obtain ⟨v, hv, -⟩ := Word.exists_prepend_singleton_inf i w
      exact ⟨v, by rw [dualOpU_toNbhd_dualProj, hv]⟩

/-! ## Uniqueness of the attractor -/

private theorem dualOpU_mem_of_isDualAttractor {Λ : Set (nbhd ε →ᵤ ℂ)} (hΛ : Φ.IsDualAttractor Λ)
    (i : Fin N) {u : nbhd ε →ᵤ ℂ} (hu : u ∈ Λ) : Φ.dualOpU i u ∈ Λ := by
  rw [hΛ.2.2.2]
  exact mem_iUnion.2 ⟨i, mem_image_of_mem _ hu⟩

private theorem dualCompU_mem_of_isDualAttractor {Λ : Set (nbhd ε →ᵤ ℂ)} (hΛ : Φ.IsDualAttractor Λ)
    (w : List (Fin N)) {u : nbhd ε →ᵤ ℂ} (hu : u ∈ Λ) : Φ.dualCompU w u ∈ Λ := by
  induction w with
  | nil => exact hu
  | cons i w ih => exact Φ.dualOpU_mem_of_isDualAttractor hΛ i ih

/-- Every element of an attractor is bounded on `B_ε`: it is `F_i h` with `h` holomorphic on
`B_ε`, and `f_i` maps the compact set `cl B_ε` into `B_ε`. -/
private theorem exists_bound_of_mem_isDualAttractor {Λ : Set (nbhd ε →ᵤ ℂ)}
    (hΛ : Φ.IsDualAttractor Λ) {u : nbhd ε →ᵤ ℂ} (hu : u ∈ Λ) :
    ∃ C, ∀ z, ‖UniformFun.toFun u z‖ ≤ C := by
  rw [hΛ.2.2.2] at hu
  obtain ⟨i, u', hu', rfl⟩ := mem_iUnion.1 hu
  obtain ⟨g, hg, -, rfl⟩ := hΛ.1 hu'
  obtain ⟨Mn, -, hMn⟩ := Φ.exists_nonlin_bound
  have hK : IsCompact (Φ.f i '' closure (nbhd ε)) :=
    (isCompact_closure_nbhd ε).image_of_continuousOn
      ((Φ.differentiableOn_f i).continuousOn.mono closure_nbhd_subset_two)
  have hKs : Φ.f i '' closure (nbhd ε) ⊆ nbhd ε := (Φ.inClass i).mapsTo.image_subset
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hg.continuousOn.mono hKs)
  refine ⟨Φ.cmax * C + Mn, fun z => ?_⟩
  have hz : (z : ℂ) ∈ closure (nbhd ε) := subset_closure z.2
  rw [toFun_dualOpU]
  refine (norm_add_le _ _).trans (add_le_add ?_ (hMn i z hz))
  rw [norm_mul]
  exact mul_le_mul (Φ.norm_deriv_le_cmax i hz) (hC _ (mem_image_of_mem _ hz)) (norm_nonneg _)
    Φ.cmax_nonneg

/-- An attractor is uniformly bounded on `B_ε`, being totally bounded. -/
private theorem exists_bound_isDualAttractor {Λ : Set (nbhd ε →ᵤ ℂ)} (hΛ : Φ.IsDualAttractor Λ) :
    ∃ B, ∀ u ∈ Λ, ∀ z, ‖UniformFun.toFun u z‖ ≤ B := by
  have hb : ∀ u, ∃ C, u ∈ Λ → ∀ z, ‖UniformFun.toFun u z‖ ≤ C := fun u => by
    by_cases hu : u ∈ Λ
    · obtain ⟨C, hC⟩ := Φ.exists_bound_of_mem_isDualAttractor hΛ hu
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h hu⟩
  choose C hC using hb
  have hd : UniformFun.gen (nbhd ε) ℂ {p | dist p.1 p.2 < 1} ∈ uniformity (nbhd ε →ᵤ ℂ) :=
    (UniformFun.hasBasis_uniformity _ _).mem_of_mem (Metric.dist_mem_uniformity one_pos)
  obtain ⟨t, htΛ, ht, hcover⟩ := totallyBounded_iff_subset.1 hΛ.2.2.1.totallyBounded _ hd
  obtain ⟨B, hB⟩ := (ht.image C).bddAbove
  refine ⟨B + 1, fun u hu z => ?_⟩
  obtain ⟨y, hy, hyu⟩ := mem_iUnion₂.1 (hcover hu)
  have h1 : ‖UniformFun.toFun y z‖ ≤ B := (hC y (htΛ hy) z).trans (hB (mem_image_of_mem C hy))
  have h2 : dist (UniformFun.toFun u z) (UniformFun.toFun y z) < 1 := hyu z
  rw [dist_eq_norm] at h2
  linarith [norm_le_insert' (UniformFun.toFun u z) (UniformFun.toFun y z)]

/-- Every attractor of the dual IFS is `{H_i : i ∈ Σ}`. -/
private theorem eq_range_of_isDualAttractor {Λ : Set (nbhd ε →ᵤ ℂ)} (hΛ : Φ.IsDualAttractor Λ) :
    Λ = range fun w : ℕ → Fin N => toNbhd ε (Φ.dualProj (.inf w)) := by
  obtain ⟨B, hB⟩ := Φ.exists_bound_isDualAttractor hΛ
  obtain ⟨M, -, hM, -⟩ := Φ.exists_dualProj_bounds
  -- `F_{w|n} u` is within `c_max^n (B + M)` of `H_w` for `u ∈ Λ`
  have key : ∀ (w : ℕ → Fin N) (n : ℕ) (u : nbhd ε →ᵤ ℂ), u ∈ Λ → ∀ z : nbhd ε,
      ‖UniformFun.toFun (Φ.dualCompU (List.ofFn fun k : Fin n => w k) u) z -
        UniformFun.toFun (toNbhd ε (Φ.dualProj (.inf w))) z‖ ≤ Φ.cmax ^ n * (B + M) := by
    intro w n u hu z
    rw [Φ.toNbhd_dualProj_inf_eq w n]
    have h := Φ.norm_dualCompU_sub_le (List.ofFn fun k : Fin n => w k)
      (u := u) (v := toNbhd ε (Φ.dualProj (.inf fun k => w (k + n)))) (C := B + M)
      (fun z' => (norm_sub_le _ _).trans (add_le_add (hB u hu z') (hM _ _ (subset_closure z'.2))))
      z
    rwa [List.length_ofFn] at h
  apply Subset.antisymm
  · intro u hu
    have hinv : ∀ v : Λ, ∃ p : Fin N × Λ, (v : nbhd ε →ᵤ ℂ) = Φ.dualOpU p.1 p.2 := by
      rintro ⟨v, hv⟩
      have hv' := hv
      rw [hΛ.2.2.2] at hv'
      obtain ⟨i, v', hv'Λ, hvv'⟩ := mem_iUnion.1 hv'
      exact ⟨(i, ⟨v', hv'Λ⟩), hvv'.symm⟩
    choose g hg using hinv
    let s : ℕ → Λ := fun n => (fun v => (g v).2)^[n] ⟨u, hu⟩
    let w : ℕ → Fin N := fun n => (g (s n)).1
    have hs : ∀ n, u = Φ.dualCompU (List.ofFn fun k : Fin n => w k) (s n) := by
      intro n
      induction n with
      | zero => simp [s]
      | succ n ih =>
        have h1 : s (n + 1) = (g (s n)).2 := Function.iterate_succ_apply' _ _ _
        have h2 : (List.ofFn fun k : Fin (n + 1) => w k) =
            (List.ofFn fun k : Fin n => w k) ++ [w n] := by
          rw [List.ofFn_succ', List.concat_eq_append]
          simp
        rw [h2, dualCompU_append, dualCompU_cons, dualCompU_nil, h1]
        exact ih.trans (congrArg _ (hg (s n)))
    refine ⟨w, ?_⟩
    apply UniformFun.toFun.injective
    funext z
    refine (sub_eq_zero.1 (norm_le_zero_iff.1 ?_)).symm
    refine ge_of_tendsto' (tendsto_pow_mul_nhds_zero Φ.cmax_nonneg Φ.cmax_lt_one (K := B + M))
      fun n => ?_
    have h := key w n (s n) (s n).2 z
    rwa [← hs n] at h
  · rintro _ ⟨w, rfl⟩
    obtain ⟨u, hu⟩ := hΛ.2.1
    exact hΛ.2.2.1.isClosed.mem_of_tendsto
      (tendsto_uniformFun_of_norm_le (tendsto_pow_mul_nhds_zero Φ.cmax_nonneg Φ.cmax_lt_one)
        fun n z => key w n u hu z)
      (Eventually.of_forall fun n => Φ.dualCompU_mem_of_isDualAttractor hΛ _ hu)

/-- Lemma 2.1: the dual IFS has a unique attractor. -/
theorem existsUnique_isDualAttractor (hN : 0 < N) : ∃! Λ, Φ.IsDualAttractor Λ :=
  ⟨_, Φ.isDualAttractor_range hN, fun _ hΛ => Φ.eq_range_of_isDualAttractor hΛ⟩

/-! ## Strong separation of the dual IFS -/

private theorem toNbhd_dualProj_eq_iff (i j : ℕ → Fin N) :
    toNbhd ε (Φ.dualProj (.inf i)) = toNbhd ε (Φ.dualProj (.inf j)) ↔
      ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x := by
  constructor
  · intro h x hx
    exact congrArg (fun u => UniformFun.toFun u ⟨(x : ℂ), ofReal_mem_nbhd Φ.ε_pos hx⟩) h
  · intro h
    exact toNbhd_congr (eqOn_nbhd_of_eqOn_Icc Φ.ε_pos (Φ.differentiableOn_dualProj _)
      (Φ.differentiableOn_dualProj _) zero_lt_one subset_rfl h)

/-- The dual IFS is strongly separated if and only if `H_i ≠ H_j` on `B_ε` whenever `i₁ ≠ j₁`. -/
private theorem dualSSC_iff_toNbhd_ne (hN : 0 < N) :
    Φ.DualSSC ↔ ∀ i j : ℕ → Fin N, i 0 ≠ j 0 →
      toNbhd ε (Φ.dualProj (.inf i)) ≠ toNbhd ε (Φ.dualProj (.inf j)) := by
  have hmem : ∀ w : ℕ → Fin N, toNbhd ε (Φ.dualProj (.inf w)) ∈
      Φ.dualOpU (w 0) '' range fun w : ℕ → Fin N => toNbhd ε (Φ.dualProj (.inf w)) := by
    intro w
    refine ⟨_, ⟨fun k => w (k + 1), rfl⟩, ?_⟩
    rw [dualOpU_toNbhd_dualProj]
    conv_rhs => rw [Word.inf_eq_prepend_singleton w]
  constructor
  · rintro ⟨Λ, hΛ, hdisj⟩ i j hij heq
    rw [Φ.eq_range_of_isDualAttractor hΛ] at hdisj
    refine Set.disjoint_left.1 (hdisj _ _ hij) (hmem i) ?_
    rw [heq]
    exact hmem j
  · intro h
    refine ⟨_, Φ.isDualAttractor_range hN, fun a b hab => Set.disjoint_left.2 ?_⟩
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩ ⟨_, ⟨w', rfl⟩, heq⟩
    obtain ⟨v, hv, hv0⟩ := Word.exists_prepend_singleton_inf a w
    obtain ⟨v', hv', hv'0⟩ := Word.exists_prepend_singleton_inf b w'
    rw [dualOpU_toNbhd_dualProj, dualOpU_toNbhd_dualProj, hv, hv'] at heq
    exact h v v' (by rw [hv0, hv'0]; exact hab) heq.symm

theorem dualSSC_iff_ne (hN : 0 < N) :
    Φ.DualSSC ↔ ∀ i j : ℕ → Fin N, i 0 ≠ j 0 →
      ∃ x ∈ I, Φ.dualProj (.inf i) x ≠ Φ.dualProj (.inf j) x := by
  rw [Φ.dualSSC_iff_toNbhd_ne hN]
  refine forall₂_congr fun i j => imp_congr_right fun _ => ?_
  rw [Ne, Φ.toNbhd_dualProj_eq_iff]
  push Not
  rfl

/-- Suprema of pointwise close bounded functions are close. -/
private theorem abs_ciSup_sub_ciSup_le {ι : Type*} [Nonempty ι] {f g : ι → ℝ} {c : ℝ}
    (hf : BddAbove (range f)) (hg : BddAbove (range g)) (h : ∀ x, |f x - g x| ≤ c) :
    |(⨆ x, f x) - ⨆ x, g x| ≤ c := by
  have h1 : ∀ x, f x ≤ c + ⨆ x, g x := fun x => by
    have := (abs_sub_le_iff.1 (h x)).1
    have := le_ciSup hg x
    linarith
  have h2 : ∀ x, g x ≤ c + ⨆ x, f x := fun x => by
    have := (abs_sub_le_iff.1 (h x)).2
    have := le_ciSup hf x
    linarith
  rw [abs_sub_le_iff, sub_le_iff_le_add, sub_le_iff_le_add]
  exact ⟨ciSup_le h1, ciSup_le h2⟩

/-- Lemma 2.5, (a) ⇔ (c). -/
theorem dualSSC_iff_exists_delta (hN : 0 < N) :
    Φ.DualSSC ↔ ∃ δ > 0, ∀ i j : ℕ → Fin N, i 0 ≠ j 0 →
      δ < ⨆ x : I, ‖Φ.dualProj (.inf i) ((x : ℝ) : ℂ) - Φ.dualProj (.inf j) ((x : ℝ) : ℂ)‖ := by
  obtain ⟨M, -, hM, hMd⟩ := Φ.exists_dualProj_bounds
  have : Nonempty I := ⟨⟨0, left_mem_Icc.2 zero_le_one⟩⟩
  have hx : ∀ x : I, ((x : ℝ) : ℂ) ∈ closure (nbhd ε) := fun x =>
    subset_closure (ofReal_mem_nbhd Φ.ε_pos x.2)
  let D : (ℕ → Fin N) × (ℕ → Fin N) → ℝ := fun p =>
    ⨆ x : I, ‖Φ.dualProj (.inf p.1) ((x : ℝ) : ℂ) - Φ.dualProj (.inf p.2) ((x : ℝ) : ℂ)‖
  have hbdd : ∀ p : (ℕ → Fin N) × (ℕ → Fin N), BddAbove (range fun x : I =>
      ‖Φ.dualProj (.inf p.1) ((x : ℝ) : ℂ) - Φ.dualProj (.inf p.2) ((x : ℝ) : ℂ)‖) := by
    intro p
    refine ⟨M + M, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (norm_sub_le _ _).trans (add_le_add (hM _ _ (hx x)) (hM _ _ (hx x)))
  rw [Φ.dualSSC_iff_ne hN]
  constructor
  · intro h
    let S : Set ((ℕ → Fin N) × (ℕ → Fin N)) := {p | p.1 0 ≠ p.2 0}
    have hpos : ∀ p ∈ S, 0 < D p := by
      rintro ⟨i, j⟩ hp
      obtain ⟨x, hxI, hne⟩ := h i j hp
      exact (norm_pos_iff.2 (sub_ne_zero.2 hne)).trans_le (le_ciSup (hbdd (i, j)) ⟨x, hxI⟩)
    have hcont : Continuous D := by
      rw [continuous_iff_continuousAt]
      intro p
      rw [ContinuousAt, Metric.tendsto_nhds]
      intro η hη
      obtain ⟨m, hm⟩ := ((tendsto_pow_mul_nhds_zero Φ.cmax_nonneg Φ.cmax_lt_one
        (K := 4 * M)).eventually (gt_mem_nhds hη)).exists
      have h1 := (continuous_fst.tendsto p).eventually (eventually_forall_lt_eq p.1 m)
      have h2 := (continuous_snd.tendsto p).eventually (eventually_forall_lt_eq p.2 m)
      filter_upwards [h1, h2] with q hq1 hq2
      rw [Real.dist_eq]
      refine lt_of_le_of_lt (abs_ciSup_sub_ciSup_le (hbdd q) (hbdd p) fun x => ?_) hm
      have e1 := hMd _ _ m (le_commonPrefixLength_of_forall_lt_eq hq1) _ (hx x)
      have e2 := hMd _ _ m (le_commonPrefixLength_of_forall_lt_eq hq2) _ (hx x)
      refine (abs_norm_sub_norm_le _ _).trans ?_
      have e3 := norm_sub_le
        (Φ.dualProj (.inf q.1) ((x : ℝ) : ℂ) - Φ.dualProj (.inf p.1) ((x : ℝ) : ℂ))
        (Φ.dualProj (.inf q.2) ((x : ℝ) : ℂ) - Φ.dualProj (.inf p.2) ((x : ℝ) : ℂ))
      have e4 : Φ.dualProj (.inf q.1) ((x : ℝ) : ℂ) - Φ.dualProj (.inf q.2) ((x : ℝ) : ℂ) -
          (Φ.dualProj (.inf p.1) ((x : ℝ) : ℂ) - Φ.dualProj (.inf p.2) ((x : ℝ) : ℂ)) =
          Φ.dualProj (.inf q.1) ((x : ℝ) : ℂ) - Φ.dualProj (.inf p.1) ((x : ℝ) : ℂ) -
          (Φ.dualProj (.inf q.2) ((x : ℝ) : ℂ) - Φ.dualProj (.inf p.2) ((x : ℝ) : ℂ)) := by ring
      rw [e4]
      linarith
    have hS : IsCompact S :=
      (IsClosed.preimage (f := fun p : (ℕ → Fin N) × (ℕ → Fin N) => (p.1 0, p.2 0))
        (by fun_prop) (isClosed_discrete {q : Fin N × Fin N | q.1 ≠ q.2})).isCompact
    rcases S.eq_empty_or_nonempty with hE | hne
    · refine ⟨1, one_pos, fun i j hij => ?_⟩
      have : (i, j) ∈ S := hij
      rw [hE] at this
      exact absurd this (notMem_empty _)
    · obtain ⟨p₀, hp₀, hmin⟩ := hS.exists_isMinOn hne hcont.continuousOn
      refine ⟨D p₀ / 2, half_pos (hpos p₀ hp₀), fun i j hij => ?_⟩
      calc D p₀ / 2 < D p₀ := half_lt_self (hpos p₀ hp₀)
        _ ≤ D (i, j) := isMinOn_iff.1 hmin (i, j) hij
  · rintro ⟨δ, hδ, h⟩ i j hij
    by_contra hcon
    push Not at hcon
    have h0 : ∀ x : I,
        ‖Φ.dualProj (.inf i) ((x : ℝ) : ℂ) - Φ.dualProj (.inf j) ((x : ℝ) : ℂ)‖ = 0 :=
      fun x => by rw [hcon x x.2, sub_self, norm_zero]
    have := h i j hij
    simp only [h0, ciSup_const] at this
    linarith

/-- An exact coincidence `f_a = f_b` on `I`, for words of equal length with different last
letters, contradicts the strong separation of the dual. -/
theorem not_dualSSC_of_comp_eq {a b : List (Fin N)} (hlen : a.length = b.length)
    (hlast : a.getLast? ≠ b.getLast?) (h : ∀ x ∈ I, Φ.comp a x = Φ.comp b x) : ¬ Φ.DualSSC := by
  rintro ⟨Λ, hΛ, hdisj⟩
  -- `f_a = f_b` on `B_ε`, together with the first two derivatives
  have hEq : EqOn (Φ.comp a) (Φ.comp b) (nbhd ε) :=
    eqOn_nbhd_of_eqOn_Icc Φ.ε_pos (Φ.differentiableOn_comp a) (Φ.differentiableOn_comp b)
      zero_lt_one subset_rfl h
  have hEv : ∀ z ∈ nbhd ε, Φ.comp a =ᶠ[𝓝 z] Φ.comp b := fun z hz =>
    Filter.eventuallyEq_of_mem ((isOpen_nbhd ε).mem_nhds hz) hEq
  -- hence `F_{a^←} = F_{b^←}` on functions on `B_ε`, by (2.7)
  have hF : ∀ u, Φ.dualCompU a.reverse u = Φ.dualCompU b.reverse u := by
    intro u
    rw [← toNbhd_extendNbhd u, dualCompU_toNbhd, dualCompU_toNbhd]
    refine toNbhd_congr fun z hz => ?_
    rw [Φ.dualComp_apply _ _ hz, Φ.dualComp_apply _ _ hz, List.reverse_reverse,
      List.reverse_reverse, Φ.dualProj_fin_reverse a (subset_closure hz),
      Φ.dualProj_fin_reverse b (subset_closure hz), (hEv z hz).deriv_eq,
      (hEv z hz).deriv.deriv_eq, hEq hz]
  -- the last letters of `a` and `b`
  rcases List.eq_nil_or_concat' a with rfl | ⟨a', x, rfl⟩
  · exact hlast (by rw [List.length_eq_zero_iff.1 hlen.symm])
  rcases List.eq_nil_or_concat' b with rfl | ⟨b', y, rfl⟩
  · simp at hlen
  have hxy : x ≠ y := fun hxy => hlast (by rw [List.getLast?_concat, List.getLast?_concat, hxy])
  obtain ⟨u, hu⟩ := hΛ.2.1
  have hA : Φ.dualCompU (a' ++ [x]).reverse u ∈ Φ.dualOpU x '' Λ := by
    rw [List.reverse_concat, dualCompU_cons]
    exact mem_image_of_mem _ (Φ.dualCompU_mem_of_isDualAttractor hΛ _ hu)
  have hB : Φ.dualCompU (b' ++ [y]).reverse u ∈ Φ.dualOpU y '' Λ := by
    rw [List.reverse_concat, dualCompU_cons]
    exact mem_image_of_mem _ (Φ.dualCompU_mem_of_isDualAttractor hΛ _ hu)
  rw [← hF u] at hB
  exact Set.disjoint_left.1 (hdisj x y hxy) hA hB

end IFS

end AnalyticESC
