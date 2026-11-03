module

public import AnalyticESC.Literature.SelfConformal.Distortion

@[expose] public section

/-!
# Cylinder decompositions and the cut-sets `Ψ_n`

Decompositions `μ = ∑_{u ∈ U} p_u μ ∘ φ_u⁻¹` of the self-conformal measure along partitions of
the symbolic space into cylinders, and the cut-sets `Ψ_n` of Section 2.6 of A. Rapaport,
*Dimension of self-conformal measures associated to an exponentially separated analytic IFS on
ℝ*, arXiv:2412.16753v2: `Ψ_n` is the set of words `u` with `|φ_u'(0)| ≤ 2^{-n}` all of whose
proper prefixes `v` have `|φ_v'(0)| > 2^{-n}`. We prove that `Ψ_n` is a finite minimal cut-set,
the decomposition (2.7) and the derivative bounds (2.8).

## Main declarations

* `listCylinder`, `weight`: the cylinder `[u]` and the weight `p_u` of a word given as a list.
* `map_realComp_selfConformal_compl_image`: `μ ∘ φ_u⁻¹` is carried by `φ_u(I)`.
* `selfConformal_eq_sum_of_partition`, `selfConformal_eq_sum_fin`: `μ = ∑_u p_u μ ∘ φ_u⁻¹` for a
  finite partition into cylinders, in particular for the words of a fixed length.
* `IsCutWord`, `cutSet`, `mem_cutSet`, `finite_cutWords`, `existsUnique_isCutWord`: `Ψ_n`.
* `selfConformal_eq_sum_cutSet`: (2.7), `μ = ∑_{u ∈ Ψ_n} p_u μ ∘ φ_u⁻¹`.
* `sum_weight_cutSet`: `∑_{u ∈ Ψ_n} p_u = 1`.
* `cutConst`, `abs_deriv_le_of_isCutWord`, `le_abs_deriv_of_isCutWord`: (2.8),
  `C⁻¹ 2^{-n} ≤ |φ_u'(x)| ≤ C 2^{-n}` for `u ∈ Ψ_n` and `x ∈ I`.

Copied from the library `FractalGeometry` (module `FractalGeometry.SelfConformal.CutSet`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.SelfConformal

open MeasureTheory Set Filter Topology
open AnalyticESC (I realComp RapaportHyp IsProbVec)

variable {N : ℕ} {φ : Fin N → ℝ → ℝ} {p : Fin N → ℝ}

/-! ### Cylinders and weights of words given as lists -/

/-- The cylinder `[u] = {ω : ω|_{|u|} = u}` of a finite word `u`. -/
def listCylinder (u : List (Fin N)) : Set (ℕ → Fin N) := {ω | word ω u.length = u}

/-- The cylinder of a list is the cylinder of its tuple of letters. -/
theorem listCylinder_eq_cylinder (u : List (Fin N)) : listCylinder u = cylinder u.get := by
  ext ω
  rw [mem_cylinder_iff_word, List.ofFn_get]
  rfl

/-- Cylinders of lists are measurable. -/
theorem measurableSet_listCylinder (u : List (Fin N)) : MeasurableSet (listCylinder u) := by
  rw [listCylinder_eq_cylinder]
  exact measurableSet_cylinder _

/-- `ω ∈ [ω|_k]`. -/
theorem mem_listCylinder_word (ω : ℕ → Fin N) (k : ℕ) : ω ∈ listCylinder (word ω k) := by
  show word ω (word ω k).length = word ω k
  rw [length_word]

/-- The weight `p_u = ∏_k p_{u_k}` of a finite word. -/
def weight (p : Fin N → ℝ) (u : List (Fin N)) : ℝ := (u.map p).prod

/-- The weight as a product over the letters. -/
theorem weight_eq_prod (p : Fin N → ℝ) (u : List (Fin N)) :
    weight p u = ∏ k : Fin u.length, p (u.get k) := by
  conv_lhs => rw [← List.ofFn_get u]
  rw [weight, List.map_ofFn, List.prod_ofFn]
  rfl

/-- The weight of `List.ofFn v`. -/
theorem weight_ofFn (p : Fin N → ℝ) {n : ℕ} (v : Fin n → Fin N) :
    weight p (List.ofFn v) = ∏ k, p (v k) := by
  rw [weight, List.map_ofFn, List.prod_ofFn]
  rfl

/-- Weights are nonnegative. -/
theorem weight_nonneg (hp : IsProbVec p) (u : List (Fin N)) : 0 ≤ weight p u := by
  rw [weight_eq_prod]
  exact Finset.prod_nonneg fun k _ => (hp.1 _).le

/-- `β([u] ∩ Π⁻¹ S) = p_u β((φ_u ∘ Π)⁻¹ S)` for a word `u` and measurable `S`. -/
theorem bernoulli_listCylinder_inter_coding (hφ : RapaportHyp φ) (hp : IsProbVec p)
    (u : List (Fin N)) {S : Set ℝ} (hS : MeasurableSet S) :
    bernoulli p hp (listCylinder u ∩ coding φ ⁻¹' S) =
      ENNReal.ofReal (weight p u) *
        bernoulli p hp ((fun ω => realComp φ u (coding φ ω)) ⁻¹' S) := by
  have h := bernoulli_cylinder_inter_coding hφ hp u.get hS
  rw [List.ofFn_get] at h
  rw [listCylinder_eq_cylinder, h, weight_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun k _ => (hp.1 _).le)]

/-- `β[u] = p_u`. -/
theorem bernoulli_listCylinder (hp : IsProbVec p) (u : List (Fin N)) :
    bernoulli p hp (listCylinder u) = ENNReal.ofReal (weight p u) := by
  rw [listCylinder_eq_cylinder, bernoulli_cylinder, weight_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun k _ => (hp.1 _).le)]

/-- `μ ∘ φ_u⁻¹` is carried by the image `φ_u(I)`. -/
theorem map_realComp_selfConformal_compl_image (hφ : RapaportHyp φ) (hp : IsProbVec p)
    (u : List (Fin N)) :
    (selfConformal φ p hp).map (realComp φ u) (realComp φ u '' I)ᶜ = 0 := by
  have hmeas : MeasurableSet (realComp φ u '' I)ᶜ :=
    (isCompact_I.image_of_continuousOn (continuousOn_realComp hφ u)).isClosed.measurableSet.compl
  rw [Measure.map_apply_of_aemeasurable
    (aemeasurable_realComp hφ u (selfConformal_compl_I hφ hp)) hmeas]
  refine measure_mono_null (fun x hx hxI => hx ⟨x, hxI, rfl⟩) (selfConformal_compl_I hφ hp)

/-! ### Decompositions of `μ` along partitions into cylinders -/

/-- `μ = ∑_{u ∈ U} p_u μ ∘ φ_u⁻¹` for a finite set `U` of words whose cylinders partition the
symbolic space. -/
theorem selfConformal_eq_sum_of_partition (hφ : RapaportHyp φ) (hp : IsProbVec p)
    (U : Finset (List (Fin N))) (hcover : ∀ ω, ∃ u ∈ U, ω ∈ listCylinder u)
    (hdisj : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → Disjoint (listCylinder u) (listCylinder v)) :
    selfConformal φ p hp =
      ∑ u ∈ U, ENNReal.ofReal (weight p u) • (selfConformal φ p hp).map (realComp φ u) := by
  ext S hS
  have hunion : coding φ ⁻¹' S = ⋃ u ∈ U, listCylinder u ∩ coding φ ⁻¹' S := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, exists_prop]
    constructor
    · intro h
      obtain ⟨u, hu, hω⟩ := hcover ω
      exact ⟨u, hu, hω, h⟩
    · rintro ⟨u, _, _, h⟩
      exact h
  rw [selfConformal_apply φ hp hS, hunion, measure_biUnion_finset
    (fun u hu v hv huv => ((hdisj u hu v hv huv).inter_right _).inter_left _)
    (fun u _ => (measurableSet_listCylinder u).inter (measurable_coding φ hS))]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_smul, Pi.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [bernoulli_listCylinder_inter_coding hφ hp u hS, map_realComp_selfConformal hφ hp u,
    Measure.map_apply (continuous_realComp_coding hφ u).measurable hS]

/-- `μ = ∑_{|u| = n} p_u μ ∘ φ_u⁻¹`. -/
theorem selfConformal_eq_sum_fin (hφ : RapaportHyp φ) (hp : IsProbVec p) (n : ℕ) :
    selfConformal φ p hp = ∑ v : Fin n → Fin N,
      ENNReal.ofReal (∏ k, p (v k)) • (selfConformal φ p hp).map (realComp φ (List.ofFn v)) := by
  classical
  have h := selfConformal_eq_sum_of_partition hφ hp (Finset.univ.image List.ofFn)
    (fun ω => ⟨word ω n, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, by
      simpa using mem_listCylinder_word ω n⟩)
    (by
      rintro _ hu _ hv huv
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hv
      rw [listCylinder_eq_cylinder, listCylinder_eq_cylinder]
      have hne : u ≠ v := fun h => huv (h ▸ rfl)
      refine Set.disjoint_left.2 fun ω h1 h2 => hne ?_
      rw [← listCylinder_eq_cylinder, listCylinder, mem_ofPred_eq, List.length_ofFn] at h1 h2
      exact List.ofFn_injective (h1.symm.trans h2))
  rw [Finset.sum_image (fun u _ v _ huv => List.ofFn_injective huv)] at h
  simpa only [weight_ofFn] using h

/-! ### The cut-sets `Ψ_n` -/

/-- `u ∈ Ψ_n`: `|φ_u'(0)| ≤ 2^{-n}` and `|φ_v'(0)| > 2^{-n}` for every proper prefix `v` of `u`. -/
def IsCutWord (φ : Fin N → ℝ → ℝ) (n : ℕ) (u : List (Fin N)) : Prop :=
  |deriv (realComp φ u) 0| ≤ (2 : ℝ)⁻¹ ^ n ∧
    ∀ s < u.length, (2 : ℝ)⁻¹ ^ n < |deriv (realComp φ (u.take s)) 0|

/-- The set `Ψ_n` of cut words. -/
def cutWords (φ : Fin N → ℝ → ℝ) (n : ℕ) : Set (List (Fin N)) := {u | IsCutWord φ n u}

/-- Some prefix of `ω` has `|φ_{ω|_k}'(0)| ≤ 2^{-n}`. -/
theorem exists_abs_deriv_word_le (hφ : RapaportHyp φ) (ω : ℕ → Fin N) (n : ℕ) :
    ∃ k, |deriv (realComp φ (word ω k)) 0| ≤ (2 : ℝ)⁻¹ ^ n := by
  obtain ⟨k, hk⟩ := ((tendsto_cmax_pow hφ).eventually
    (gt_mem_nhds (pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) n))).exists
  refine ⟨k, (abs_deriv_realComp_le_cmax_pow hφ _ zero_mem_I).trans ?_⟩
  rw [length_word]
  exact hk.le

/-- Prefixes of `ω|_k`. -/
theorem take_word (ω : ℕ → Fin N) {s k : ℕ} (hs : s ≤ k) : (word ω k).take s = word ω s := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [word_add]
  exact List.take_left' (length_word ω s)

/-- **`Ψ_n` is a minimal cut-set**: every `ω` has exactly one prefix in `Ψ_n`. -/
theorem existsUnique_isCutWord (hφ : RapaportHyp φ) (n : ℕ) (ω : ℕ → Fin N) :
    ∃! k, IsCutWord φ n (word ω k) := by
  classical
  have h := exists_abs_deriv_word_le hφ ω n
  refine ⟨Nat.find h, ⟨Nat.find_spec h, fun s hs => ?_⟩, fun k hk => ?_⟩
  · rw [length_word] at hs
    rw [take_word ω hs.le]
    exact lt_of_not_ge (Nat.find_min h hs)
  · rcases lt_trichotomy k (Nat.find h) with hlt | heq | hgt
    · exact absurd hk.1 (Nat.find_min h hlt)
    · exact heq
    · have := hk.2 (Nat.find h) (by rw [length_word]; exact hgt)
      rw [take_word ω hgt.le] at this
      exact absurd (Nat.find_spec h) (not_le.2 this)

/-- The words of `Ψ_n` have bounded length, so `Ψ_n` is finite. -/
theorem finite_cutWords (hφ : RapaportHyp φ) (n : ℕ) : (cutWords φ n).Finite := by
  obtain ⟨L, hL⟩ := ((tendsto_cmax_pow hφ).eventually
    (gt_mem_nhds (pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) n))).exists
  refine (List.finite_length_le (α := Fin N) (n := L)).subset fun u hu => ?_
  by_contra hlen
  have hlt : L < u.length := lt_of_not_ge hlen
  have h1 := hu.2 L hlt
  have h2 := abs_deriv_realComp_le_cmax_pow hφ (u.take L) zero_mem_I
  rw [List.length_take, min_eq_left hlt.le] at h2
  linarith

/-- The cut-set `Ψ_n` as a finite set. -/
noncomputable def cutSet (φ : Fin N → ℝ → ℝ) (n : ℕ) : Finset (List (Fin N)) :=
  open Classical in if h : (cutWords φ n).Finite then h.toFinset else ∅

/-- `u ∈ Ψ_n`. -/
theorem mem_cutSet (hφ : RapaportHyp φ) {n : ℕ} {u : List (Fin N)} :
    u ∈ cutSet φ n ↔ IsCutWord φ n u := by
  rw [cutSet, dite_eq_left_of_eq_true (eq_true (finite_cutWords hφ n)), Set.Finite.mem_toFinset]
  rfl

/-- The cylinders of `Ψ_n` cover the symbolic space. -/
theorem exists_mem_cutSet (hφ : RapaportHyp φ) (n : ℕ) (ω : ℕ → Fin N) :
    ∃ u ∈ cutSet φ n, ω ∈ listCylinder u := by
  obtain ⟨k, hk, -⟩ := existsUnique_isCutWord hφ n ω
  exact ⟨word ω k, (mem_cutSet hφ).2 hk, mem_listCylinder_word ω k⟩

/-- Distinct words of `Ψ_n` have disjoint cylinders. -/
theorem disjoint_listCylinder_cutSet (hφ : RapaportHyp φ) {n : ℕ} {u v : List (Fin N)}
    (hu : u ∈ cutSet φ n) (hv : v ∈ cutSet φ n) (huv : u ≠ v) :
    Disjoint (listCylinder u) (listCylinder v) := by
  refine Set.disjoint_left.2 fun ω h1 h2 => huv ?_
  have h1' : word ω u.length = u := h1
  have h2' : word ω v.length = v := h2
  obtain ⟨k, -, hk⟩ := existsUnique_isCutWord hφ n ω
  have hu' := hk u.length (by beta_reduce; rw [h1']; exact (mem_cutSet hφ).1 hu)
  have hv' := hk v.length (by beta_reduce; rw [h2']; exact (mem_cutSet hφ).1 hv)
  rw [← h1', ← h2', hu', hv']

/-- **(2.7)**: `μ = ∑_{u ∈ Ψ_n} p_u μ ∘ φ_u⁻¹`. -/
theorem selfConformal_eq_sum_cutSet (hφ : RapaportHyp φ) (hp : IsProbVec p) (n : ℕ) :
    selfConformal φ p hp = ∑ u ∈ cutSet φ n,
      ENNReal.ofReal (weight p u) • (selfConformal φ p hp).map (realComp φ u) :=
  selfConformal_eq_sum_of_partition hφ hp _ (exists_mem_cutSet hφ n)
    fun _ hu _ hv huv => disjoint_listCylinder_cutSet hφ hu hv huv

/-- `∑_{u ∈ Ψ_n} p_u = 1`. -/
theorem sum_weight_cutSet (hφ : RapaportHyp φ) (hp : IsProbVec p) (n : ℕ) :
    ∑ u ∈ cutSet φ n, weight p u = 1 := by
  have hunion : (univ : Set (ℕ → Fin N)) = ⋃ u ∈ cutSet φ n, listCylinder u := by
    ext ω
    simp only [mem_univ, mem_iUnion, exists_prop, true_iff]
    exact exists_mem_cutSet hφ n ω
  have h := congrArg (bernoulli p hp) hunion
  rw [measure_univ, measure_biUnion_finset
    (fun u hu v hv huv => disjoint_listCylinder_cutSet hφ hu hv huv)
    (fun u _ => measurableSet_listCylinder u)] at h
  simp_rw [bernoulli_listCylinder hp] at h
  rw [← ENNReal.ofReal_sum_of_nonneg (fun u _ => weight_nonneg hp u)] at h
  have := congrArg ENNReal.toReal h
  rwa [ENNReal.toReal_one, ENNReal.toReal_ofReal
    (Finset.sum_nonneg fun u _ => weight_nonneg hp u), eq_comm] at this

/-- The constant `C = (distConst φ)^2 / c_min` of (2.8). -/
noncomputable def cutConst (φ : Fin N → ℝ → ℝ) : ℝ := distConst φ ^ 2 / cmin φ

/-- `distConst φ ≤ cutConst φ`. -/
theorem distConst_le_cutConst (hφ : RapaportHyp φ) (hN : 0 < N) : distConst φ ≤ cutConst φ := by
  have hc := cmin_pos hφ hN
  have hc1 : cmin φ < 1 := (cmin_le_cmax hφ).trans_lt (cmax_lt_one hφ)
  have hD := one_lt_distConst hφ
  rw [cutConst, le_div_iff₀ hc, sq]
  nlinarith

/-- `1 < cutConst φ`. -/
theorem one_lt_cutConst (hφ : RapaportHyp φ) (hN : 0 < N) : 1 < cutConst φ :=
  (one_lt_distConst hφ).trans_le (distConst_le_cutConst hφ hN)

/-- **(2.8)**, upper bound: `|φ_u'(x)| ≤ C 2^{-n}` for `u ∈ Ψ_n` and `x ∈ I`. -/
theorem abs_deriv_le_of_isCutWord (hφ : RapaportHyp φ) (hN : 0 < N) {n : ℕ}
    {u : List (Fin N)} (hu : IsCutWord φ n u) {x : ℝ} (hx : x ∈ I) :
    |deriv (realComp φ u) x| ≤ cutConst φ * (2 : ℝ)⁻¹ ^ n :=
  (abs_deriv_realComp_le hφ u hx zero_mem_I).trans
    (mul_le_mul (distConst_le_cutConst hφ hN) hu.1 (abs_nonneg _)
      ((zero_lt_one.trans (one_lt_cutConst hφ hN)).le))

/-- **(2.8)**, lower bound: `C⁻¹ 2^{-n} ≤ |φ_u'(x)|` for `u ∈ Ψ_n` and `x ∈ I`. -/
theorem le_abs_deriv_of_isCutWord (hφ : RapaportHyp φ) (hN : 0 < N) {n : ℕ}
    {u : List (Fin N)} (hu : IsCutWord φ n u) {x : ℝ} (hx : x ∈ I) :
    (cutConst φ)⁻¹ * (2 : ℝ)⁻¹ ^ n ≤ |deriv (realComp φ u) x| := by
  have hD := one_lt_distConst hφ
  have hD0 : 0 < distConst φ := distConst_pos
  have hc := cmin_pos hφ hN
  have hc1 : cmin φ < 1 := (cmin_le_cmax hφ).trans_lt (cmax_lt_one hφ)
  have h2n : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := pow_pos (by norm_num) n
  have h2n1 : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h0 : (distConst φ)⁻¹ * cmin φ * (2 : ℝ)⁻¹ ^ n ≤ |deriv (realComp φ u) 0| := by
    rcases List.eq_nil_or_concat u with rfl | ⟨v, i, rfl⟩
    · have : |deriv (realComp φ ([] : List (Fin N))) 0| = 1 := by simp
      rw [this]
      have h3 : (distConst φ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD.le
      calc (distConst φ)⁻¹ * cmin φ * (2 : ℝ)⁻¹ ^ n ≤ 1 * 1 * 1 := by gcongr
        _ = 1 := by ring
    · rw [List.concat_eq_append] at hu ⊢
      have hv := hu.2 v.length (by simp)
      rw [List.take_left' rfl] at hv
      rw [deriv_realComp_append hφ v [i] zero_mem_I, abs_mul]
      have h1 := abs_deriv_realComp_le hφ v zero_mem_I (mapsTo_realComp hφ [i] zero_mem_I)
      have h2 : cmin φ ≤ |deriv (realComp φ [i]) 0| := by
        simpa using cmin_pow_le_abs_deriv_realComp hφ [i] zero_mem_I
      have h4 : (distConst φ)⁻¹ * (2 : ℝ)⁻¹ ^ n ≤
          |deriv (realComp φ v) (realComp φ [i] 0)| := by
        rw [inv_mul_le_iff₀ hD0]
        linarith
      calc (distConst φ)⁻¹ * cmin φ * (2 : ℝ)⁻¹ ^ n
          = ((distConst φ)⁻¹ * (2 : ℝ)⁻¹ ^ n) * cmin φ := by ring
        _ ≤ |deriv (realComp φ v) (realComp φ [i] 0)| * |deriv (realComp φ [i]) 0| :=
            mul_le_mul h4 h2 hc.le (abs_nonneg _)
  have h1 := abs_deriv_realComp_le hφ u zero_mem_I hx
  have hcut : (cutConst φ)⁻¹ = (distConst φ)⁻¹ * ((distConst φ)⁻¹ * cmin φ) := by
    rw [cutConst, inv_div, sq]
    field_simp
  rw [hcut]
  calc (distConst φ)⁻¹ * ((distConst φ)⁻¹ * cmin φ) * (2 : ℝ)⁻¹ ^ n
      = (distConst φ)⁻¹ * ((distConst φ)⁻¹ * cmin φ * (2 : ℝ)⁻¹ ^ n) := by ring
    _ ≤ (distConst φ)⁻¹ * |deriv (realComp φ u) 0| :=
        mul_le_mul_of_nonneg_left h0 (inv_nonneg.2 hD0.le)
    _ ≤ |deriv (realComp φ u) x| := by
        rw [inv_mul_le_iff₀ hD0]
        exact h1

end FractalGeometry.SelfConformal
