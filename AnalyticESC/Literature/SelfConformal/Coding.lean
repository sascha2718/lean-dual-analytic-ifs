module

public import AnalyticESC.Literature.SelfConformal.Bernoulli

@[expose] public section

/-!
# The coding map, the attractor and the self-conformal measure

For a system `φ : Fin N → ℝ → ℝ` satisfying `AnalyticESC.RapaportHyp φ` (Rapaport,
arXiv:2412.16753v2, Section 2.1 and Sections 2.3, 2.6), this file proves the basic properties of
the compositions `φ_u = AnalyticESC.realComp φ u`, the coding map `Π = coding φ`, the attractor
`K = Set.range (coding φ)` and the self-conformal measure `μ = selfConformal φ p hp`.

## Main declarations

* `cmax`, `cmin`: `max` and `min` of `|φ_i'|` over `i` and `I`; `abs_deriv_le_cmax`,
  `cmin_le_abs_deriv`, `cmax_lt_one`, `cmin_pos`, `cmin_le_cmax`.
* `realComp_append`, `mapsTo_realComp`, `differentiableAt_realComp`, `deriv_realComp_cons`,
  `deriv_realComp_append`, `abs_realComp_sub_le`, `continuousOn_realComp`, `injOn_realComp`.
* `tendsto_coding`, `coding_mem`, `coding_eq`, `coding_prepend`, `coding_eq_realComp`,
  `abs_coding_sub_le`, `continuous_coding`, `measurable_coding`.
* `isCompact_range_coding`, `range_coding_nonempty`, `range_coding_subset`,
  `range_coding_eq_iUnion`, `eq_range_coding`, `range_coding_eq_singleton_iff`.
* `isProbabilityMeasure_selfConformal`, `selfConformal_compl_I`, `selfConformal_compl_range`,
  `selfConformal_eq_sum`, `eq_selfConformal` (uniqueness), `selfConformal_singleton` (no atoms).

Copied from the library `FractalGeometry` (module `FractalGeometry.SelfConformal.Coding`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.SelfConformal

open MeasureTheory ProbabilityTheory Set Filter Topology
open AnalyticESC (I realComp RapaportHyp IsProbVec)
open scoped BoundedContinuousFunction

variable {N : ℕ} {φ : Fin N → ℝ → ℝ}

/-! ### Regularity of the maps on `I` -/

/-- `I` is convex. -/
theorem convex_I : Convex ℝ I := convex_Icc 0 1

/-- `I` is compact. -/
theorem isCompact_I : IsCompact I := isCompact_Icc

/-- `I` is nonempty. -/
theorem zero_mem_I : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩

/-- `1 ∈ I`. -/
theorem one_mem_I : (1 : ℝ) ∈ I := ⟨zero_le_one, le_rfl⟩

/-- Points of `I` are at distance at most one. -/
theorem abs_sub_le_one_of_mem_I {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) : |x - y| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- Each map is differentiable at the points of `I`. -/
theorem differentiableAt_map (hφ : RapaportHyp φ) (i : Fin N) {x : ℝ} (hx : x ∈ I) :
    DifferentiableAt ℝ (φ i) x :=
  (hφ.analytic i x hx).differentiableAt

/-- Each map is continuous on `I`. -/
theorem continuousOn_map (hφ : RapaportHyp φ) (i : Fin N) : ContinuousOn (φ i) I :=
  (hφ.analytic i).continuousOn

/-- The derivative of each map is analytic on a neighbourhood of `I`. -/
theorem analyticOnNhd_deriv_map (hφ : RapaportHyp φ) (i : Fin N) :
    AnalyticOnNhd ℝ (deriv (φ i)) I :=
  (hφ.analytic i).deriv

/-- The derivative of each map is continuous on `I`. -/
theorem continuousOn_deriv_map (hφ : RapaportHyp φ) (i : Fin N) :
    ContinuousOn (deriv (φ i)) I :=
  (analyticOnNhd_deriv_map hφ i).continuousOn

/-- `|φ_i'|` attains its maximum on `I`. -/
private theorem exists_iSup_eq (hφ : RapaportHyp φ) (i : Fin N) :
    ∃ x ∈ I, ⨆ y : I, |deriv (φ i) y| = |deriv (φ i) x| := by
  obtain ⟨x, hx, hmax⟩ := isCompact_I.exists_isMaxOn ⟨0, zero_mem_I⟩
    (continuousOn_deriv_map hφ i).abs
  refine ⟨x, hx, le_antisymm (ciSup_le fun y => isMaxOn_iff.1 hmax y y.2) ?_⟩
  exact le_ciSup (f := fun y : I => |deriv (φ i) y|)
    ⟨_, forall_mem_range.2 fun y => isMaxOn_iff.1 hmax y y.2⟩ ⟨x, hx⟩

/-- `|φ_i'|` attains its minimum on `I`. -/
private theorem exists_iInf_eq (hφ : RapaportHyp φ) (i : Fin N) :
    ∃ x ∈ I, ⨅ y : I, |deriv (φ i) y| = |deriv (φ i) x| := by
  obtain ⟨x, hx, hmin⟩ := isCompact_I.exists_isMinOn ⟨0, zero_mem_I⟩
    (continuousOn_deriv_map hφ i).abs
  refine ⟨x, hx, le_antisymm ?_ (le_ciInf fun y => isMinOn_iff.1 hmin y y.2)⟩
  exact ciInf_le (f := fun y : I => |deriv (φ i) y|)
    ⟨_, forall_mem_range.2 fun y => isMinOn_iff.1 hmin y y.2⟩ ⟨x, hx⟩

/-- `|φ_i'|` is bounded on `I`. -/
private theorem bddAbove_abs_deriv (hφ : RapaportHyp φ) (i : Fin N) :
    BddAbove (range fun y : I => |deriv (φ i) y|) := by
  obtain ⟨_, _, hmax⟩ := isCompact_I.exists_isMaxOn ⟨0, zero_mem_I⟩
    (continuousOn_deriv_map hφ i).abs
  exact ⟨_, forall_mem_range.2 fun y => isMaxOn_iff.1 hmax y y.2⟩

/-- `|φ_i'|` is bounded below on `I`. -/
private theorem bddBelow_abs_deriv (i : Fin N) :
    BddBelow (range fun y : I => |deriv (φ i) y|) :=
  ⟨0, forall_mem_range.2 fun _ => abs_nonneg _⟩

/-- `c_max = max_{i, x ∈ I} |φ_i'(x)|` (zero for the empty alphabet). -/
noncomputable def cmax (φ : Fin N → ℝ → ℝ) : ℝ := ⨆ i, ⨆ x : I, |deriv (φ i) x|

/-- `c_min = min_{i, x ∈ I} |φ_i'(x)|` (zero for the empty alphabet). -/
noncomputable def cmin (φ : Fin N → ℝ → ℝ) : ℝ := ⨅ i, ⨅ x : I, |deriv (φ i) x|

/-- `|φ_i'(x)| ≤ c_max` on `I`. -/
theorem abs_deriv_le_cmax (hφ : RapaportHyp φ) (i : Fin N) {x : ℝ} (hx : x ∈ I) :
    |deriv (φ i) x| ≤ cmax φ := by
  refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove i)
  exact le_ciSup (bddAbove_abs_deriv hφ i) ⟨x, hx⟩

/-- `c_min ≤ |φ_i'(x)|` on `I`. -/
theorem cmin_le_abs_deriv (i : Fin N) {x : ℝ} (hx : x ∈ I) : cmin φ ≤ |deriv (φ i) x| := by
  refine le_trans (ciInf_le ⟨0, forall_mem_range.2 fun j => Real.iInf_nonneg fun _ =>
    abs_nonneg _⟩ i) ?_
  exact ciInf_le (bddBelow_abs_deriv i) ⟨x, hx⟩

/-- `0 ≤ c_max`. -/
theorem cmax_nonneg : 0 ≤ cmax φ :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _

/-- `0 ≤ c_min`. -/
theorem cmin_nonneg : 0 ≤ cmin φ :=
  Real.iInf_nonneg fun _ => Real.iInf_nonneg fun _ => abs_nonneg _

/-- `c_max < 1`. -/
theorem cmax_lt_one (hφ : RapaportHyp φ) : cmax φ < 1 := by
  rcases isEmpty_or_nonempty (Fin N) with h | h
  · simp [cmax]
  · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => ⨆ x : I, |deriv (φ i) x|)
    obtain ⟨x, hx, hx'⟩ := exists_iSup_eq hφ i
    rw [cmax, ← hi, hx']
    exact hφ.deriv_lt_one i x hx

/-- `0 < c_min` for a nonempty alphabet. -/
theorem cmin_pos (hφ : RapaportHyp φ) (hN : 0 < N) : 0 < cmin φ := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i => ⨅ x : I, |deriv (φ i) x|)
  obtain ⟨x, hx, hx'⟩ := exists_iInf_eq hφ i
  rw [cmin, ← hi, hx']
  exact hφ.deriv_pos i x hx

/-- `c_min ≤ c_max`. -/
theorem cmin_le_cmax (hφ : RapaportHyp φ) : cmin φ ≤ cmax φ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [cmin, cmax]
  · exact (cmin_le_abs_deriv ⟨0, hN⟩ zero_mem_I).trans (abs_deriv_le_cmax hφ _ zero_mem_I)

/-! ### Compositions -/

@[simp] theorem realComp_nil : realComp φ [] = id := rfl

@[simp] theorem realComp_cons (i : Fin N) (u : List (Fin N)) :
    realComp φ (i :: u) = φ i ∘ realComp φ u := rfl

/-- `φ_{uv} = φ_u ∘ φ_v`. -/
theorem realComp_append (u v : List (Fin N)) :
    realComp φ (u ++ v) = realComp φ u ∘ realComp φ v := by
  induction u with
  | nil => rfl
  | cons i u ih => rw [List.cons_append, realComp_cons, ih, realComp_cons]; rfl

/-- `φ_u` maps `I` into `I`. -/
theorem mapsTo_realComp (hφ : RapaportHyp φ) (u : List (Fin N)) : MapsTo (realComp φ u) I I := by
  induction u with
  | nil => exact mapsTo_id _
  | cons i u ih => exact (hφ.mapsTo i).comp ih

/-- `φ_u` is differentiable at the points of `I`. -/
theorem differentiableAt_realComp (hφ : RapaportHyp φ) (u : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    DifferentiableAt ℝ (realComp φ u) x := by
  induction u with
  | nil => exact differentiableAt_id
  | cons i u ih =>
    exact (differentiableAt_map hφ i (mapsTo_realComp hφ u hx)).comp x ih

/-- The chain rule `φ_{iu}'(x) = φ_i'(φ_u x) φ_u'(x)` on `I`. -/
theorem deriv_realComp_cons (hφ : RapaportHyp φ) (i : Fin N) (u : List (Fin N)) {x : ℝ}
    (hx : x ∈ I) :
    deriv (realComp φ (i :: u)) x = deriv (φ i) (realComp φ u x) * deriv (realComp φ u) x := by
  rw [realComp_cons]
  exact deriv_comp x (differentiableAt_map hφ i (mapsTo_realComp hφ u hx))
    (differentiableAt_realComp hφ u hx)

/-- The chain rule `φ_{uv}'(x) = φ_u'(φ_v x) φ_v'(x)` on `I`. -/
theorem deriv_realComp_append (hφ : RapaportHyp φ) (u v : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    deriv (realComp φ (u ++ v)) x =
      deriv (realComp φ u) (realComp φ v x) * deriv (realComp φ v) x := by
  rw [realComp_append]
  exact deriv_comp x (differentiableAt_realComp hφ u (mapsTo_realComp hφ v hx))
    (differentiableAt_realComp hφ v hx)

/-- Each map is `c_max`-Lipschitz on `I`. -/
theorem abs_map_sub_le (hφ : RapaportHyp φ) (i : Fin N) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    |φ i x - φ i y| ≤ cmax φ * |x - y| := by
  have h := convex_I.norm_image_sub_le_of_norm_deriv_le (f := φ i)
    (fun z hz => differentiableAt_map hφ i hz) (fun z hz => abs_deriv_le_cmax hφ i hz) hy hx
  simpa [Real.norm_eq_abs] using h

/-- `|φ_u x - φ_u y| ≤ c_max^{|u|} |x - y|` on `I`. -/
theorem abs_realComp_sub_le (hφ : RapaportHyp φ) (u : List (Fin N)) {x y : ℝ} (hx : x ∈ I)
    (hy : y ∈ I) : |realComp φ u x - realComp φ u y| ≤ cmax φ ^ u.length * |x - y| := by
  induction u with
  | nil => simp
  | cons i u ih =>
    calc |realComp φ (i :: u) x - realComp φ (i :: u) y|
        ≤ cmax φ * |realComp φ u x - realComp φ u y| :=
          abs_map_sub_le hφ i (mapsTo_realComp hφ u hx) (mapsTo_realComp hφ u hy)
      _ ≤ cmax φ * (cmax φ ^ u.length * |x - y|) := by gcongr; exact cmax_nonneg
      _ = cmax φ ^ (i :: u).length * |x - y| := by rw [List.length_cons, pow_succ]; ring

/-- `|φ_u x - φ_u y| ≤ c_max^{|u|}` on `I`. -/
theorem abs_realComp_sub_le_pow (hφ : RapaportHyp φ) (u : List (Fin N)) {x y : ℝ} (hx : x ∈ I)
    (hy : y ∈ I) : |realComp φ u x - realComp φ u y| ≤ cmax φ ^ u.length :=
  (abs_realComp_sub_le hφ u hx hy).trans
    (mul_le_of_le_one_right (pow_nonneg cmax_nonneg _) (abs_sub_le_one_of_mem_I hx hy))

/-- `φ_u` is continuous on `I`. -/
theorem continuousOn_realComp (hφ : RapaportHyp φ) (u : List (Fin N)) :
    ContinuousOn (realComp φ u) I :=
  fun _ hx => (differentiableAt_realComp hφ u hx).continuousAt.continuousWithinAt

/-- Each map is injective on `I` (its derivative does not vanish there). -/
theorem injOn_map (hφ : RapaportHyp φ) (i : Fin N) : InjOn (φ i) I := by
  have key : ∀ x ∈ I, ∀ y ∈ I, x < y → φ i x ≠ φ i y := by
    intro x hx y hy hxy hxy'
    have hsub : Icc x y ⊆ I := Icc_subset_Icc hx.1 hy.2
    obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope (φ i) hxy ((continuousOn_map hφ i).mono hsub)
      fun z hz => (differentiableAt_map hφ i (hsub (Ioo_subset_Icc_self hz))).differentiableWithinAt
    rw [hxy', sub_self, zero_div] at hc'
    have := hφ.deriv_pos i c (hsub (Ioo_subset_Icc_self hc))
    rw [hc', abs_zero] at this
    exact lt_irrefl 0 this
  intro x hx y hy h
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · exact (key x hx y hy hxy h).elim
  · rfl
  · exact (key y hy x hx hxy h.symm).elim

/-- `φ_u` is injective on `I`. -/
theorem injOn_realComp (hφ : RapaportHyp φ) (u : List (Fin N)) : InjOn (realComp φ u) I := by
  induction u with
  | nil => exact injOn_id _
  | cons i u ih => exact (injOn_map hφ i).comp ih (mapsTo_realComp hφ u)

/-! ### Words and the coding map -/

@[simp] theorem length_word (ω : ℕ → Fin N) (n : ℕ) : (word ω n).length = n :=
  List.length_ofFn

@[simp] theorem word_zero (ω : ℕ → Fin N) : word ω 0 = [] := rfl

/-- `ω|_{n+1} = ω_0 (σ ω)|_n`. -/
theorem word_succ (ω : ℕ → Fin N) (n : ℕ) : word ω (n + 1) = ω 0 :: word (shift ω) n := by
  simp [word, List.ofFn_succ, shift]

/-- `ω|_{n+m} = ω|_n (σ^n ω)|_m`. -/
theorem word_add (ω : ℕ → Fin N) (n m : ℕ) :
    word ω (n + m) = word ω n ++ word (shift^[n] ω) m := by
  induction n generalizing ω with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_right_comm, word_succ, ih, word_succ, Function.iterate_succ_apply]
    rfl

/-- `ω|_{n+1} = ω|_n ω_n`. -/
theorem word_succ' (ω : ℕ → Fin N) (n : ℕ) : word ω (n + 1) = word ω n ++ [ω n] := by
  rw [word_add]
  simp [word, shift_iterate_apply]

/-- The word of the constant sequence. -/
theorem word_const (i : Fin N) (n : ℕ) : word (fun _ => i) n = List.ofFn fun _ : Fin n => i :=
  rfl

/-- `φ_{ω|_{n+m}} = φ_{ω|_n} ∘ φ_{(σ^n ω)|_m}`. -/
theorem realComp_word_add (ω : ℕ → Fin N) (n m : ℕ) (x : ℝ) :
    realComp φ (word ω (n + m)) x = realComp φ (word ω n) (realComp φ (word (shift^[n] ω) m) x) :=
  by rw [word_add, realComp_append]; rfl

/-- `|φ_{ω|_{n+m}}(x) - φ_{ω|_n}(y)| ≤ c_max^n` for `x, y ∈ I`. -/
theorem abs_realComp_word_sub_le (hφ : RapaportHyp φ) (ω : ℕ → Fin N) (n m : ℕ) {x y : ℝ}
    (hx : x ∈ I) (hy : y ∈ I) :
    |realComp φ (word ω (n + m)) x - realComp φ (word ω n) y| ≤ cmax φ ^ n := by
  rw [realComp_word_add]
  have := abs_realComp_sub_le_pow hφ (word ω n) (mapsTo_realComp hφ (word (shift^[n] ω) m) hx) hy
  rwa [length_word] at this

/-- `c_max^n → 0`. -/
theorem tendsto_cmax_pow (hφ : RapaportHyp φ) :
    Tendsto (fun n : ℕ => cmax φ ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one cmax_nonneg (cmax_lt_one hφ)

/-- The approximations `φ_{ω|_n}(0)` form a Cauchy sequence. -/
theorem cauchySeq_realComp_word (hφ : RapaportHyp φ) (ω : ℕ → Fin N) :
    CauchySeq fun n => realComp φ (word ω n) 0 := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 ((tendsto_cmax_pow hφ).eventually (gt_mem_nhds hε))
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Real.dist_eq]
  exact (abs_realComp_word_sub_le hφ ω n₀ m zero_mem_I zero_mem_I).trans_lt (hn₀ n₀ le_rfl)

/-- The coding map is well defined: `φ_{ω|_n}(0) → Π(ω)`. -/
theorem tendsto_coding (hφ : RapaportHyp φ) (ω : ℕ → Fin N) :
    Tendsto (fun n => realComp φ (word ω n) 0) atTop (𝓝 (coding φ ω)) :=
  (cauchySeq_realComp_word hφ ω).tendsto_limUnder

/-- `Π(ω) ∈ I`. -/
theorem coding_mem (hφ : RapaportHyp φ) (ω : ℕ → Fin N) : coding φ ω ∈ I :=
  isClosed_Icc.mem_of_tendsto (tendsto_coding hφ ω)
    (Eventually.of_forall fun _ => mapsTo_realComp hφ _ zero_mem_I)

/-- `|Π(ω) - φ_{ω|_n}(x)| ≤ c_max^n` for `x ∈ I`. -/
theorem abs_coding_sub_le (hφ : RapaportHyp φ) (ω : ℕ → Fin N) (n : ℕ) {x : ℝ} (hx : x ∈ I) :
    |coding φ ω - realComp φ (word ω n) x| ≤ cmax φ ^ n := by
  have h : Tendsto (fun m => |realComp φ (word ω (n + m)) 0 - realComp φ (word ω n) x|) atTop
      (𝓝 |coding φ ω - realComp φ (word ω n) x|) :=
    (((tendsto_coding hφ ω).comp
      (tendsto_atTop_mono (fun m => Nat.le_add_left m n) tendsto_id)).sub_const _).abs
  exact le_of_tendsto' h fun m => abs_realComp_word_sub_le hφ ω n m zero_mem_I hx

/-- `φ_{ω|_n}(x) → Π(ω)` for every `x ∈ I`. -/
theorem tendsto_realComp_word (hφ : RapaportHyp φ) (ω : ℕ → Fin N) {x : ℝ} (hx : x ∈ I) :
    Tendsto (fun n => realComp φ (word ω n) x) atTop (𝓝 (coding φ ω)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) (tendsto_cmax_pow hφ)
  rw [Real.dist_eq, abs_sub_comm]
  exact abs_coding_sub_le hφ ω n hx

/-- `Π(ω) = φ_{ω|_n}(Π(σ^n ω))`. -/
theorem coding_eq_realComp (hφ : RapaportHyp φ) (ω : ℕ → Fin N) (n : ℕ) :
    coding φ ω = realComp φ (word ω n) (coding φ (shift^[n] ω)) := by
  have h1 : Tendsto (fun m => realComp φ (word ω (n + m)) 0) atTop (𝓝 (coding φ ω)) :=
    (tendsto_coding hφ ω).comp (tendsto_atTop_mono (fun m => Nat.le_add_left m n) tendsto_id)
  have h2 : Tendsto (fun m => realComp φ (word ω (n + m)) 0) atTop
      (𝓝 (realComp φ (word ω n) (coding φ (shift^[n] ω)))) := by
    simp_rw [realComp_word_add]
    have ht : Tendsto (fun m => realComp φ (word (shift^[n] ω) m) 0) atTop
        (𝓝[I] (coding φ (shift^[n] ω))) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_coding hφ _,
        Eventually.of_forall fun _ => mapsTo_realComp hφ _ zero_mem_I⟩
    exact ((continuousOn_realComp hφ _) _ (coding_mem hφ _)).tendsto.comp ht
  exact tendsto_nhds_unique h1 h2

/-- `Π(ω) = φ_{ω_0}(Π(σ ω))`. -/
theorem coding_eq (hφ : RapaportHyp φ) (ω : ℕ → Fin N) :
    coding φ ω = φ (ω 0) (coding φ (shift ω)) := by
  have h := coding_eq_realComp hφ ω 1
  simpa [word_succ] using h

/-- `Π(i ω) = φ_i(Π(ω))`. -/
theorem coding_prepend (hφ : RapaportHyp φ) (i : Fin N) (ω : ℕ → Fin N) :
    coding φ (prepend i ω) = φ i (coding φ ω) := by
  rw [coding_eq hφ]
  rfl

/-- On the cylinder `[u]` of a word of length `n`, `Π(ω) = φ_u(Π(σ^n ω))`. -/
theorem coding_eq_of_mem_cylinder (hφ : RapaportHyp φ) {n : ℕ} {u : Fin n → Fin N}
    {ω : ℕ → Fin N} (hω : ω ∈ cylinder u) :
    coding φ ω = realComp φ (List.ofFn u) (coding φ (shift^[n] ω)) := by
  rw [coding_eq_realComp hφ ω n, (mem_cylinder_iff_word u ω).1 hω]

/-- The coding map is measurable (for any system: it is a pointwise limit, where it exists, of
functions of finitely many coordinates). -/
theorem measurable_coding (φ : Fin N → ℝ → ℝ) : Measurable (coding φ) := by
  have h : ∀ n, StronglyMeasurable fun ω : ℕ → Fin N => realComp φ (word ω n) 0 := by
    intro n
    have hm : Measurable fun ω : ℕ → Fin N => fun k : Fin n => ω k :=
      Measurable.of_eval fun k => measurable_pi_apply _
    exact ((measurable_of_finite
      (fun v : Fin n → Fin N => realComp φ (List.ofFn v) 0)).comp hm).stronglyMeasurable
  exact (StronglyMeasurable.limUnder (l := atTop)
    (f := fun n ω => realComp φ (word ω n) 0) h).measurable

/-- The coding map is continuous. -/
theorem continuous_coding (hφ : RapaportHyp φ) : Continuous (coding φ) := by
  refine TendstoUniformly.continuous (F := fun n ω => realComp φ (word ω n) 0) (p := atTop) ?_
    (Frequently.of_forall fun n => ?_)
  · rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    filter_upwards [(tendsto_cmax_pow hφ).eventually (gt_mem_nhds hδ)] with n hn ω
    rw [Real.dist_eq]
    exact (abs_coding_sub_le hφ ω n zero_mem_I).trans_lt hn
  · exact (continuous_of_discreteTopology
      (f := fun v : Fin n → Fin N => realComp φ (List.ofFn v) 0)).comp
      (continuous_pi fun k => continuous_apply (k : ℕ))

/-- `ω ↦ φ_u(Π(ω))` is continuous. -/
theorem continuous_realComp_coding (hφ : RapaportHyp φ) (u : List (Fin N)) :
    Continuous fun ω => realComp φ u (coding φ ω) :=
  (continuousOn_realComp hφ u).comp_continuous (continuous_coding hφ) (coding_mem hφ)

/-! ### The attractor `K = Π(Σ)` -/

/-- The attractor is compact. -/
theorem isCompact_range_coding (hφ : RapaportHyp φ) : IsCompact (range (coding φ)) :=
  isCompact_range (continuous_coding hφ)

/-- The attractor is nonempty for a nonempty alphabet. -/
theorem range_coding_nonempty (hN : 0 < N) : (range (coding φ)).Nonempty :=
  ⟨_, mem_range_self fun _ => (⟨0, hN⟩ : Fin N)⟩

/-- The attractor lies in `I`. -/
theorem range_coding_subset (hφ : RapaportHyp φ) : range (coding φ) ⊆ I :=
  range_subset_iff.2 (coding_mem hφ)

/-- The attractor is invariant: `K = ⋃_i φ_i(K)`. -/
theorem range_coding_eq_iUnion (hφ : RapaportHyp φ) :
    range (coding φ) = ⋃ i, φ i '' range (coding φ) := by
  ext x
  simp only [mem_iUnion, mem_image, mem_range]
  constructor
  · rintro ⟨ω, rfl⟩
    exact ⟨ω 0, coding φ (shift ω), ⟨shift ω, rfl⟩, (coding_eq hφ ω).symm⟩
  · rintro ⟨i, _, ⟨ω, rfl⟩, rfl⟩
    exact ⟨prepend i ω, coding_prepend hφ i ω⟩

/-- Uniqueness of the attractor: a nonempty compact `K' ⊆ I` with `K' = ⋃_i φ_i(K')` is the
attractor. -/
theorem eq_range_coding (hφ : RapaportHyp φ) {K' : Set ℝ} (hne : K'.Nonempty)
    (hcpt : IsCompact K') (hsub : K' ⊆ I) (hinv : K' = ⋃ i, φ i '' K') :
    K' = range (coding φ) := by
  have hmaps : ∀ i, MapsTo (φ i) K' K' := fun i y hy => by
    rw [hinv]
    exact mem_iUnion.2 ⟨i, mem_image_of_mem _ hy⟩
  have hcomp : ∀ u : List (Fin N), MapsTo (realComp φ u) K' K' := by
    intro u
    induction u with
    | nil => exact mapsTo_id _
    | cons i u ih => exact (hmaps i).comp ih
  apply Subset.antisymm
  · intro y hy
    have hpre : ∀ z : K', ∃ i, ∃ w : K', φ i w = z := by
      intro z
      have hz := hinv.subset z.2
      obtain ⟨i, hi⟩ := mem_iUnion.1 hz
      obtain ⟨w, hw, hwz⟩ := hi
      exact ⟨i, ⟨w, hw⟩, hwz⟩
    choose g h hg using hpre
    let seq : ℕ → K' := fun k => h^[k] ⟨y, hy⟩
    let ω : ℕ → Fin N := fun k => g (seq k)
    have key : ∀ n, y = realComp φ (word ω n) (seq n) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [word_succ', realComp_append]
        have hs : (seq (n + 1) : ℝ) = h (seq n) := by
          simp only [seq, Function.iterate_succ_apply']
        simp only [Function.comp_apply, realComp_cons, realComp_nil, Function.comp_id, hs]
        rw [hg]
        exact ih
    refine ⟨ω, ?_⟩
    have hle : ∀ n, |coding φ ω - y| ≤ cmax φ ^ n := fun n => by
      rw [key n]
      exact abs_coding_sub_le hφ ω n (hsub (seq n).2)
    have := ge_of_tendsto' (tendsto_cmax_pow hφ) hle
    exact sub_eq_zero.1 (abs_nonpos_iff.1 this)
  · rintro _ ⟨ω, rfl⟩
    obtain ⟨y, hy⟩ := hne
    exact hcpt.isClosed.mem_of_tendsto (tendsto_realComp_word hφ ω (hsub hy))
      (Eventually.of_forall fun n => hcomp _ hy)

/-- The attractor is a singleton exactly when the maps have a common fixed point in `I`. -/
theorem range_coding_eq_singleton_iff (hφ : RapaportHyp φ) (hN : 0 < N) :
    (∃ x, range (coding φ) = {x}) ↔ ∃ x ∈ I, ∀ i, φ i x = x := by
  constructor
  · rintro ⟨x, hx⟩
    have hc : ∀ i : Fin N, coding φ (fun _ => i) = x := fun i => by
      have h : coding φ (fun _ => i) ∈ range (coding φ) := mem_range_self _
      rwa [hx] at h
    refine ⟨x, hc ⟨0, hN⟩ ▸ coding_mem hφ _, fun i => ?_⟩
    have h := coding_eq hφ (fun _ => i)
    rw [show shift (fun _ : ℕ => i) = fun _ => i from rfl, hc i] at h
    exact h.symm
  · rintro ⟨x, hx, hfix⟩
    have hc : ∀ u : List (Fin N), realComp φ u x = x := by
      intro u
      induction u with
      | nil => rfl
      | cons i u ih => rw [realComp_cons, Function.comp_apply, ih, hfix]
    have hπ : ∀ ω, coding φ ω = x := by
      intro ω
      have hle : ∀ n, |coding φ ω - x| ≤ cmax φ ^ n := fun n => by
        have := abs_coding_sub_le hφ ω n hx
        rwa [hc] at this
      exact sub_eq_zero.1 (abs_nonpos_iff.1 (ge_of_tendsto' (tendsto_cmax_pow hφ) hle))
    refine ⟨x, ?_⟩
    ext y
    constructor
    · rintro ⟨ω, rfl⟩
      exact hπ ω
    · rintro rfl
      exact ⟨fun _ => ⟨0, hN⟩, hπ _⟩

/-! ### Measures carried by `I` -/

/-- A measure with `ν Iᶜ = 0` is carried by `I`. -/
theorem ae_mem_I_of_compl {ν : Measure ℝ} (h : ν Iᶜ = 0) : ∀ᵐ x ∂ν, x ∈ I :=
  ae_iff.2 h

/-- A measure with `ν Iᶜ = 0` equals its restriction to `I`. -/
theorem restrict_I_eq_self {ν : Measure ℝ} (h : ν Iᶜ = 0) : ν.restrict I = ν :=
  Measure.restrict_eq_self_of_ae_mem (ae_mem_I_of_compl h)

/-- `φ_u` is almost everywhere measurable for a measure carried by `I`. -/
theorem aemeasurable_realComp (hφ : RapaportHyp φ) (u : List (Fin N)) {ν : Measure ℝ}
    (h : ν Iᶜ = 0) : AEMeasurable (realComp φ u) ν := by
  rw [← restrict_I_eq_self h]
  exact (continuousOn_realComp hφ u).aemeasurable measurableSet_Icc

/-- Each map is almost everywhere measurable for a measure carried by `I`. -/
theorem aemeasurable_map (hφ : RapaportHyp φ) (i : Fin N) {ν : Measure ℝ} (h : ν Iᶜ = 0) :
    AEMeasurable (φ i) ν := by
  rw [← restrict_I_eq_self h]
  exact (continuousOn_map hφ i).aemeasurable measurableSet_Icc

/-! ### The self-conformal measure -/

/-- The self-conformal measure is a probability measure. -/
instance isProbabilityMeasure_selfConformal (φ : Fin N → ℝ → ℝ) {p : Fin N → ℝ}
    (hp : IsProbVec p) : IsProbabilityMeasure (selfConformal φ p hp) := by
  unfold selfConformal
  infer_instance

/-- `μ(s) = β(Π⁻¹ s)` for measurable `s`. -/
theorem selfConformal_apply (φ : Fin N → ℝ → ℝ) {p : Fin N → ℝ} (hp : IsProbVec p)
    {s : Set ℝ} (hs : MeasurableSet s) :
    selfConformal φ p hp s = bernoulli p hp (coding φ ⁻¹' s) :=
  Measure.map_apply (measurable_coding φ) hs

/-- `μ` is carried by `I`. -/
theorem selfConformal_compl_I (hφ : RapaportHyp φ) {p : Fin N → ℝ} (hp : IsProbVec p) :
    selfConformal φ p hp Iᶜ = 0 := by
  rw [selfConformal_apply φ hp measurableSet_Icc.compl]
  exact measure_mono_null (fun ω hω => (hω (coding_mem hφ ω)).elim) measure_empty

/-- `μ`-almost every point lies in `I`. -/
theorem ae_mem_I (hφ : RapaportHyp φ) {p : Fin N → ℝ} (hp : IsProbVec p) :
    ∀ᵐ x ∂selfConformal φ p hp, x ∈ I :=
  ae_mem_I_of_compl (selfConformal_compl_I hφ hp)

/-- `μ` is carried by the attractor. -/
theorem selfConformal_compl_range (hφ : RapaportHyp φ) {p : Fin N → ℝ} (hp : IsProbVec p) :
    selfConformal φ p hp (range (coding φ))ᶜ = 0 := by
  rw [selfConformal_apply φ hp (isCompact_range_coding hφ).isClosed.measurableSet.compl]
  exact measure_mono_null (fun ω hω => (hω (mem_range_self ω)).elim) measure_empty

/-- `μ ∘ φ_u⁻¹ = β ∘ (φ_u ∘ Π)⁻¹`. -/
theorem map_realComp_selfConformal (hφ : RapaportHyp φ) {p : Fin N → ℝ} (hp : IsProbVec p)
    (u : List (Fin N)) :
    (selfConformal φ p hp).map (realComp φ u) =
      (bernoulli p hp).map fun ω => realComp φ u (coding φ ω) := by
  rw [selfConformal, AEMeasurable.map_map_of_aemeasurable
    (aemeasurable_realComp hφ u (selfConformal_compl_I hφ hp)) (measurable_coding φ).aemeasurable]
  rfl

/-- `μ ∘ φ_i⁻¹ = β ∘ (φ_i ∘ Π)⁻¹`. -/
theorem map_map_selfConformal (hφ : RapaportHyp φ) {p : Fin N → ℝ} (hp : IsProbVec p)
    (i : Fin N) :
    (selfConformal φ p hp).map (φ i) = (bernoulli p hp).map fun ω => φ i (coding φ ω) := by
  rw [selfConformal, AEMeasurable.map_map_of_aemeasurable
    (aemeasurable_map hφ i (selfConformal_compl_I hφ hp)) (measurable_coding φ).aemeasurable]
  rfl

/-- `∫⁻ f d(step p) = ∑_i p_i f(i)`. -/
theorem lintegral_step (p : Fin N → ℝ) (f : Fin N → ENNReal) :
    ∫⁻ i, f i ∂step p = ∑ i, ENNReal.ofReal (p i) * f i := by
  simp [step, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac]

/-- The self-conformal relation `μ = ∑_i p_i μ ∘ φ_i⁻¹`. -/
theorem selfConformal_eq_sum (hφ : RapaportHyp φ) {p : Fin N → ℝ} (hp : IsProbVec p) :
    selfConformal φ p hp = ∑ i, ENNReal.ofReal (p i) • (selfConformal φ p hp).map (φ i) := by
  ext s hs
  have hcont : ∀ i, Continuous fun ω => φ i (coding φ ω) := fun i =>
    (continuousOn_map hφ i).comp_continuous (continuous_coding hφ) (coding_mem hφ)
  have hpre : MeasurableSet ((fun q : Fin N × (ℕ → Fin N) => prepend q.1 q.2) ⁻¹'
      (coding φ ⁻¹' s)) := measurable_prepend (measurable_coding φ hs)
  rw [selfConformal_apply φ hp hs, ← map_prepend_bernoulli hp,
    Measure.map_apply measurable_prepend (measurable_coding φ hs),
    Measure.prod_apply hpre, lintegral_step]
  simp only [Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_map_selfConformal hφ hp i, Measure.map_apply (hcont i).measurable hs]
  congr 2
  ext ω
  simp [coding_prepend hφ]

/-! ### Uniqueness of the self-conformal measure -/

/-- The retraction `x ↦ max 0 (min 1 x)` of `ℝ` onto `I`. -/
def clampI (x : ℝ) : ℝ := max 0 (min 1 x)

/-- The retraction onto `I` is continuous. -/
theorem continuous_clampI : Continuous clampI :=
  continuous_const.max (continuous_const.min continuous_id)

/-- The retraction takes values in `I`. -/
theorem clampI_mem (x : ℝ) : clampI x ∈ I :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- The retraction fixes `I`. -/
theorem clampI_of_mem {x : ℝ} (hx : x ∈ I) : clampI x = x := by
  simp [clampI, hx.1, hx.2]

/-- The continuous extensions `φ_i ∘ clampI` of the maps. -/
def extend (φ : Fin N → ℝ → ℝ) (i : Fin N) (x : ℝ) : ℝ := φ i (clampI x)

/-- The extended maps are continuous. -/
theorem continuous_extend (hφ : RapaportHyp φ) (i : Fin N) : Continuous (extend φ i) :=
  (continuousOn_map hφ i).comp_continuous continuous_clampI clampI_mem

/-- The compositions of the extended maps are continuous. -/
theorem continuous_realComp_extend (hφ : RapaportHyp φ) (u : List (Fin N)) :
    Continuous (realComp (extend φ) u) := by
  induction u with
  | nil => exact continuous_id
  | cons i u ih => exact (continuous_extend hφ i).comp ih

/-- The compositions of the extended maps agree with `φ_u` on `I`. -/
theorem realComp_extend (hφ : RapaportHyp φ) (u : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    realComp (extend φ) u x = realComp φ u x := by
  induction u with
  | nil => rfl
  | cons i u ih =>
    simp only [realComp_cons, Function.comp_apply, ih, extend,
      clampI_of_mem (mapsTo_realComp hφ u hx)]

/-- The sum of the cylinder weights of length `n` is one. -/
theorem sum_prod_weights {p : Fin N → ℝ} (hp : IsProbVec p) (n : ℕ) :
    ∑ u : Fin n → Fin N, ∏ k, p (u k) = 1 := by
  have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin N)))
    (fun _ i => p i)
  rw [Fintype.piFinset_univ] at h
  rw [← h, hp.2]
  simp

/-- One step of the self-conformal relation tested against a bounded continuous function. -/
private theorem integral_eq_sum_step (hφ : RapaportHyp φ) {p : Fin N → ℝ} (hp : IsProbVec p)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hνI : ν Iᶜ = 0)
    (hν : ν = ∑ i, ENNReal.ofReal (p i) • ν.map (φ i)) (g : ℝ →ᵇ ℝ) :
    ∫ x, g x ∂ν = ∑ i, p i * ∫ x, g (extend φ i x) ∂ν := by
  have hmap : ∀ i, ν.map (φ i) = ν.map (extend φ i) := fun i => Measure.map_congr <| by
    filter_upwards [ae_mem_I_of_compl hνI] with x hx
    simp [extend, clampI_of_mem hx]
  calc ∫ x, g x ∂ν = ∫ x, g x ∂(∑ i, ENNReal.ofReal (p i) • ν.map (extend φ i)) := by
        simp_rw [← hmap]
        exact congrArg (fun m => ∫ x, g x ∂m) hν
    _ = ∑ i, p i * ∫ x, g (extend φ i x) ∂ν := by
        rw [integral_finsetSum_measure fun i _ =>
          (g.integrable (ν.map (extend φ i))).smul_measure ENNReal.ofReal_ne_top]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_smul_measure, ENNReal.toReal_ofReal (hp.1 i).le, smul_eq_mul,
          integral_map (continuous_extend hφ i).aemeasurable g.continuous.aestronglyMeasurable]

/-- The `n`-fold iterate of the self-conformal relation tested against a bounded continuous
function. -/
private theorem integral_eq_sum_iterate (hφ : RapaportHyp φ) {p : Fin N → ℝ} (hp : IsProbVec p)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hνI : ν Iᶜ = 0)
    (hν : ν = ∑ i, ENNReal.ofReal (p i) • ν.map (φ i)) (n : ℕ) (g : ℝ →ᵇ ℝ) :
    ∫ x, g x ∂ν = ∑ u : Fin n → Fin N,
      (∏ k, p (u k)) * ∫ x, g (realComp (extend φ) (List.ofFn u) x) ∂ν := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    rw [integral_eq_sum_step hφ hp hνI hν g]
    have h2 : ∀ i, ∫ x, g (extend φ i x) ∂ν = ∑ u : Fin n → Fin N,
        (∏ k, p (u k)) * ∫ x, g (extend φ i (realComp (extend φ) (List.ofFn u) x)) ∂ν :=
      fun i => ih (g.compContinuous ⟨extend φ i, continuous_extend hφ i⟩)
    simp_rw [h2, Finset.mul_sum]
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => Fin N).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u _ => ?_
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      List.ofFn_succ, realComp_cons, Function.comp_apply]
    ring

/-- For a probability measure `ν` on `I` with `ν = ∑_i p_i ν ∘ φ_i⁻¹`, `∫ g dν` is within `ε` of
`∑_{|u| = n} p_u g(φ_u(0))` once `c_max^n` is below a modulus of uniform continuity `δ` of `g`
on `I` for `ε`. -/
private theorem abs_integral_sub_sum_le (hφ : RapaportHyp φ) {p : Fin N → ℝ} (hp : IsProbVec p)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hνI : ν Iᶜ = 0)
    (hν : ν = ∑ i, ENNReal.ofReal (p i) • ν.map (φ i)) (g : ℝ →ᵇ ℝ) {ε δ : ℝ}
    (hδ : ∀ x ∈ I, ∀ y ∈ I, dist x y < δ → dist (g x) (g y) < ε) {n : ℕ}
    (hn : cmax φ ^ n < δ) :
    |∫ x, g x ∂ν - ∑ u : Fin n → Fin N, (∏ k, p (u k)) * g (realComp φ (List.ofFn u) 0)| ≤ ε := by
  rw [integral_eq_sum_iterate hφ hp hνI hν n g, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ u : Fin n → Fin N, |(∏ k, p (u k)) * ∫ x, g (realComp (extend φ) (List.ofFn u) x)
      ∂ν - (∏ k, p (u k)) * g (realComp φ (List.ofFn u) 0)| ≤ (∏ k, p (u k)) * ε := by
    intro u
    have hpu : 0 ≤ ∏ k, p (u k) := Finset.prod_nonneg fun k _ => (hp.1 _).le
    rw [← mul_sub, abs_mul, abs_of_nonneg hpu]
    refine mul_le_mul_of_nonneg_left ?_ hpu
    have hint : ∫ x, g (realComp (extend φ) (List.ofFn u) x) ∂ν - g (realComp φ (List.ofFn u) 0)
        = ∫ x, (g (realComp (extend φ) (List.ofFn u) x) - g (realComp φ (List.ofFn u) 0)) ∂ν := by
      have hi : Integrable (fun x => g (realComp (extend φ) (List.ofFn u) x)) ν :=
        (g.compContinuous ⟨_, continuous_realComp_extend hφ (List.ofFn u)⟩).integrable ν
      rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul]
    rw [hint, ← Real.norm_eq_abs]
    have hb := norm_integral_le_of_norm_le_const (μ := ν) (C := ε)
      (f := fun x => g (realComp (extend φ) (List.ofFn u) x) - g (realComp φ (List.ofFn u) 0))
      (by
        filter_upwards [ae_mem_I_of_compl hνI] with x hx
        rw [realComp_extend hφ _ hx, Real.norm_eq_abs, ← Real.dist_eq]
        refine (hδ _ (mapsTo_realComp hφ _ hx) _ (mapsTo_realComp hφ _ zero_mem_I) ?_).le
        rw [Real.dist_eq]
        refine lt_of_le_of_lt ?_ hn
        have := abs_realComp_sub_le_pow hφ (List.ofFn u) hx zero_mem_I
        rwa [List.length_ofFn] at this)
    rwa [probReal_univ, mul_one] at hb
  refine (Finset.sum_le_sum fun u _ => hterm u).trans ?_
  rw [← Finset.sum_mul, sum_prod_weights hp, one_mul]

/-- Uniqueness of the self-conformal measure: a probability measure `ν` on `ℝ` with `ν Iᶜ = 0`
and `ν = ∑_i p_i ν ∘ φ_i⁻¹` is the self-conformal measure. -/
theorem eq_selfConformal (hφ : RapaportHyp φ) {p : Fin N → ℝ} (hp : IsProbVec p)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hνI : ν Iᶜ = 0)
    (hν : ν = ∑ i, ENNReal.ofReal (p i) • ν.map (φ i)) : ν = selfConformal φ p hp := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
  have hunif := (isCompact_I.uniformContinuousOn_of_continuous g.continuous.continuousOn)
  rw [Metric.uniformContinuousOn_iff] at hunif
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨δ, hδ, hδ'⟩ := hunif (ε / 2) (half_pos hε)
  obtain ⟨n, hn⟩ := ((tendsto_cmax_pow hφ).eventually (gt_mem_nhds hδ)).exists
  have h1 := abs_integral_sub_sum_le hφ hp hνI hν g hδ' hn
  have h2 := abs_integral_sub_sum_le hφ hp (selfConformal_compl_I hφ hp)
    (selfConformal_eq_sum hφ hp) g hδ' hn
  calc dist (∫ x, g x ∂ν) (∫ x, g x ∂selfConformal φ p hp)
      ≤ dist (∫ x, g x ∂ν)
          (∑ u : Fin n → Fin N, (∏ k, p (u k)) * g (realComp φ (List.ofFn u) 0)) +
        dist (∫ x, g x ∂selfConformal φ p hp)
          (∑ u : Fin n → Fin N, (∏ k, p (u k)) * g (realComp φ (List.ofFn u) 0)) :=
        dist_triangle_right _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (by rwa [Real.dist_eq]) (by rwa [Real.dist_eq])
    _ = ε := add_halves ε

/-! ### Cylinder decomposition and absence of atoms -/

/-- `β([u] ∩ Π⁻¹ S) = p_u β((φ_u ∘ Π)⁻¹ S)` for a word `u` and measurable `S`. -/
theorem bernoulli_cylinder_inter_coding (hφ : RapaportHyp φ) {p : Fin N → ℝ} (hp : IsProbVec p)
    {n : ℕ} (u : Fin n → Fin N) {S : Set ℝ} (hS : MeasurableSet S) :
    bernoulli p hp (cylinder u ∩ coding φ ⁻¹' S) =
      (∏ k, ENNReal.ofReal (p (u k))) *
        bernoulli p hp ((fun ω => realComp φ (List.ofFn u) (coding φ ω)) ⁻¹' S) := by
  have h : cylinder u ∩ coding φ ⁻¹' S = cylinder u ∩ shift^[n] ⁻¹'
      ((fun ω => realComp φ (List.ofFn u) (coding φ ω)) ⁻¹' S) := by
    ext ω
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hω, hS⟩
      exact ⟨hω, coding_eq_of_mem_cylinder hφ hω ▸ hS⟩
    · rintro ⟨hω, hS⟩
      exact ⟨hω, (coding_eq_of_mem_cylinder hφ hω).symm ▸ hS⟩
  rw [h, bernoulli_cylinder_inter_shift_iterate hp u
    ((continuous_realComp_coding hφ _).measurable hS)]

/-- The self-conformal measure of a set, decomposed along the cylinders of length `n`. -/
theorem measureReal_selfConformal_eq_sum (φ : Fin N → ℝ → ℝ) {p : Fin N → ℝ} (hp : IsProbVec p)
    (n : ℕ) {S : Set ℝ} (hS : MeasurableSet S) :
    (selfConformal φ p hp).real S =
      ∑ u : Fin n → Fin N, (bernoulli p hp).real (cylinder u ∩ coding φ ⁻¹' S) := by
  rw [measureReal_def, selfConformal_apply φ hp hS, ← measureReal_def]
  have h : coding φ ⁻¹' S = ⋃ u : Fin n → Fin N, cylinder u ∩ coding φ ⁻¹' S := by
    rw [← iUnion_inter, iUnion_cylinder, univ_inter]
  conv_lhs => rw [h]
  exact measureReal_iUnion_fintype
    (fun u v huv => ((disjoint_cylinder huv).inter_right _).inter_left _)
    (fun u => (measurableSet_cylinder u).inter (measurable_coding φ hS))

/-- **No atoms** (Rapaport, Section 2.3): if the maps have no common fixed point, the
self-conformal measure has no atoms. -/
theorem selfConformal_singleton (hφ : RapaportHyp φ) {p : Fin N → ℝ} (hp : IsProbVec p)
    (x : ℝ) : selfConformal φ p hp {x} = 0 := by
  by_contra hx0
  set μ := selfConformal φ p hp with hμ
  have hN := pos_of_isProbVec hp
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  -- the largest atom
  have hbdd : BddAbove (range fun y => μ.real {y}) :=
    ⟨1, forall_mem_range.2 fun y => measureReal_le_one⟩
  set a := ⨆ y : ℝ, μ.real {y} with ha_def
  have hxpos : 0 < μ.real {x} := ENNReal.toReal_pos hx0 (measure_ne_top _ _)
  have ha : 0 < a := hxpos.trans_le (le_ciSup hbdd x)
  have hle_a : ∀ y, μ.real {y} ≤ a := fun y => le_ciSup hbdd y
  -- the smallest weight
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciInf_of_finite (f := p)
  set q := ⨅ i, p i with hq_def
  have hq : 0 < q := hi₀ ▸ hp.1 i₀
  have hqle : ∀ i, q ≤ p i := fun i => ciInf_le (Set.finite_range p).bddBelow i
  -- the mass of a cylinder piece is at most `p_u a`
  have hpiece : ∀ {n : ℕ} (u : Fin n → Fin N) (y : ℝ),
      (bernoulli p hp).real (cylinder u ∩ coding φ ⁻¹' {y}) ≤ (∏ k, p (u k)) * a := by
    intro n u y
    rw [measureReal_def, bernoulli_cylinder_inter_coding hφ hp u (measurableSet_singleton y),
      ENNReal.toReal_mul, ENNReal.toReal_prod]
    simp_rw [ENNReal.toReal_ofReal (hp.1 _).le]
    refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun k _ => (hp.1 _).le)
    by_cases hy : ∃ z ∈ I, realComp φ (List.ofFn u) z = y
    · obtain ⟨z, hz, rfl⟩ := hy
      have hsub : (fun ω => realComp φ (List.ofFn u) (coding φ ω)) ⁻¹'
          {realComp φ (List.ofFn u) z} ⊆ coding φ ⁻¹' {z} := fun ω hω =>
        injOn_realComp hφ _ (coding_mem hφ ω) hz hω
      refine le_trans ?_ (hle_a z)
      rw [← measureReal_def, measureReal_def μ,
        selfConformal_apply φ hp (measurableSet_singleton z), ← measureReal_def]
      exact measureReal_mono hsub
    · push Not at hy
      have hempty : (fun ω => realComp φ (List.ofFn u) (coding φ ω)) ⁻¹' {y} = ∅ :=
        eq_empty_of_forall_notMem fun ω hω => hy _ (coding_mem hφ ω) hω
      rw [hempty, measure_empty, ENNReal.toReal_zero]
      exact ha.le
  -- for every `n` some point lies in all the images `φ_u(I)`, `|u| = n`
  have key : ∀ n : ℕ, ∃ y, ∀ u : Fin n → Fin N, ∃ z ∈ I, realComp φ (List.ofFn u) z = y := by
    intro n
    have hqn : 0 < q ^ n := pow_pos hq n
    obtain ⟨y, hy⟩ := exists_lt_of_lt_ciSup (show (1 - q ^ n) * a < a by nlinarith)
    refine ⟨y, fun u₀ => ?_⟩
    by_contra hnot
    push Not at hnot
    have h0 : (bernoulli p hp).real (cylinder u₀ ∩ coding φ ⁻¹' {y}) = 0 := by
      have : cylinder u₀ ∩ coding φ ⁻¹' {y} = ∅ := by
        refine eq_empty_of_forall_notMem fun ω hω => ?_
        exact hnot _ (coding_mem hφ _) ((coding_eq_of_mem_cylinder hφ hω.1).symm.trans hω.2)
      rw [this, measureReal_empty]
    have hsum := measureReal_selfConformal_eq_sum φ hp n (measurableSet_singleton y)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u₀), h0, zero_add] at hsum
    have hbound : μ.real {y} ≤ (1 - q ^ n) * a := by
      rw [hsum]
      calc ∑ u ∈ Finset.univ.erase u₀, (bernoulli p hp).real (cylinder u ∩ coding φ ⁻¹' {y})
          ≤ ∑ u ∈ Finset.univ.erase u₀, (∏ k, p (u k)) * a :=
            Finset.sum_le_sum fun u _ => hpiece u y
        _ = (1 - ∏ k, p (u₀ k)) * a := by
            rw [← Finset.sum_mul, ← sum_prod_weights hp n,
              ← Finset.add_sum_erase _ _ (Finset.mem_univ u₀)]
            ring
        _ ≤ (1 - q ^ n) * a := by
            refine mul_le_mul_of_nonneg_right ?_ ha.le
            have : q ^ n ≤ ∏ k, p (u₀ k) := by
              rw [← Fin.prod_const n q]
              exact Finset.prod_le_prod₀ (fun _ _ => hq.le) fun k _ => hqle _
            linarith
    exact lt_irrefl _ (hy.trans_le hbound)
  -- hence all the constant codings coincide, and their common value is a common fixed point
  have hconst : ∀ i j : Fin N, coding φ (fun _ => i) = coding φ (fun _ => j) := by
    intro i j
    have hclose : ∀ (n : ℕ) (k : Fin N), ∃ y, |coding φ (fun _ => k) - y| ≤ cmax φ ^ n ∧
        ∀ k' : Fin N, |coding φ (fun _ => k') - y| ≤ cmax φ ^ n := by
      intro n k
      obtain ⟨y, hy⟩ := key n
      have hk : ∀ k' : Fin N, |coding φ (fun _ => k') - y| ≤ cmax φ ^ n := by
        intro k'
        obtain ⟨z, hz, hzy⟩ := hy fun _ => k'
        rw [← hzy]
        exact abs_coding_sub_le hφ _ n hz
      exact ⟨y, hk k, hk⟩
    have hle : ∀ n : ℕ, |coding φ (fun _ => i) - coding φ (fun _ => j)| ≤ 2 * cmax φ ^ n := by
      intro n
      obtain ⟨y, hi, hall⟩ := hclose n i
      have hj := hall j
      calc |coding φ (fun _ => i) - coding φ (fun _ => j)|
          ≤ |coding φ (fun _ => i) - y| + |coding φ (fun _ => j) - y| := by
            simpa only [← Real.dist_eq] using dist_triangle_right _ _ y
        _ ≤ 2 * cmax φ ^ n := by linarith
    have := ge_of_tendsto' ((tendsto_cmax_pow hφ).const_mul 2) hle
    rw [mul_zero] at this
    exact sub_eq_zero.1 (abs_nonpos_iff.1 this)
  refine hφ.no_common_fixed_point ⟨coding φ (fun _ => (⟨0, hN⟩ : Fin N)),
    coding_mem hφ _, fun j => ?_⟩
  have h := coding_eq hφ (fun _ => j)
  rw [show shift (fun _ : ℕ => j) = fun _ => j from rfl] at h
  rw [hconst ⟨0, hN⟩ j]
  exact h.symm

end FractalGeometry.SelfConformal
