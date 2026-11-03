module

public import AnalyticESC.Literature.Rapaport.Analytic.Setup
public import AnalyticESC.Literature.Rapaport.Analytic.PolyBounds

@[expose] public section

/-!
# Entropy of polynomial measures forces entropy of their evaluations

Lemma 3.10 of A. Rapaport, *Dimension of self-conformal measures associated to an exponentially
separated analytic IFS on ℝ*, arXiv:2412.16753v2: if `ν` on `𝒫_k` has entropy
`H(ν, 𝒟_n) ≥ ε n`, then for a positive proportion of levels `i` and components `ν_{p,i}`, the
evaluations `ν_{p,i}.x` have positive entropy at scale `m` for a set of `x` of positive
`θ`-measure, for every `θ` on `I` giving small mass to small balls.

The proof follows Rapaport, with one change in the last step: instead of integrating over the
`(k + 1)`-fold product of `θ`, if the evaluations `ν_{p,i}.x` had small entropy for `θ`-most `x`,
one could choose `k + 1` points `x_0, …, x_k` of `I`, pairwise `δ`-separated, at which all
evaluations have small entropy; since `q ↦ (q(x_0), …, q(x_k))` is bi-Lipschitz on `𝒫_k`, this
contradicts the entropy of `ν_{p,i}`.

## Main declarations

* `SepTuple k δ`: tuples `(x_0, …, x_k)` of points of `I` with `|x_j - x_l| ≥ δ` for `j ≠ l`.
* `exists_norm_le_sum_abs_eval`: `‖q‖ ≤ C ∑_j |q(x_j)|` on separated tuples (compactness).
* `exists_sepTuple_subset`: a set of `θ`-mass `> k c` contains a separated tuple when balls of
  radius `δ` have mass `≤ c`.
* `ent_pi_le`: subadditivity of entropy for finitely many labellings.
* `ent_cellIdxVec_le_sum_actPoint`: `H(ρ, 𝒟_n) ≤ ∑_j H(ρ.x_j, 𝒟_n) + O_{k,δ}(1)`.
* `lemma310`: Lemma 3.10.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.PolyEntropy`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic

open MeasureTheory ProbabilityTheory Set Filter Topology FractalGeometry.SelfConformal
open scoped ENNReal

variable {k : ℕ}

/-! ### Separated tuples and the evaluation map -/

/-- The tuples `(x_0, …, x_k)` of points of `I` with `|x_j - x_l| ≥ δ` for `j ≠ l`. -/
def SepTuple (k : ℕ) (δ : ℝ) : Set (Fin (k + 1) → ℝ) :=
  {x | (∀ j, x j ∈ AnalyticESC.I) ∧ ∀ j l, j ≠ l → δ ≤ |x j - x l|}

/-- The separated tuples form a compact set. -/
theorem isCompact_sepTuple (k : ℕ) (δ : ℝ) : IsCompact (SepTuple k δ) := by
  refine (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset ?_
    fun x hx j _ => hx.1 j
  have h1 : IsClosed {x : Fin (k + 1) → ℝ | ∀ j, x j ∈ AnalyticESC.I} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_Icc.preimage (continuous_apply j)
  have h2 : IsClosed {x : Fin (k + 1) → ℝ | ∀ j l, j ≠ l → δ ≤ |x j - x l|} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_iInter fun l => isClosed_iInter fun _ =>
      isClosed_le continuous_const ((continuous_apply j).sub (continuous_apply l)).abs
  exact h1.inter h2

/-- The evaluation map at a separated tuple is uniformly injective:
`‖q‖ ≤ C ∑_j |q(x_j)|`. -/
theorem exists_norm_le_sum_abs_eval (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ SepTuple k δ, ∀ q : Poly k,
      ‖q‖ ≤ C * ∑ j, |Poly.eval q (x j)| := by
  classical
  set G : (Fin (k + 1) → ℝ) × Poly k → ℝ := fun z => ∑ j, |Poly.eval z.2 (z.1 j)| with hGdef
  have hGc : Continuous G := continuous_finsetSum _ fun j _ =>
    (Poly.continuous_eval_uncurry.comp
      (continuous_snd.prodMk ((continuous_apply j).comp continuous_fst))).abs
  by_cases hE : (SepTuple k δ).Nonempty
  · have hs : IsCompact (SepTuple k δ ×ˢ Metric.sphere (0 : Poly k) 1) :=
      (isCompact_sepTuple k δ).prod (isCompact_sphere _ _)
    have hne : (SepTuple k δ ×ˢ Metric.sphere (0 : Poly k) 1).Nonempty :=
      hE.prod (NormedSpace.sphere_nonempty.2 zero_le_one)
    obtain ⟨z₀, hz₀, hmin⟩ := hs.exists_isMinOn hne hGc.continuousOn
    have hpos : 0 < G z₀ := by
      rcases (Finset.sum_nonneg fun j _ => abs_nonneg _ : 0 ≤ G z₀).lt_or_eq with h | h
      · exact h
      exfalso
      have h0 : ∀ j, Poly.eval z₀.2 (z₀.1 j) = 0 := fun j => by
        have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => abs_nonneg _).1 h.symm j
          (Finset.mem_univ j)
        exact abs_eq_zero.1 this
      have hinj : Function.Injective z₀.1 := fun j l hjl => by
        by_contra hne'
        have := hz₀.1.2 j l hne'
        rw [hjl, sub_self, abs_zero] at this
        linarith
      have hP := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
        (Poly.toPolynomial z₀.2) hinj
        (fun j => by rw [← Poly.eval_eq_eval_toPolynomial]; exact h0 j)
        (by rw [Fintype.card_fin]; exact Nat.lt_succ_of_le (Poly.natDegree_toPolynomial_le _))
      have hz0 : z₀.2 = 0 := by
        rw [← Poly.ofPolynomial_toPolynomial z₀.2, hP]
        ext j
        simp
      have := hz₀.2
      rw [mem_sphere_zero_iff_norm, hz0, norm_zero] at this
      exact zero_ne_one this
    refine ⟨(G z₀)⁻¹, inv_pos.2 hpos, fun x hx q => ?_⟩
    by_cases hq : q = 0
    · rw [hq, norm_zero]
      exact mul_nonneg (inv_pos.2 hpos).le (Finset.sum_nonneg fun j _ => abs_nonneg _)
    have hqn : 0 < ‖q‖ := norm_pos_iff.2 hq
    have h1 := hmin (a := (x, ‖q‖⁻¹ • q)) ⟨hx, by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hqn.ne']⟩
    simp only [Set.mem_ofPred_eq, hGdef, Poly.eval_smul, abs_mul, abs_inv, abs_norm,
      ← Finset.mul_sum] at h1
    rw [inv_mul_eq_div, le_div_iff₀ hqn] at h1
    rw [← div_eq_inv_mul, le_div_iff₀ hpos]
    linarith

  · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hE⟩

/-- A set of mass `> k c` contains `k + 1` points that are pairwise more than `δ` apart, when
closed balls of radius `δ` have mass at most `c`. -/
theorem exists_sepTuple_subset {θ : Measure ℝ} {δ : ℝ} {c : ℝ≥0∞}
    (hball : ∀ x, θ (Metric.closedBall x δ) ≤ c) {A : Set ℝ} (hA : (k : ℝ≥0∞) * c < θ A)
    (hAI : A ⊆ AnalyticESC.I) : ∃ x ∈ SepTuple k δ, ∀ j, x j ∈ A := by
  have key : ∀ s, s ≤ k + 1 → ∃ x : Fin s → ℝ, (∀ j, x j ∈ A) ∧
      ∀ j l, j ≠ l → δ < |x j - x l| := by
    intro s
    induction s with
    | zero => exact fun _ => ⟨Fin.elim0, fun j => j.elim0, fun j => j.elim0⟩
    | succ s ih =>
      intro hs
      obtain ⟨x, hxA, hxsep⟩ := ih (by omega)
      set U := ⋃ j, Metric.closedBall (x j) δ
      have hU : θ U ≤ s * c := by
        calc θ U ≤ ∑ j, θ (Metric.closedBall (x j) δ) := measure_iUnion_fintype_le _ _
          _ ≤ ∑ _j : Fin s, c := Finset.sum_le_sum fun j _ => hball _
          _ = s * c := by simp
      have hne : (A \ U).Nonempty := by
        by_contra hne
        rw [Set.not_nonempty_iff_eq_empty] at hne
        have h1 : θ A ≤ θ (A \ U) + θ U :=
          (measure_mono fun y hy => by
            by_cases hyU : y ∈ U
            · exact Or.inr hyU
            · exact Or.inl ⟨hy, hyU⟩).trans (measure_union_le _ _)
        rw [hne, measure_empty, zero_add] at h1
        have h2 : (s : ℝ≥0∞) * c ≤ k * c := by
          gcongr
          exact_mod_cast (by omega : s ≤ k)
        exact absurd (h1.trans (hU.trans h2)) (not_le.2 hA)
      obtain ⟨y, hyA, hyU⟩ := hne
      refine ⟨Fin.cons y x, fun j => Fin.cases hyA hxA j, fun j l hjl => ?_⟩
      have hfar : ∀ j, δ < |y - x j| := fun j => by
        by_contra h
        exact hyU (Set.mem_iUnion.2 ⟨j, by
          rw [Metric.mem_closedBall, Real.dist_eq]
          exact le_of_not_gt h⟩)
      induction j using Fin.cases with
      | zero =>
        induction l using Fin.cases with
        | zero => exact absurd rfl hjl
        | succ l => simpa using hfar l
      | succ j =>
        induction l using Fin.cases with
        | zero => simpa [abs_sub_comm] using hfar j
        | succ l =>
          simp only [Fin.cons_succ]
          exact hxsep j l fun h => hjl (by rw [h])
  obtain ⟨x, hxA, hxsep⟩ := key (k + 1) le_rfl
  exact ⟨x, ⟨fun j => hAI (hxA j), fun j l hjl => (hxsep j l hjl).le⟩, hxA⟩

/-! ### Subadditivity of entropy -/

section Pi

variable {X : Type*} [MeasurableSpace X] {θ : Measure X}

/-- Finitely many labellings with finite labels have a joint labelling with finite labels. -/
theorem FiniteLabels.pi {n : ℕ} {f : Fin n → X → ℤ} (hf : ∀ j, FiniteLabels θ (f j)) :
    FiniteLabels θ (fun x j => f j x) := by
  refine (Set.Finite.pi (t := fun j => Function.support fun b => θ (f j ⁻¹' {b}))
    fun j => hf j).subset fun v hv j _ => ?_
  simp only [Function.mem_support, ne_eq] at hv ⊢
  exact fun h => hv (measure_mono_null (fun x hx => by
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
    rw [← hx]) h)

/-- Subadditivity of entropy: `H(θ, ⋁_j f_j) ≤ ∑_j H(θ, f_j)`. -/
theorem ent_pi_le [IsProbabilityMeasure θ] : ∀ {n : ℕ} {f : Fin n → X → ℤ},
    (∀ j, Measurable (f j)) → (∀ j, FiniteLabels θ (f j)) →
    ent θ (fun x j => f j x) ≤ ∑ j, ent θ (f j)
  | 0, f, _, _ => by
    rw [ent_eq_zero_of_ae_eq (measurable_pi_iff.2 fun j => j.elim0) (fun j => j.elim0)
      (Filter.Eventually.of_forall fun x => funext fun j => j.elim0)]
    simp
  | n + 1, f, hm, hfin => by
    have he : ent θ (fun x j => f j x) =
        ent θ (fun x => (f 0 x, fun j : Fin n => f j.succ x)) := by
      refine ent_eq_of_injective (φ := fun a : ℤ × (Fin n → ℤ) => (Fin.cons a.1 a.2 :
        Fin (n + 1) → ℤ)) (fun a b hab => ?_) ?_
      · obtain ⟨h1, h2⟩ := Fin.cons_injective2 hab
        exact Prod.ext h1 h2
      · funext x
        simp only [Function.comp_apply]
        funext j
        induction j using Fin.cases with
        | zero => rfl
        | succ j => rfl
    rw [he, Fin.sum_univ_succ]
    have hrest : Measurable fun x => fun j : Fin n => f j.succ x :=
      measurable_pi_iff.2 fun j => hm j.succ
    refine (ent_pair_le (hm 0) hrest (hfin 0) (FiniteLabels.pi fun j => hfin j.succ)).trans ?_
    have := ent_pi_le (f := fun j : Fin n => f j.succ) (fun j => hm j.succ) fun j => hfin j.succ
    linarith

end Pi

/-! ### Entropy of a component through its evaluations -/

/-- For a separated tuple `x`, `H(ρ, 𝒟_n) ≤ ∑_j H(ρ.x_j, 𝒟_n) + (k + 1) log (2 (k + 1) C + 2)`
(in nats), where `C` is the constant of `exists_norm_le_sum_abs_eval`. -/
theorem ent_cellIdxVec_le_sum_actPoint {ρ : Measure (Poly k)} [IsProbabilityMeasure ρ] {B : ℝ}
    (hρ : ∀ᵐ q ∂ρ, ‖q‖ ≤ B) {δ C : ℝ} (hC0 : 0 < C)
    (hC : ∀ x ∈ SepTuple k δ, ∀ q : Poly k, ‖q‖ ≤ C * ∑ j, |Poly.eval q (x j)|)
    {x : Fin (k + 1) → ℝ} (hx : x ∈ SepTuple k δ) (n : ℕ) :
    ent ρ (cellIdxVec n) ≤ ∑ j, ent (actPoint ρ (x j)) (cellIdx n) +
      (k + 1) * Real.log (2 * ((k + 1) * C) + 2) := by
  classical
  have hev : ∀ j, Measurable fun q : Poly k => cellIdx n (Poly.eval q (x j)) := fun j =>
    (measurable_cellIdx n).comp (Poly.measurable_eval_left _)
  have hfev : ∀ j, FiniteLabels ρ fun q : Poly k => cellIdx n (Poly.eval q (x j)) := fun j =>
    finiteLabels_cellIdx_comp (F := fun q => Poly.eval q (x j)) (a := -((k + 1) * |B|))
      (b := (k + 1) * |B|) n (by
        filter_upwards [hρ] with q hq
        exact abs_le.1 (abs_eval_le q (fun l => (abs_apply_le_norm q l).trans
          (hq.trans (le_abs_self B))) (abs_le_one_of_mem_I (hx.1 j))))
  have h1 := ent_cellIdxVec_comp_le (θ := ρ) (F := id)
    (g := fun q j => cellIdx n (Poly.eval q (x j))) measurable_id (measurable_pi_iff.2 hev) n
    (finiteLabels_cellIdxVec_comp_of_norm_le n hρ) (FiniteLabels.pi hfev) MeasurableSet.univ
    (by simp) (r := (k + 1) * C / 2 ^ n) (by positivity) fun q _ q' _ hqq l => by
      have hj : ∀ j, |Poly.eval (q - q') (x j)| ≤ 1 / 2 ^ n := fun j => by
        rw [Poly.eval_sub]
        exact (abs_sub_lt_of_cellIdx_eq (congrFun hqq j)).le
      have h2 := hC x hx (q - q')
      have h3 : ∑ j, |Poly.eval (q - q') (x j)| ≤ (k + 1) * (1 / 2 ^ n) := by
        calc ∑ j, |Poly.eval (q - q') (x j)| ≤ ∑ _j : Fin (k + 1), 1 / 2 ^ n :=
              Finset.sum_le_sum fun j _ => hj j
          _ = (k + 1) * (1 / 2 ^ n) := by simp
      have h4 := abs_apply_le_norm (q - q') l
      simp only [id]
      calc |q l - q' l| = |(q - q') l| := by simp
        _ ≤ ‖q - q'‖ := h4
        _ ≤ C * ((k + 1) * (1 / 2 ^ n)) := h2.trans (mul_le_mul_of_nonneg_left h3 hC0.le)
        _ = (k + 1) * C / 2 ^ n := by ring
  have he : (2 : ℝ) ^ n * (2 * ((k + 1) * C / 2 ^ n)) + 2 = 2 * ((k + 1) * C) + 2 := by
    field_simp
  rw [he] at h1
  have h2 := ent_pi_le (θ := ρ) hev hfev
  have h3 : ∀ j, ent ρ (fun q : Poly k => cellIdx n (Poly.eval q (x j))) =
      ent (actPoint ρ (x j)) (cellIdx n) := fun j =>
    (ent_map (Poly.measurable_eval_left _) (measurable_cellIdx n)).symm
  simp_rw [h3] at h2
  exact h1.trans (by linarith)

/-! ### Lemma 3.10 -/

/-- Normalised dyadic entropies on `𝒫_k` are nonnegative. -/
theorem dyadicEntropyVec_nonneg_aux (ρ : Measure (Poly k)) [IsZeroOrProbabilityMeasure ρ]
    (n m : ℕ) : 0 ≤ dyadicEntropyVec ρ n / m := by
  rw [dyadicEntropyVec_eq_ent]
  exact div_nonneg (div_nonneg (ent_nonneg _) (Real.log_nonneg (by norm_num)))
    (Nat.cast_nonneg m)

/-- Step 1 of the proof of Lemma 3.10: by Hochman's Lemma 3.4, the components of `ν` have
average entropy at least `ε n / 2` over the levels `i < n`, for `n` large. -/
theorem sum_cavg_dyadicEntropyVec_ge {ν : Measure (Poly k)} [IsProbabilityMeasure ν] {R ε : ℝ}
    (hR : 0 < R) (hνR : ∀ᵐ q ∂ν, ‖q‖ ≤ R) {n m : ℕ} (hm : 1 ≤ m)
    (hνent : ε ≤ dyadicEntropyVec ν n / n)
    (hN : 2 * ((k + 1) * Real.log (2 * R + 2) + m * ((k + 1) * Real.log 6)) ≤
      n * (ε * Real.log 2)) :
    ε * n / 2 ≤ ∑ i ∈ Finset.range n,
      cavg ν (cellIdxVec i) (fun ρ => dyadicEntropyVec ρ (i + m) / m) := by
  have hl2 := Real.log_pos one_lt_two
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  set B₀ : ℝ := (k + 1) * Real.log (2 * R + 2) with hB₀
  have hB₀0 : 0 ≤ B₀ := mul_nonneg hk1.le (Real.log_nonneg (by linarith))
  have hl6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hn0 : (0 : ℝ) < n := by
    by_contra h
    have : (n : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg n)
    rw [this, zero_mul] at hN
    have : 0 < 2 * (B₀ + m * ((k + 1) * Real.log 6)) := by
      have : 0 < Real.log (2 * R + 2) := Real.log_pos (by linarith)
      positivity
    linarith
  have hνbox : ∀ᵐ q ∂ν, ∀ j, q j ∈ Icc (-R) R := by
    filter_upwards [hνR] with q hq j
    exact abs_le.1 ((abs_apply_le_norm q j).trans hq)
  have hfν : ∀ i, FiniteLabels ν (cellIdxVec i) := fun i =>
    finiteLabels_cellIdxVec_comp_of_norm_le (F := id) i hνR
  have hms := abs_sum_cavg_cellIdxVec_sub_le (θ := ν) (F := id) measurable_id
    (a := fun _ => -R) (b := fun _ => R) hνbox n m
  simp only [Function.comp_id] at hms
  rw [abs_le] at hms
  have h0 : ent ν (cellIdxVec 0) ≤ B₀ := by
    have := ent_cellIdxVec_comp_le_log (θ := ν) (F := id) measurable_id
      (a := fun _ => -R) (ℓ := 2 * R) (by positivity) 0 (by
        filter_upwards [hνbox] with q hq j
        have h2 := (hq j).2
        exact ⟨(hq j).1, show q j ≤ -R + 2 * R by linarith⟩)
    simpa using this
  have hνn : Real.log 2 * (ε * n) ≤ ent ν (cellIdxVec n) := by
    have hn' : ent ν (cellIdxVec n) = Real.log 2 * dyadicEntropyVec ν n := by
      rw [dyadicEntropyVec_eq_ent]
      field_simp
    rw [hn']
    rw [le_div_iff₀ hn0] at hνent
    exact mul_le_mul_of_nonneg_left hνent hl2.le
  have hFcavg : ∀ i, cavg ν (cellIdxVec i) (fun ρ => dyadicEntropyVec ρ (i + m) / m) *
      (m * Real.log 2) = cavg ν (cellIdxVec i) (fun ρ => ent ρ (cellIdxVec (i + m))) := by
    intro i
    rw [mul_comm, ← cavg_const_mul (hfν i)]
    congr 1
    funext ρ
    rw [dyadicEntropyVec_eq_ent]
    field_simp
  have hs : (∑ i ∈ Finset.range n, cavg ν (cellIdxVec i)
      (fun ρ => dyadicEntropyVec ρ (i + m) / m)) * (m * Real.log 2) =
      ∑ i ∈ Finset.range n, cavg ν (cellIdxVec i) (fun ρ => ent ρ (cellIdxVec (i + m))) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => hFcavg i
  have hA : (m : ℝ) * (Real.log 2 * (ε * n)) ≤ m * ent ν (cellIdxVec n) :=
    mul_le_mul_of_nonneg_left hνn hm0.le
  have hB : (m : ℝ) * ent ν (cellIdxVec 0) ≤ m * B₀ := mul_le_mul_of_nonneg_left h0 hm0.le
  have hN' : (m : ℝ) * (2 * (B₀ + m * ((k + 1) * Real.log 6))) ≤
      m * (n * (ε * Real.log 2)) := mul_le_mul_of_nonneg_left hN hm0.le
  have e1 : (m : ℝ) * (ent ν (cellIdxVec n) - ent ν (cellIdxVec 0)) =
      m * ent ν (cellIdxVec n) - m * ent ν (cellIdxVec 0) := by ring
  have e2 : (m : ℝ) * (2 * (B₀ + m * ((k + 1) * Real.log 6))) =
      2 * (m * B₀) + 2 * (m * m * ((k + 1) * Real.log 6)) := by ring
  have e3 : (m : ℝ) * (n * (ε * Real.log 2)) = 2 * (ε * n / 2 * (m * Real.log 2)) := by ring
  have e4 : (m : ℝ) * (Real.log 2 * (ε * n)) = 2 * (ε * n / 2 * (m * Real.log 2)) := by ring
  rw [e1] at hms
  rw [e2, e3] at hN'
  rw [e4] at hA
  have key : ε * n / 2 * (m * Real.log 2) ≤ (∑ i ∈ Finset.range n, cavg ν (cellIdxVec i)
      (fun ρ => dyadicEntropyVec ρ (i + m) / m)) * (m * Real.log 2) := by
    rw [hs]
    linarith [hms.1]
  exact le_of_mul_le_mul_right key (by positivity)

/-- The components of `ν` at level `i` have entropy at most `2 (k + 1) m` bits at level
`i + m`. -/
theorem dyadicEntropyVec_comp_le {ν : Measure (Poly k)} [IsFiniteMeasure ν] {i m : ℕ}
    (hm : 1 ≤ m) {c : Fin (k + 1) → ℤ} (hc : ν (cellIdxVec i ⁻¹' {c}) ≠ 0) :
    dyadicEntropyVec (comp ν (cellIdxVec i) c) (i + m) / m ≤ 2 * (k + 1) := by
  have := comp_isProbabilityMeasure hc
  have hl2 := Real.log_pos one_lt_two
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hbox : ∀ᵐ q ∂(comp ν (cellIdxVec i) c), ∀ j,
      q j ∈ Icc ((c j : ℝ) / 2 ^ i) ((c j : ℝ) / 2 ^ i + 1 / 2 ^ i) := by
    filter_upwards [ae_comp_mem (measurable_cellIdxVec i) c] with q hq j
    have h := (mem_cell_iff i (c j) (q j)).2 (congrFun hq j)
    rw [cell, mem_Ico] at h
    exact ⟨h.1, h.2.le.trans (le_of_eq (by ring))⟩
  have h1 := ent_cellIdxVec_comp_le_log (θ := comp ν (cellIdxVec i) c) (F := id)
    measurable_id (ℓ := 1 / 2 ^ i) (by positivity) (i + m) hbox
  have he : (2 : ℝ) ^ (i + m) * (1 / 2 ^ i) + 2 = 2 ^ m + 2 := by
    rw [pow_add]
    field_simp
  rw [he] at h1
  have h2 : Real.log (2 ^ m + 2) ≤ 2 * m * Real.log 2 := by
    have h3 : (2 : ℝ) ^ m + 2 ≤ 2 ^ (2 * m) := by
      have h4 : (2 : ℝ) ≤ 2 ^ m := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
      calc (2 : ℝ) ^ m + 2 ≤ 2 ^ m + 2 ^ m := by linarith
        _ = 2 * 2 ^ m := by ring
        _ ≤ 2 ^ m * 2 ^ m := by nlinarith
        _ = 2 ^ (2 * m) := by rw [← pow_add]; ring_nf
    calc Real.log (2 ^ m + 2) ≤ Real.log (2 ^ (2 * m)) := Real.log_le_log (by positivity) h3
      _ = 2 * m * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
  simp only [Function.comp_id] at h1
  rw [dyadicEntropyVec_eq_ent, div_div, div_le_iff₀ (by positivity)]
  have hk : (0 : ℝ) ≤ k + 1 := by positivity
  calc ent (comp ν (cellIdxVec i) c) (cellIdxVec (i + m)) ≤ (k + 1) * Real.log (2 ^ m + 2) := h1
    _ ≤ (k + 1) * (2 * m * Real.log 2) := mul_le_mul_of_nonneg_left h2 hk
    _ = 2 * (k + 1) * (Real.log 2 * m) := by ring

/-- Step 3 of the proof of Lemma 3.10: if a measure `ρ` on `𝒫_k` has entropy `> ε m / 4` bits
at level `i + m`, then its evaluations `ρ.x` have entropy `> ε₀ m` for a set of `x` of
`θ`-mass at least `1/2`. -/
theorem half_le_measureReal_of_entropy {ρ : Measure (Poly k)} [IsProbabilityMeasure ρ]
    {R : ℝ} (hρR : ∀ᵐ q ∂ρ, ‖q‖ ≤ R) {θ : Measure ℝ} [IsProbabilityMeasure θ]
    (hθI : θ AnalyticESC.Iᶜ = 0) {δ C ε ε₀ : ℝ} (hC0 : 0 < C)
    (hC : ∀ x ∈ SepTuple k δ, ∀ q : Poly k, ‖q‖ ≤ C * ∑ j, |Poly.eval q (x j)|)
    (hball : ∀ x, θ.real (Metric.closedBall x δ) ≤ 1 / (2 * (k + 1))) {i m : ℕ} (hm : 1 ≤ m)
    (hcδ : (k + 1) * Real.log (2 * ((k + 1) * C) + 2) ≤ ε / 8 * (m * Real.log 2))
    (hε₀ : (k + 1) * ε₀ = ε / 32)
    (hF : ε / 4 < dyadicEntropyVec ρ (i + m) / m) :
    1 / 2 ≤ θ.real {x | ε₀ < dyadicEntropy (actPoint ρ x) (i + m) / m} := by
  have hl2 := Real.log_pos one_lt_two
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  set G := {x | ε₀ < dyadicEntropy (actPoint ρ x) (i + m) / m}
  by_contra hG
  rw [not_le] at hG
  have hA : (1 : ℝ) / 2 < θ.real (Gᶜ ∩ AnalyticESC.I) := by
    have h1 : θ univ ≤ θ G + θ (Gᶜ ∩ AnalyticESC.I) + θ AnalyticESC.Iᶜ := by
      refine (measure_mono fun y _ => ?_).trans ((measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) le_rfl))
      by_cases hyG : y ∈ G
      · exact Or.inl (Or.inl hyG)
      · by_cases hyI : y ∈ AnalyticESC.I
        · exact Or.inl (Or.inr ⟨hyG, hyI⟩)
        · exact Or.inr hyI
    rw [hθI, add_zero, measure_univ] at h1
    have h2 := ENNReal.toReal_mono (by finiteness) h1
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_one] at h2
    simp only [measureReal_def] at hG ⊢
    linarith
  have hballE : ∀ x, θ (Metric.closedBall x δ) ≤ ENNReal.ofReal (1 / (2 * (k + 1))) := by
    intro x
    rw [← ENNReal.ofReal_toReal (measure_ne_top θ _)]
    exact ENNReal.ofReal_le_ofReal (hball x)
  have hkc : (k : ℝ≥0∞) * ENNReal.ofReal (1 / (2 * (k + 1))) < θ (Gᶜ ∩ AnalyticESC.I) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg k),
      ← ENNReal.ofReal_toReal (measure_ne_top θ (Gᶜ ∩ AnalyticESC.I))]
    refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 ?_
    have : (k : ℝ) * (1 / (2 * (k + 1))) < 1 / 2 := by
      rw [mul_one_div, div_lt_iff₀ (by positivity)]
      linarith
    exact this.trans hA
  obtain ⟨x, hx, hxA⟩ := exists_sepTuple_subset hballE hkc Set.inter_subset_right
  have hent := ent_cellIdxVec_le_sum_actPoint hρR hC0 hC hx (i + m)
  have hsum : ∑ j, ent (actPoint ρ (x j)) (cellIdx (i + m)) ≤
      (k + 1) * (ε₀ * (m * Real.log 2)) := by
    calc ∑ j, ent (actPoint ρ (x j)) (cellIdx (i + m))
        ≤ ∑ _j : Fin (k + 1), ε₀ * (m * Real.log 2) := Finset.sum_le_sum fun j _ => by
          have h := (hxA j).1
          simp only [G, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at h
          rw [dyadicEntropy_eq_ent, div_div, div_le_iff₀ (by positivity)] at h
          linarith
      _ = (k + 1) * (ε₀ * (m * Real.log 2)) := by simp
  have h3 : (k + 1) * (ε₀ * (m * Real.log 2)) = ε / 32 * (m * Real.log 2) := by
    rw [← mul_assoc, hε₀]
  have hFρ : dyadicEntropyVec ρ (i + m) / m * (m * Real.log 2) =
      ent ρ (cellIdxVec (i + m)) := by
    rw [dyadicEntropyVec_eq_ent]
    field_simp
  have h4 : dyadicEntropyVec ρ (i + m) / m * (m * Real.log 2) ≤
      (ε / 32 + ε / 8) * (m * Real.log 2) := by
    rw [hFρ, add_mul]
    linarith
  have h5 := le_of_mul_le_mul_right h4 (by positivity)
  have h6 : 0 < ε := by
    have := (dyadicEntropyVec_nonneg_aux ρ (i + m) m)
    linarith
  linarith

/-- Lemma 3.10 of Rapaport, for every measure `θ` on `I` with `θ(B(x, δ)) ≤ 1 / (2 (k + 1))`. -/
theorem lemma310 (k : ℕ) {ε : ℝ} (hε : 0 < ε) : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ δ : ℝ, 0 < δ →
    ∃ M : ℕ, ∀ m ≥ M, ∃ N₂ : ℕ, ∀ n ≥ N₂, ∀ ν : Measure (Poly k), IsProbabilityMeasure ν →
    (∀ᵐ q ∂ν, ‖q‖ ≤ ε⁻¹) → ε ≤ dyadicEntropyVec ν n / n → ∀ θ : Measure ℝ,
    IsProbabilityMeasure θ → θ AnalyticESC.Iᶜ = 0 →
    (∀ x, θ.real (Metric.closedBall x δ) ≤ 1 / (2 * (k + 1))) →
    ε₀ * n < ∑ i ∈ Finset.range n, cavg ν (cellIdxVec i)
      (fun ρ => θ.real {x | ε₀ < dyadicEntropy (actPoint ρ x) (i + m) / m}) := by
  classical
  have hl2 := Real.log_pos one_lt_two
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  set ε' : ℝ := min ε 1 with hε'def
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  refine ⟨ε' / (32 * (k + 1)), by positivity, fun δ hδ => ?_⟩
  set ε₀ := ε' / (32 * (k + 1)) with hε₀def
  have hε₀k : (k + 1) * ε₀ = ε' / 32 := by
    rw [hε₀def]
    field_simp
  obtain ⟨C, hC0, hC⟩ := exists_norm_le_sum_abs_eval k hδ
  set cδ : ℝ := (k + 1) * Real.log (2 * ((k + 1) * C) + 2) with hcδ
  have hcδ0 : 0 ≤ cδ := mul_nonneg hk1.le (Real.log_nonneg (by nlinarith))
  obtain ⟨M, hM⟩ := exists_nat_ge (8 * cδ / (ε' * Real.log 2) + 1)
  refine ⟨M, fun m hmM => ?_⟩
  have hMm : (M : ℝ) ≤ m := by exact_mod_cast hmM
  have hX0 : 0 ≤ 8 * cδ / (ε' * Real.log 2) := by positivity
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmcδ : cδ ≤ ε' / 8 * (m * Real.log 2) := by
    have h1 : 8 * cδ / (ε' * Real.log 2) ≤ m := by linarith
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  set B : ℝ := 2 * ((k + 1) * Real.log (2 * ε⁻¹ + 2) + m * ((k + 1) * Real.log 6)) with hB
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (B / (ε' * Real.log 2))
  refine ⟨N₂, fun n hn ν hν hνR hνent θ hθ hθI hball => ?_⟩
  have hN₂n : (N₂ : ℝ) ≤ n := by exact_mod_cast hn
  have hNB : B ≤ n * (ε' * Real.log 2) := by
    have h1 : B / (ε' * Real.log 2) ≤ n := hN₂.trans hN₂n
    rwa [div_le_iff₀ (by positivity)] at h1
  have hn0 : (0 : ℝ) < n := by
    have hB0 : 0 < B := by
      have : 0 < Real.log (2 * ε⁻¹ + 2) := Real.log_pos (by
        have : 0 < 2 * ε⁻¹ := by positivity
        linarith)
      have : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
      positivity
    by_contra h
    have : (n : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg n)
    rw [this, zero_mul] at hNB
    linarith
  have hνent' : ε' ≤ dyadicEntropyVec ν n / n := hε'ε.trans hνent
  have hfν : ∀ i, FiniteLabels ν (cellIdxVec i) := fun i =>
    finiteLabels_cellIdxVec_comp_of_norm_le (F := id) i hνR
  -- Step 1: the average entropy of the components
  have hsumF := sum_cavg_dyadicEntropyVec_ge (inv_pos.2 hε) hνR hm1 hνent' hNB
  -- Step 2 and 3, at each level
  have hlt : ε' / 4 < 2 * (k + 1) := by linarith
  have hlev : ∀ i ∈ Finset.range n,
      (cavg ν (cellIdxVec i) (fun ρ => dyadicEntropyVec ρ (i + m) / m) - ε' / 4) /
        (2 * (k + 1) - ε' / 4) / 2 ≤ cavg ν (cellIdxVec i)
          (fun ρ => θ.real {x | ε₀ < dyadicEntropy (actPoint ρ x) (i + m) / m}) := by
    intro i _
    have hmk := cavg_indicator_ge (measurable_cellIdxVec i) (hfν i) hlt
      (F := fun ρ => dyadicEntropyVec ρ (i + m) / m)
      (fun c hc => dyadicEntropyVec_comp_le hm1 hc)
    have hmono := cavg_mono (hfν i)
      (F := fun ρ => (1 / 2) * (if ε' / 4 < dyadicEntropyVec ρ (i + m) / m then 1 else 0))
      (G := fun ρ => θ.real {x | ε₀ < dyadicEntropy (actPoint ρ x) (i + m) / m})
      fun c hc => by
        have := comp_isProbabilityMeasure hc
        by_cases h : ε' / 4 < dyadicEntropyVec (comp ν (cellIdxVec i) c) (i + m) / m
        · simp only [h, ↓reduceIte, mul_one]
          exact half_le_measureReal_of_entropy (ρ := comp ν (cellIdxVec i) c)
            ((cond_absolutelyContinuous (μ := ν)).ae_le hνR) hθI hC0 hC hball hm1 hmcδ hε₀k h
        · simp only [h, ↓reduceIte, mul_zero]
          exact measureReal_nonneg
    rw [cavg_const_mul (hfν i)] at hmono
    linarith
  have hsum := Finset.sum_le_sum hlev
  have hD : 0 < 2 * ((k : ℝ) + 1) - ε' / 4 := by linarith
  have he : ∑ i ∈ Finset.range n,
      (cavg ν (cellIdxVec i) (fun ρ => dyadicEntropyVec ρ (i + m) / m) - ε' / 4) /
        (2 * (k + 1) - ε' / 4) / 2 =
      (∑ i ∈ Finset.range n, cavg ν (cellIdxVec i) (fun ρ => dyadicEntropyVec ρ (i + m) / m) -
        n * (ε' / 4)) / (2 * (k + 1) - ε' / 4) / 2 := by
    rw [← Finset.sum_div, ← Finset.sum_div, Finset.sum_sub_distrib]
    simp
  rw [he] at hsum
  refine lt_of_lt_of_le ?_ hsum
  rw [div_div, lt_div_iff₀ (by positivity)]
  have h2 : ε₀ * n * ((2 * (k + 1) - ε' / 4) * 2) ≤ ε₀ * n * (4 * (k + 1)) := by
    have : (2 * ((k : ℝ) + 1) - ε' / 4) * 2 ≤ 4 * (k + 1) := by linarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have h3 : ε₀ * n * (4 * (k + 1)) = ε' * n / 8 := by
    rw [hε₀def]
    field_simp
    ring
  have h4 : ε' * n / 8 < ε' * n / 4 := by
    have : 0 < ε' * n := by positivity
    linarith
  linarith

end FractalGeometry.Rapaport.Analytic
