module

public import AnalyticESC.Literature.SelfConformal.Vocabulary

@[expose] public section

/-!
# The one-sided Bernoulli shift

Basic properties of the Bernoulli measure `β = p^ℕ` on `Σ = (Fin N)^ℕ` of the shared vocabulary,
as used in Section 2.6 of A. Rapaport, *Dimension of self-conformal measures associated to an
exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2.

## Main declarations

* `shift`: the left shift `σ ω = (ω_{k+1})_k`; `measurable_shift`, `continuous_shift`.
* `prepend`: the sequence `i ω = (i, ω_0, ω_1, …)`, with `shift_prepend`, `prepend_zero_shift`.
* `measurableSet_cylinder`, `isClopen_cylinder`, `iUnion_cylinder`, `disjoint_cylinder`,
  `mem_cylinder_self`, `mem_cylinder_iff_word`.
* `bernoulli_cylinder`, `measureReal_bernoulli_cylinder`: `β[u] = ∏ k, p (u k)`.
* `measurePreserving_shift`: `σ` preserves `β`.
* `indepFun_zero_shift`, `map_zero_shift_bernoulli`: the first letter and the tail are independent,
  and the law of `ω ↦ (ω 0, σ ω)` is `(step p).prod β`; `map_prepend_bernoulli`.
* `bernoulli_inter_shift`, `bernoulli_cylinder_inter_shift_iterate`:
  `β([u] ∩ σ^{-n} S) = β[u] β(S)` for `u` of length `n` and measurable `S`.
* `ergodic_shift`: the one-sided Bernoulli shift is ergodic (Kolmogorov's zero-one law).

Copied from the library `FractalGeometry` (module `FractalGeometry.SelfConformal.Bernoulli`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.SelfConformal

open MeasureTheory ProbabilityTheory Set Filter Topology

variable {N : ℕ}

/-! ### The shift and prepending a letter -/

/-- The left shift `σ ω = (ω_{k+1})_k` on `(Fin N)^ℕ`. -/
def shift (ω : ℕ → Fin N) : ℕ → Fin N := fun k => ω (k + 1)

@[simp] theorem shift_apply (ω : ℕ → Fin N) (k : ℕ) : shift ω k = ω (k + 1) := rfl

/-- `(σ^n ω)_k = ω_{k+n}`. -/
theorem shift_iterate_apply (n : ℕ) (ω : ℕ → Fin N) (k : ℕ) :
    (shift^[n] ω) k = ω (k + n) := by
  induction n generalizing ω with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih]; rfl

/-- The shift is measurable. -/
theorem measurable_shift : Measurable (shift : (ℕ → Fin N) → ℕ → Fin N) :=
  Measurable.of_eval fun k => measurable_pi_apply (k + 1)

/-- The shift is continuous. -/
theorem continuous_shift : Continuous (shift : (ℕ → Fin N) → ℕ → Fin N) :=
  continuous_pi fun k => continuous_apply (k + 1)

/-- The sequence `i ω = (i, ω_0, ω_1, …)`. -/
def prepend (i : Fin N) (ω : ℕ → Fin N) : ℕ → Fin N
  | 0 => i
  | k + 1 => ω k

@[simp] theorem prepend_zero (i : Fin N) (ω : ℕ → Fin N) : prepend i ω 0 = i := rfl

@[simp] theorem prepend_succ (i : Fin N) (ω : ℕ → Fin N) (k : ℕ) :
    prepend i ω (k + 1) = ω k := rfl

/-- `σ (i ω) = ω`. -/
@[simp] theorem shift_prepend (i : Fin N) (ω : ℕ → Fin N) : shift (prepend i ω) = ω := rfl

/-- `ω = ω_0 (σ ω)`. -/
@[simp] theorem prepend_zero_shift (ω : ℕ → Fin N) : prepend (ω 0) (shift ω) = ω := by
  funext k
  cases k <;> rfl

/-- Prepending a letter is measurable in both arguments. -/
theorem measurable_prepend :
    Measurable fun q : Fin N × (ℕ → Fin N) => prepend q.1 q.2 := by
  refine Measurable.of_eval fun k => ?_
  cases k with
  | zero => exact measurable_fst
  | succ k => exact (measurable_pi_apply k).comp measurable_snd

/-- Prepending a letter is continuous in both arguments. -/
theorem continuous_prepend :
    Continuous fun q : Fin N × (ℕ → Fin N) => prepend q.1 q.2 := by
  refine continuous_pi fun k => ?_
  cases k with
  | zero => exact continuous_fst
  | succ k => exact (continuous_apply k).comp continuous_snd

/-! ### Cylinders -/

/-- A cylinder is a finite intersection of coordinate conditions. -/
theorem cylinder_eq_iInter {n : ℕ} (u : Fin n → Fin N) :
    cylinder u = ⋂ k : Fin n, (fun ω : ℕ → Fin N => ω k) ⁻¹' {u k} := by
  ext ω
  simp [cylinder]

/-- Cylinders are measurable. -/
theorem measurableSet_cylinder {n : ℕ} (u : Fin n → Fin N) : MeasurableSet (cylinder u) := by
  rw [cylinder_eq_iInter]
  exact MeasurableSet.iInter fun k => measurable_pi_apply _ (measurableSet_singleton _)

/-- Cylinders are clopen. -/
theorem isClopen_cylinder {n : ℕ} (u : Fin n → Fin N) : IsClopen (cylinder u) := by
  rw [cylinder_eq_iInter]
  exact isClopen_iInter_of_finite fun k => (isClopen_discrete _).preimage (continuous_apply _)

/-- `ω ∈ [ω|_n]`. -/
theorem mem_cylinder_self (ω : ℕ → Fin N) (n : ℕ) : ω ∈ cylinder (fun k : Fin n => ω k) :=
  fun _ => rfl

/-- `ω ∈ [u]` if and only if `ω|_n = u` as words. -/
theorem mem_cylinder_iff_word {n : ℕ} (u : Fin n → Fin N) (ω : ℕ → Fin N) :
    ω ∈ cylinder u ↔ word ω n = List.ofFn u := by
  rw [word, List.ofFn_inj]
  exact ⟨fun h => funext h, fun h k => congrFun h k⟩

/-- The cylinders of length `n` cover the space. -/
theorem iUnion_cylinder (n : ℕ) : ⋃ u : Fin n → Fin N, cylinder u = univ :=
  eq_univ_of_forall fun ω => mem_iUnion.2 ⟨_, mem_cylinder_self ω n⟩

/-- Distinct cylinders of the same length are disjoint. -/
theorem disjoint_cylinder {n : ℕ} {u v : Fin n → Fin N} (h : u ≠ v) :
    Disjoint (cylinder u) (cylinder v) := by
  refine Set.disjoint_left.2 fun ω hu hv => h (funext fun k => ?_)
  rw [← hu k, ← hv k]

/-- The cylinders of length `n` are pairwise disjoint. -/
theorem pairwiseDisjoint_cylinder (n : ℕ) :
    Pairwise (Function.onFun Disjoint fun u : Fin n → Fin N => cylinder u) :=
  fun _ _ h => disjoint_cylinder h

/-- `[i u] = {ω_0 = i} ∩ σ^{-1}[u]`. -/
theorem cylinder_succ {n : ℕ} (u : Fin (n + 1) → Fin N) :
    cylinder u = {ω | ω 0 = u 0} ∩ shift ⁻¹' cylinder (Fin.tail u) := by
  ext ω
  simp only [cylinder, mem_ofPred_eq, mem_inter_iff, mem_preimage, Fin.tail]
  constructor
  · intro h
    exact ⟨h 0, fun k => h k.succ⟩
  · rintro ⟨h0, h⟩ k
    cases k using Fin.cases with
    | zero => exact h0
    | succ k => exact h k

/-! ### The one-step law and the Bernoulli measure of cylinders -/

/-- `p` is a probability vector on a nonempty alphabet. -/
theorem pos_of_isProbVec {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with rfl | h
  · have := hp.2
    simp at this
  · exact h

/-- A probability vector forces a nonempty alphabet. -/
theorem neZero_of_isProbVec {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p) : NeZero N :=
  ⟨(pos_of_isProbVec hp).ne'⟩

/-- `step p {i} = p_i`. -/
theorem step_singleton (p : Fin N → ℝ) (i : Fin N) : step p {i} = ENNReal.ofReal (p i) := by
  simp [step, Measure.dirac_apply', Set.indicator_apply]

/-- The law of the first coordinate under `β` is `step p`. -/
theorem map_eval_bernoulli {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p) (k : ℕ) :
    (bernoulli p hp).map (fun ω => ω k) = step p := by
  have := isProbabilityMeasure_step hp
  exact Measure.infinitePi_map_eval _ k

/-- The Bernoulli measure of a cylinder: `β[u] = ∏_k p_{u_k}`. -/
theorem bernoulli_cylinder {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p) {n : ℕ}
    (u : Fin n → Fin N) :
    bernoulli p hp (cylinder u) = ∏ k, ENNReal.ofReal (p (u k)) := by
  have := isProbabilityMeasure_step hp
  have h : cylinder u =
      (Finset.range n : Set ℕ).pi (fun k => if h : k < n then {u ⟨k, h⟩} else univ) := by
    ext ω
    simp only [cylinder, mem_ofPred_eq, Set.mem_pi, Finset.coe_range, mem_Iio]
    constructor
    · intro hω k hk
      simpa [hk] using hω ⟨k, hk⟩
    · intro hω k
      simpa [k.2] using hω k k.2
  rw [h, bernoulli, Measure.infinitePi_pi]
  · rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [k.2, dite_true, step_singleton]
  · intro k _
    split_ifs
    · exact measurableSet_singleton _
    · exact MeasurableSet.univ

/-- The Bernoulli measure of a cylinder, as a real number. -/
theorem measureReal_bernoulli_cylinder {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p) {n : ℕ}
    (u : Fin n → Fin N) :
    (bernoulli p hp).real (cylinder u) = ∏ k, p (u k) := by
  rw [measureReal_def, bernoulli_cylinder, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl fun k _ => ENNReal.toReal_ofReal (hp.1 _).le

/-! ### Invariance and independence -/

/-- The shift preserves the Bernoulli measure. -/
theorem measurePreserving_shift {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p) :
    MeasurePreserving shift (bernoulli p hp) (bernoulli p hp) := by
  have := isProbabilityMeasure_step hp
  refine ⟨measurable_shift, ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => step p)
    (f := fun k => k + 1) (add_left_injective 1)

/-- The coordinates are independent under `β`. -/
theorem iIndepFun_eval {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p) :
    iIndepFun (fun (k : ℕ) (ω : ℕ → Fin N) => ω k) (bernoulli p hp) := by
  have := isProbabilityMeasure_step hp
  exact iIndepFun_infinitePi (P := fun _ : ℕ => step p) (X := fun _ x => x)
    (fun _ => measurable_id)

/-- `σ^n` is measurable for the `σ`-algebra generated by the coordinates `k ≥ n`. -/
private theorem measurable_shift_iterate_le (n : ℕ) :
    Measurable[⨆ k ∈ Ici n, MeasurableSpace.comap (fun ω : ℕ → Fin N => ω k) inferInstance]
      (shift^[n] : (ℕ → Fin N) → ℕ → Fin N) := by
  refine @Measurable.of_eval (ℕ → Fin N) ℕ (fun _ => Fin N)
    (⨆ k ∈ Ici n, MeasurableSpace.comap (fun ω : ℕ → Fin N => ω k) inferInstance) _ _
    fun k => ?_
  have h : (fun ω : ℕ → Fin N => (shift^[n] ω) k) = fun ω => ω (k + n) :=
    funext fun ω => shift_iterate_apply n ω k
  rw [h]
  refine Measurable.mono (comap_measurable (fun ω : ℕ → Fin N => ω (k + n))) ?_ le_rfl
  exact le_iSup₂_of_le (f := fun k _ =>
    MeasurableSpace.comap (fun ω : ℕ → Fin N => ω k) inferInstance) (k + n)
    (mem_Ici.2 (Nat.le_add_left n k)) le_rfl

/-- The first letter and the tail `σ ω` are independent under `β`. -/
theorem indepFun_zero_shift {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p) :
    IndepFun (fun ω : ℕ → Fin N => ω 0) shift (bernoulli p hp) := by
  rw [IndepFun_iff_Indep]
  have h := indep_iSup_of_disjoint (fun k => (measurable_pi_apply k).comap_le)
    ((iIndepFun_iff_iIndep _ _ _).1 (iIndepFun_eval hp)) (S := {0}) (T := Ici 1)
    (by simp)
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
  · exact le_iSup₂_of_le (f := fun k _ =>
      MeasurableSpace.comap (fun ω : ℕ → Fin N => ω k) inferInstance) 0 (mem_singleton 0) le_rfl
  · simpa using (measurable_shift_iterate_le (N := N) 1).comap_le

/-- The law of `ω ↦ (ω_0, σ ω)` under `β` is `(step p) × β`. -/
theorem map_zero_shift_bernoulli {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p) :
    (bernoulli p hp).map (fun ω => (ω 0, shift ω)) = (step p).prod (bernoulli p hp) := by
  rw [(indepFun_zero_shift hp).map_prod_eq_prod_map_map (measurable_pi_apply 0).aemeasurable
    measurable_shift.aemeasurable, map_eval_bernoulli, (measurePreserving_shift hp).map_eq]

/-- `β` is the image of `(step p) × β` under `(i, ω) ↦ i ω`. -/
theorem map_prepend_bernoulli {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p) :
    ((step p).prod (bernoulli p hp)).map (fun q => prepend q.1 q.2) = bernoulli p hp := by
  rw [← map_zero_shift_bernoulli hp, Measure.map_map measurable_prepend
    ((measurable_pi_apply 0).prodMk measurable_shift :
      Measurable fun ω : ℕ → Fin N => (ω 0, shift ω))]
  have : ((fun q : Fin N × (ℕ → Fin N) => prepend q.1 q.2) ∘ fun ω => (ω 0, shift ω)) = id :=
    funext prepend_zero_shift
  rw [this, Measure.map_id]

/-- `β({ω_0 = i} ∩ σ^{-1} S) = p_i β(S)` for measurable `S`. -/
theorem bernoulli_inter_shift {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p) (i : Fin N)
    {S : Set (ℕ → Fin N)} (hS : MeasurableSet S) :
    bernoulli p hp ({ω | ω 0 = i} ∩ shift ⁻¹' S) = ENNReal.ofReal (p i) * bernoulli p hp S := by
  have h := (indepFun_zero_shift hp).measure_inter_preimage_eq_mul {i} S
    (measurableSet_singleton i) hS
  have h0 : bernoulli p hp ((fun ω : ℕ → Fin N => ω 0) ⁻¹' {i}) = ENNReal.ofReal (p i) := by
    rw [← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton i),
      map_eval_bernoulli, step_singleton]
  rw [← (measurePreserving_shift hp).measure_preimage hS.nullMeasurableSet, ← h0, ← h]
  rfl

/-- `β([u] ∩ σ^{-n} S) = β[u] β(S)` for a word `u` of length `n` and measurable `S`. -/
theorem bernoulli_cylinder_inter_shift_iterate {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p)
    {n : ℕ} (u : Fin n → Fin N) {S : Set (ℕ → Fin N)} (hS : MeasurableSet S) :
    bernoulli p hp (cylinder u ∩ shift^[n] ⁻¹' S) =
      (∏ k, ENNReal.ofReal (p (u k))) * bernoulli p hp S := by
  induction n generalizing S with
  | zero =>
    have : cylinder u = univ := eq_univ_of_forall fun ω k => k.elim0
    simp [this]
  | succ n ih =>
    have hmeas : MeasurableSet (cylinder (Fin.tail u) ∩ shift^[n] ⁻¹' S) :=
      (measurableSet_cylinder _).inter (hS.preimage (measurable_shift.iterate n))
    rw [cylinder_succ, Function.iterate_succ, preimage_comp, inter_assoc, ← preimage_inter,
      bernoulli_inter_shift hp _ hmeas, ih (Fin.tail u) hS, Fin.prod_univ_succ, mul_assoc]
    rfl

/-! ### Ergodicity -/

/-- The one-sided Bernoulli shift is ergodic. A shift-invariant set belongs to the tail
`σ`-algebra of the coordinates, so Kolmogorov's zero-one law applies. -/
theorem ergodic_shift {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p) :
    Ergodic shift (bernoulli p hp) := by
  refine ⟨measurePreserving_shift hp, ⟨fun s hs hinv => ?_⟩⟩
  set m : ℕ → MeasurableSpace (ℕ → Fin N) :=
    fun k => MeasurableSpace.comap (fun ω : ℕ → Fin N => ω k) inferInstance with hm
  have htail : MeasurableSet[limsup m atTop] s := by
    rw [limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
    intro n
    have h := (measurable_shift_iterate_le (N := N) n) hs
    rwa [Function.IsFixedPt.preimage_iterate hinv n] at h
  have h01 := measure_zero_or_one_of_measurableSet_limsup_atTop
    (fun k => (measurable_pi_apply k).comap_le)
    ((iIndepFun_iff_iIndep _ _ _).1 (iIndepFun_eval hp)) htail
  rw [eventuallyEmptyOrUniv_iff']
  rcases h01 with h | h
  · exact Or.inl (ae_eq_empty.2 h)
  · refine Or.inr (ae_eq_univ.2 ?_)
    rwa [prob_compl_eq_zero_iff hs]

end FractalGeometry.SelfConformal
