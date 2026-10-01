module

public import AnalyticESC.Defs

@[expose] public section

/-!
# Basic properties

The neighbourhoods `B_δ`, consequences of the conditions (A)–(C) defining the class, the
constants `c_min` and `c_max`, compositions along finite words, and the passage between complex
derivatives and derivatives of real restrictions.
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-! ## The neighbourhoods `B_δ` -/

/-- The image of `I` in `ℂ` is compact. -/
theorem isCompact_image_I : IsCompact (((↑) : ℝ → ℂ) '' I) :=
  isCompact_Icc.image Complex.continuous_ofReal

/-- The image of `I` in `ℂ` is convex. -/
theorem convex_image_I : Convex ℝ (((↑) : ℝ → ℂ) '' I) :=
  (convex_Icc (0 : ℝ) 1).linear_image Complex.ofRealCLM.toLinearMap

theorem isOpen_nbhd (δ : ℝ) : IsOpen (nbhd δ) := isOpen_thickening

theorem convex_nbhd (δ : ℝ) : Convex ℝ (nbhd δ) := convex_image_I.thickening δ

theorem isPreconnected_nbhd (δ : ℝ) : IsPreconnected (nbhd δ) := (convex_nbhd δ).isPreconnected

theorem isBounded_nbhd (δ : ℝ) : Bornology.IsBounded (nbhd δ) :=
  isCompact_image_I.isBounded.thickening

theorem isCompact_closure_nbhd (δ : ℝ) : IsCompact (closure (nbhd δ)) :=
  (isBounded_nbhd δ).isCompact_closure

theorem ofReal_mem_nbhd {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : x ∈ I) : (x : ℂ) ∈ nbhd δ :=
  self_subset_thickening hδ _ (mem_image_of_mem _ hx)

theorem ball_subset_nbhd {δ x : ℝ} (hx : x ∈ I) : ball (x : ℂ) δ ⊆ nbhd δ :=
  ball_subset_thickening (mem_image_of_mem _ hx) δ

theorem nbhd_mono {δ δ' : ℝ} (h : δ ≤ δ') : nbhd δ ⊆ nbhd δ' := thickening_mono h _

theorem nbhd_of_nonpos {δ : ℝ} (h : δ ≤ 0) : nbhd δ = ∅ := thickening_of_nonpos h _

theorem zero_mem_closure_nbhd {δ : ℝ} (hδ : 0 < δ) : (0 : ℂ) ∈ closure (nbhd δ) := by
  have h := ofReal_mem_nbhd hδ (x := 0) ⟨le_rfl, zero_le_one⟩
  rw [Complex.ofReal_zero] at h
  exact subset_closure h

theorem closure_nbhd_subset {δ δ' : ℝ} (h : δ < δ') : closure (nbhd δ) ⊆ nbhd δ' := by
  rcases le_or_gt δ' 0 with h' | h'
  · simp [nbhd_of_nonpos (h.le.trans h')]
  · exact (closure_thickening_subset_cthickening δ _).trans (cthickening_subset_thickening' h' h _)

/-! ## Real restrictions -/

/-- The derivative of the real restriction of a complex differentiable map. -/
theorem hasDerivAt_re_ofReal {g : ℂ → ℂ} {x : ℝ} (hg : DifferentiableAt ℂ g x) :
    HasDerivAt (fun t : ℝ => (g t).re) (deriv g x).re x := hg.hasDerivAt.real_of_complex

/-- The real points of an open subset of `ℂ` form an open subset of `ℝ`. -/
theorem isOpen_setOf_ofReal_mem {U : Set ℂ} (hU : IsOpen U) : IsOpen {t : ℝ | (t : ℂ) ∈ U} :=
  hU.preimage Complex.continuous_ofReal

/-- Iterated derivatives of the real restriction of a holomorphic map. -/
theorem iteratedDeriv_re_ofReal {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (k : ℕ) {x : ℝ} (hx : (x : ℂ) ∈ U) :
    iteratedDeriv k (fun t : ℝ => (g t).re) x = (iteratedDeriv k g x).re := by
  have hdiff : ∀ k, DifferentiableOn ℂ (iteratedDeriv k g) U := by
    intro k
    rw [iteratedDeriv_eq_iterate]
    exact ((hg.analyticOnNhd hU).iterated_deriv k).differentiableOn
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have heq : iteratedDeriv k (fun t : ℝ => (g t).re) =ᶠ[𝓝 x]
        fun t => (iteratedDeriv k g t).re := by
      filter_upwards [(isOpen_setOf_ofReal_mem hU).mem_nhds hx] with t ht using ih ht
    rw [iteratedDeriv_succ, heq.deriv_eq, iteratedDeriv_succ]
    exact (hasDerivAt_re_ofReal ((hdiff k).differentiableAt (hU.mem_nhds hx))).deriv

/-- The real restriction of a holomorphic map is smooth on the real points of its domain. -/
theorem contDiffOn_re_ofReal {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (n : ℕ) :
    ContDiffOn ℝ n (fun t : ℝ => (g t).re) {t : ℝ | (t : ℂ) ∈ U} := by
  intro x hx
  have h : ContDiffAt ℂ n g x := (hg.contDiffOn hU).contDiffAt (hU.mem_nhds hx)
  exact h.real_of_complex.contDiffWithinAt

/-- A holomorphic map that is real at the real points of an open set has real derivative
there. -/
theorem im_deriv_eq_zero {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hreal : ∀ t : ℝ, (t : ℂ) ∈ U → (g t).im = 0) {x : ℝ} (hx : (x : ℂ) ∈ U) :
    (deriv g x).im = 0 := by
  have hd : HasDerivAt g (deriv g x) x := (hg.differentiableAt (hU.mem_nhds hx)).hasDerivAt
  have h1 : HasDerivAt (fun t : ℝ => g t) (deriv g x) x := hd.comp_ofReal
  have h2 : HasDerivAt (fun t : ℝ => (g t).im) (deriv g x).im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h1
  have h3 : HasDerivAt (fun t : ℝ => (g t).im) 0 x := by
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [(isOpen_setOf_ofReal_mem hU).mem_nhds hx] with t ht using hreal t ht
  exact h2.unique h3

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-! ## Single maps -/

theorem nbhd_subset_two : nbhd ε ⊆ nbhd (2 * ε) := by
  rcases le_or_gt ε 0 with h | h
  · simp [nbhd_of_nonpos h]
  · exact nbhd_mono (by linarith)

theorem closure_nbhd_subset_two : closure (nbhd ε) ⊆ nbhd (2 * ε) := by
  rcases le_or_gt ε 0 with h | h
  · simp [nbhd_of_nonpos h]
  · exact closure_nbhd_subset (by linarith)

theorem differentiableOn_f (i : Fin N) : DifferentiableOn ℂ (Φ.f i) (nbhd (2 * ε)) :=
  (Φ.inClass i).differentiableOn

theorem differentiableAt_f (i : Fin N) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    DifferentiableAt ℂ (Φ.f i) z :=
  (Φ.differentiableOn_f i).differentiableAt ((isOpen_nbhd _).mem_nhds (closure_nbhd_subset_two hz))

theorem continuousOn_deriv_f (i : Fin N) : ContinuousOn (deriv (Φ.f i)) (nbhd (2 * ε)) :=
  ((Φ.differentiableOn_f i).deriv (isOpen_nbhd _)).continuousOn

theorem mapsTo_f (i : Fin N) : MapsTo (Φ.f i) (nbhd ε) (nbhd ε) :=
  fun _ hz => (Φ.inClass i).mapsTo (subset_closure hz)

theorem im_f_ofReal (i : Fin N) {t : ℝ} (ht : (t : ℂ) ∈ nbhd (2 * ε)) : (Φ.f i t).im = 0 :=
  (Φ.inClass i).im_eq_zero t ht

theorem continuousOn_norm_deriv_f (i : Fin N) :
    ContinuousOn (fun z => ‖deriv (Φ.f i) z‖) (closure (nbhd ε)) :=
  ((Φ.continuousOn_deriv_f i).mono closure_nbhd_subset_two).norm

theorem bddAbove_norm_deriv (i : Fin N) :
    BddAbove (range fun z : closure (nbhd ε) => ‖deriv (Φ.f i) z‖) := by
  rw [← image_eq_range (fun z => ‖deriv (Φ.f i) z‖)]
  exact (isCompact_closure_nbhd ε).bddAbove_image (Φ.continuousOn_norm_deriv_f i)

theorem bddBelow_norm_deriv (i : Fin N) :
    BddBelow (range fun z : closure (nbhd ε) => ‖deriv (Φ.f i) z‖) :=
  ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩

theorem cmax_nonneg : 0 ≤ Φ.cmax :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem cmin_nonneg : 0 ≤ Φ.cmin :=
  Real.iInf_nonneg fun _ => Real.iInf_nonneg fun _ => norm_nonneg _

theorem cmax_lt_one : Φ.cmax < 1 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [cmax]
  have hi : ∀ i, ⨆ z : closure (nbhd ε), ‖deriv (Φ.f i) z‖ < 1 := by
    intro i
    have : Nonempty (closure (nbhd ε)) := ⟨⟨0, zero_mem_closure_nbhd Φ.ε_pos⟩⟩
    obtain ⟨z, hz, hmax⟩ := (isCompact_closure_nbhd ε).exists_isMaxOn
      ⟨0, zero_mem_closure_nbhd Φ.ε_pos⟩ (Φ.continuousOn_norm_deriv_f i)
    calc ⨆ z : closure (nbhd ε), ‖deriv (Φ.f i) z‖ ≤ ‖deriv (Φ.f i) z‖ :=
          ciSup_le fun w => hmax w.2
      _ < 1 := (Φ.inClass i).norm_deriv_lt_one z hz
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨i, hi'⟩ := exists_eq_ciSup_of_finite
    (f := fun i : Fin N => ⨆ z : closure (nbhd ε), ‖deriv (Φ.f i) z‖)
  rw [cmax, ← hi']
  exact hi i

theorem norm_deriv_le_cmax (i : Fin N) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    ‖deriv (Φ.f i) z‖ ≤ Φ.cmax :=
  calc ‖deriv (Φ.f i) z‖ ≤ ⨆ z : closure (nbhd ε), ‖deriv (Φ.f i) z‖ :=
        le_ciSup (Φ.bddAbove_norm_deriv i) ⟨z, hz⟩
    _ ≤ Φ.cmax := le_ciSup (f := fun i => ⨆ z : closure (nbhd ε), ‖deriv (Φ.f i) z‖)
        (finite_range _).bddAbove i

theorem cmin_pos (hN : 0 < N) : 0 < Φ.cmin := by
  have hi : ∀ i, 0 < ⨅ z : closure (nbhd ε), ‖deriv (Φ.f i) z‖ := by
    intro i
    have : Nonempty (closure (nbhd ε)) := ⟨⟨0, zero_mem_closure_nbhd Φ.ε_pos⟩⟩
    obtain ⟨z, hz, hmin⟩ := (isCompact_closure_nbhd ε).exists_isMinOn
      ⟨0, zero_mem_closure_nbhd Φ.ε_pos⟩ (Φ.continuousOn_norm_deriv_f i)
    calc (0 : ℝ) < ‖deriv (Φ.f i) z‖ := norm_pos_iff.2 ((Φ.inClass i).deriv_ne_zero z hz)
      _ ≤ ⨅ z : closure (nbhd ε), ‖deriv (Φ.f i) z‖ := le_ciInf fun w => hmin w.2
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨i, hi'⟩ := (range_nonempty
    (fun i : Fin N => ⨅ z : closure (nbhd ε), ‖deriv (Φ.f i) z‖)).csInf_mem (finite_range _)
  rw [cmin, iInf, ← hi']
  exact hi i

theorem cmin_le_norm_deriv (i : Fin N) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    Φ.cmin ≤ ‖deriv (Φ.f i) z‖ :=
  calc Φ.cmin ≤ ⨅ z : closure (nbhd ε), ‖deriv (Φ.f i) z‖ :=
        ciInf_le (f := fun i => ⨅ z : closure (nbhd ε), ‖deriv (Φ.f i) z‖)
          (finite_range _).bddBelow i
    _ ≤ ‖deriv (Φ.f i) z‖ := ciInf_le (Φ.bddBelow_norm_deriv i) ⟨z, hz⟩

theorem cmin_le_cmax (hN : 0 < N) : Φ.cmin ≤ Φ.cmax :=
  (Φ.cmin_le_norm_deriv ⟨0, hN⟩ (zero_mem_closure_nbhd Φ.ε_pos)).trans
    (Φ.norm_deriv_le_cmax ⟨0, hN⟩ (zero_mem_closure_nbhd Φ.ε_pos))

/-- `f_i''/f_i'` is holomorphic on an open set containing `cl B_ε`. -/
theorem exists_differentiableOn_nonlin (i : Fin N) :
    ∃ U : Set ℂ, IsOpen U ∧ closure (nbhd ε) ⊆ U ∧ U ⊆ nbhd (2 * ε) ∧
      DifferentiableOn ℂ (Φ.nonlin i) U := by
  refine ⟨nbhd (2 * ε) ∩ deriv (Φ.f i) ⁻¹' {0}ᶜ,
    (Φ.continuousOn_deriv_f i).isOpen_inter_preimage (isOpen_nbhd _) isOpen_compl_singleton,
    fun z hz => ⟨closure_nbhd_subset_two hz, (Φ.inClass i).deriv_ne_zero z hz⟩,
    inter_subset_left, ?_⟩
  have h1 := (Φ.differentiableOn_f i).deriv (isOpen_nbhd _)
  have h2 := h1.deriv (isOpen_nbhd _)
  exact (h2.mono inter_subset_left).div (h1.mono inter_subset_left) fun z hz => hz.2

theorem exists_nonlin_bound :
    ∃ M, 0 ≤ M ∧ ∀ i, ∀ z ∈ closure (nbhd ε), ‖Φ.nonlin i z‖ ≤ M := by
  have h : ∀ i, ∃ C, ∀ z ∈ closure (nbhd ε), ‖Φ.nonlin i z‖ ≤ C := by
    intro i
    obtain ⟨U, -, hU, -, hd⟩ := Φ.exists_differentiableOn_nonlin i
    exact (isCompact_closure_nbhd ε).exists_bound_of_continuousOn (hd.continuousOn.mono hU)
  choose C hC using h
  refine ⟨∑ i, |C i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun i z hz => ?_⟩
  calc ‖Φ.nonlin i z‖ ≤ C i := hC i z hz
    _ ≤ |C i| := le_abs_self _
    _ ≤ ∑ i, |C i| :=
        Finset.single_le_sum (f := fun i => |C i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)

theorem im_deriv_f_ofReal (i : Fin N) {t : ℝ} (ht : (t : ℂ) ∈ nbhd (2 * ε)) :
    (deriv (Φ.f i) t).im = 0 :=
  im_deriv_eq_zero (isOpen_nbhd _) (Φ.differentiableOn_f i) (fun _ hs => Φ.im_f_ofReal i hs) ht

theorem im_nonlin_ofReal (i : Fin N) {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) :
    (Φ.nonlin i t).im = 0 := by
  have ht2 := nbhd_subset_two ht
  have h1 := (Φ.differentiableOn_f i).deriv (isOpen_nbhd _)
  have hdd : (deriv (deriv (Φ.f i)) t).im = 0 :=
    im_deriv_eq_zero (isOpen_nbhd _) h1 (fun _ hs => Φ.im_deriv_f_ofReal i hs) ht2
  simp [nonlin, Complex.div_im, Φ.im_deriv_f_ofReal i ht2, hdd]

/-! ## Compositions along finite words -/

@[simp] theorem comp_nil : Φ.comp [] = id := rfl

@[simp] theorem comp_cons (i : Fin N) (w : List (Fin N)) : Φ.comp (i :: w) = Φ.f i ∘ Φ.comp w :=
  rfl

theorem comp_append (u v : List (Fin N)) : Φ.comp (u ++ v) = Φ.comp u ∘ Φ.comp v := by
  induction u with
  | nil => rfl
  | cons i u ih => rw [List.cons_append, comp_cons, ih, comp_cons]; rfl

theorem mapsTo_comp (w : List (Fin N)) : MapsTo (Φ.comp w) (nbhd ε) (nbhd ε) := by
  induction w with
  | nil => exact mapsTo_id _
  | cons i w ih => rw [comp_cons]; exact (Φ.mapsTo_f i).comp ih

theorem mapsTo_comp_closure (w : List (Fin N)) :
    MapsTo (Φ.comp w) (closure (nbhd ε)) (closure (nbhd ε)) := by
  induction w with
  | nil => exact mapsTo_id _
  | cons i w ih =>
    rw [comp_cons]
    exact ((Φ.inClass i).mapsTo.mono_right subset_closure).comp ih

theorem differentiableAt_comp (w : List (Fin N)) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    DifferentiableAt ℂ (Φ.comp w) z := by
  induction w with
  | nil => exact differentiableAt_id
  | cons i w ih =>
    rw [comp_cons]
    exact (Φ.differentiableAt_f i (Φ.mapsTo_comp_closure w hz)).comp z ih

theorem differentiableOn_comp (w : List (Fin N)) : DifferentiableOn ℂ (Φ.comp w) (nbhd ε) :=
  fun _ hz => (Φ.differentiableAt_comp w (subset_closure hz)).differentiableWithinAt

/-- `f_w` is holomorphic on an open set containing `cl B_ε`. -/
theorem exists_differentiableOn_comp (w : List (Fin N)) :
    ∃ U : Set ℂ, IsOpen U ∧ closure (nbhd ε) ⊆ U ∧ DifferentiableOn ℂ (Φ.comp w) U := by
  induction w with
  | nil => exact ⟨univ, isOpen_univ, subset_univ _, differentiableOn_id⟩
  | cons i w ih =>
    obtain ⟨U, hU, hcl, hd⟩ := ih
    refine ⟨U ∩ Φ.comp w ⁻¹' nbhd (2 * ε),
      hd.continuousOn.isOpen_inter_preimage hU (isOpen_nbhd _),
      fun z hz => ⟨hcl hz, closure_nbhd_subset_two (Φ.mapsTo_comp_closure w hz)⟩, ?_⟩
    rw [comp_cons]
    exact (Φ.differentiableOn_f i).comp (hd.mono inter_subset_left) fun z hz => hz.2

theorem deriv_comp_cons (i : Fin N) (w : List (Fin N)) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    deriv (Φ.comp (i :: w)) z = deriv (Φ.f i) (Φ.comp w z) * deriv (Φ.comp w) z := by
  rw [comp_cons]
  exact deriv_comp z (Φ.differentiableAt_f i (Φ.mapsTo_comp_closure w hz))
    (Φ.differentiableAt_comp w hz)

theorem deriv_comp_append (u v : List (Fin N)) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    deriv (Φ.comp (u ++ v)) z = deriv (Φ.comp u) (Φ.comp v z) * deriv (Φ.comp v) z := by
  rw [comp_append]
  exact deriv_comp z (Φ.differentiableAt_comp u (Φ.mapsTo_comp_closure v hz))
    (Φ.differentiableAt_comp v hz)

theorem norm_deriv_comp_le (w : List (Fin N)) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    ‖deriv (Φ.comp w) z‖ ≤ Φ.cmax ^ w.length := by
  induction w with
  | nil => simp [deriv_id]
  | cons i w ih =>
    rw [Φ.deriv_comp_cons i w hz, norm_mul, List.length_cons, pow_succ']
    exact mul_le_mul (Φ.norm_deriv_le_cmax i (Φ.mapsTo_comp_closure w hz)) ih (norm_nonneg _)
      Φ.cmax_nonneg

theorem cmin_pow_le_norm_deriv_comp (w : List (Fin N)) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    Φ.cmin ^ w.length ≤ ‖deriv (Φ.comp w) z‖ := by
  induction w with
  | nil => simp [deriv_id]
  | cons i w ih =>
    rw [Φ.deriv_comp_cons i w hz, norm_mul, List.length_cons, pow_succ']
    exact mul_le_mul (Φ.cmin_le_norm_deriv i (Φ.mapsTo_comp_closure w hz)) ih
      (pow_nonneg Φ.cmin_nonneg _) (norm_nonneg _)

theorem deriv_comp_ne_zero (w : List (Fin N)) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    deriv (Φ.comp w) z ≠ 0 := by
  induction w with
  | nil => simp [deriv_id]
  | cons i w ih =>
    rw [Φ.deriv_comp_cons i w hz]
    exact mul_ne_zero ((Φ.inClass i).deriv_ne_zero _ (Φ.mapsTo_comp_closure w hz)) ih

/-- A uniform bound for all compositions on `cl B_ε`. -/
theorem exists_comp_bound : ∃ R, 0 ≤ R ∧ ∀ w, ∀ z ∈ closure (nbhd ε), ‖Φ.comp w z‖ ≤ R := by
  obtain ⟨R, hR⟩ := (isCompact_closure_nbhd ε).isBounded.exists_norm_le
  exact ⟨max R 0, le_max_right _ _,
    fun w z hz => (hR _ (Φ.mapsTo_comp_closure w hz)).trans (le_max_left _ _)⟩

theorem norm_comp_sub_le (w : List (Fin N)) {z z' : ℂ} (hz : z ∈ nbhd ε) (hz' : z' ∈ nbhd ε) :
    ‖Φ.comp w z - Φ.comp w z'‖ ≤ Φ.cmax ^ w.length * ‖z - z'‖ :=
  (convex_nbhd ε).norm_image_sub_le_of_norm_deriv_le
    (fun _ hx => Φ.differentiableAt_comp w (subset_closure hx))
    (fun _ hx => Φ.norm_deriv_comp_le w (subset_closure hx)) hz' hz

theorem im_comp_ofReal (w : List (Fin N)) {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) :
    (Φ.comp w t).im = 0 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [comp_cons, Function.comp_apply]
    have h1 : Φ.comp w t = ((Φ.comp w t).re : ℂ) := Complex.ext (by simp) (by simp [ih])
    have h2 : ((Φ.comp w t).re : ℂ) ∈ nbhd (2 * ε) := by
      rw [← h1]
      exact nbhd_subset_two (Φ.mapsTo_comp w ht)
    rw [h1]
    exact Φ.im_f_ofReal i h2

theorem comp_ofReal (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    Φ.comp w x = ((Φ.comp w x).re : ℂ) :=
  Complex.ext (by simp) (by simp [Φ.im_comp_ofReal w (ofReal_mem_nbhd Φ.ε_pos hx)])

theorem re_comp_mem_I (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) : (Φ.comp w x).re ∈ I := by
  induction w with
  | nil => simpa using hx
  | cons i w ih =>
    rw [comp_cons, Function.comp_apply, Φ.comp_ofReal w hx]
    exact (Φ.inClass i).re_mem_I _ ih

theorem im_deriv_comp_ofReal (w : List (Fin N)) {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) :
    (deriv (Φ.comp w) t).im = 0 :=
  im_deriv_eq_zero (isOpen_nbhd ε) (Φ.differentiableOn_comp w)
    (fun _ hs => Φ.im_comp_ofReal w hs) ht

/-- The image `f_w(I)` is an interval of length between `c_min^{|w|}` and `c_max^{|w|}`. -/
theorem exists_image_comp_eq_Icc (w : List (Fin N)) :
    ∃ p q : ℝ, 0 ≤ p ∧ p ≤ q ∧ q ≤ 1 ∧ Φ.cmin ^ w.length ≤ q - p ∧
      q - p ≤ Φ.cmax ^ w.length ∧ (fun x : ℝ => (Φ.comp w x).re) '' I = Icc p q := by
  set h : ℝ → ℝ := fun x => (Φ.comp w x).re with h_def
  have hmem : ∀ {x : ℝ}, x ∈ I → (x : ℂ) ∈ nbhd ε := fun hx => ofReal_mem_nbhd Φ.ε_pos hx
  have hderiv : ∀ x ∈ I, HasDerivAt h (deriv (Φ.comp w) x).re x := fun x hx =>
    hasDerivAt_re_ofReal (Φ.differentiableAt_comp w (subset_closure (hmem hx)))
  have hcont : ContinuousOn h I := fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have himage : h '' I = Icc (sInf (h '' I)) (sSup (h '' I)) := hcont.image_Icc zero_le_one
  set p := sInf (h '' I)
  set q := sSup (h '' I)
  have h0 : h 0 ∈ Icc p q := himage ▸ mem_image_of_mem h (left_mem_Icc.2 zero_le_one)
  have h1 : h 1 ∈ Icc p q := himage ▸ mem_image_of_mem h (right_mem_Icc.2 zero_le_one)
  have hpq : p ≤ q := h0.1.trans h0.2
  obtain ⟨a, ha, hpa⟩ : p ∈ h '' I := himage ▸ left_mem_Icc.2 hpq
  obtain ⟨b, hb, hqb⟩ : q ∈ h '' I := himage ▸ right_mem_Icc.2 hpq
  refine ⟨p, q, ?_, hpq, ?_, ?_, ?_, himage⟩
  · rw [← hpa]; exact (Φ.re_comp_mem_I w ha).1
  · rw [← hqb]; exact (Φ.re_comp_mem_I w hb).2
  · -- lower bound via the mean value theorem on `[0,1]`
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope h (fun x => (deriv (Φ.comp w) x).re)
      zero_lt_one hcont (fun x hx => hderiv x (Ioo_subset_Icc_self hx))
    have hcI : c ∈ I := Ioo_subset_Icc_self hc
    have hnorm : |(deriv (Φ.comp w) c).re| = ‖deriv (Φ.comp w) c‖ :=
      Complex.abs_re_eq_norm.2 (Φ.im_deriv_comp_ofReal w (hmem hcI))
    have hlow : Φ.cmin ^ w.length ≤ |h 1 - h 0| := by
      have := Φ.cmin_pow_le_norm_deriv_comp w (subset_closure (hmem hcI))
      rw [← hnorm, hslope] at this
      simpa using this
    have : |h 1 - h 0| ≤ q - p := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]
    linarith
  · -- upper bound via the complex mean value inequality
    have hab : ‖Φ.comp w b - Φ.comp w a‖ ≤ Φ.cmax ^ w.length * ‖(b : ℂ) - a‖ :=
      Φ.norm_comp_sub_le w (hmem hb) (hmem ha)
    have hre : q - p ≤ ‖Φ.comp w b - Φ.comp w a‖ := by
      rw [← hpa, ← hqb]
      calc h b - h a ≤ |h b - h a| := le_abs_self _
        _ = |(Φ.comp w b - Φ.comp w a).re| := by simp [h_def]
        _ ≤ ‖Φ.comp w b - Φ.comp w a‖ := Complex.abs_re_le_norm _
    have hba : ‖(b : ℂ) - a‖ ≤ 1 := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_le_iff]
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
    calc q - p ≤ ‖Φ.comp w b - Φ.comp w a‖ := hre
      _ ≤ Φ.cmax ^ w.length * ‖(b : ℂ) - a‖ := hab
      _ ≤ Φ.cmax ^ w.length * 1 :=
          mul_le_mul_of_nonneg_left hba (pow_nonneg Φ.cmax_nonneg _)
      _ = Φ.cmax ^ w.length := mul_one _

end IFS

end AnalyticESC
