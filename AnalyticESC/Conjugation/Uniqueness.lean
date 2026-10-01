module

public import AnalyticESC.Conjugation.Linearisation
public import AnalyticESC.Conjugation.Basic

@[expose] public section

/-!
# Uniqueness of linearisations of a single map

For a map `f` of the class: `Ĥ_f` satisfies the fixed-point equation of the dual operator of `f`;
a linearisation `φ` of `f` with `φ' ≠ 0` satisfies `φ'' = Ĥ_f φ'`; solutions of `φ'' = Ĥ_f φ'`
are affine functions of the linearising map `ĝ` of (5.2); and `Ĥ_f` depends only on `f` on `[0,1]`.
-/

namespace AnalyticESC

open Set Metric Filter Topology

variable {ε : ℝ} {f : ℂ → ℂ}

/-! ## Auxiliary lemmas -/

/-- The system consisting of the single map `f`. -/
private def uniqIFS {ε : ℝ} {f : ℂ → ℂ} (hε : 0 < ε) (hf : InClass ε f) : IFS 1 ε :=
  ⟨fun _ => f, hε, fun _ => hf⟩

private theorem uniqIFS_comp (hε : 0 < ε) (hf : InClass ε f) (n : ℕ) :
    (uniqIFS hε hf).comp (List.replicate n 0) = f^[n] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, IFS.comp_cons, ih, Function.iterate_succ']
    rfl

/-- `Ĥ_f` is the dual natural projection of the constant word for the system `{f}`. -/
private theorem hatH_eq_dualProj_uniq (hε : 0 < ε) (hf : InClass ε f) :
    hatH f = (uniqIFS hε hf).dualProj (.inf fun _ => 0) := by
  funext z
  simp only [hatH, IFS.dualProj]
  refine tsum_congr fun k => ?_
  rw [(uniqIFS hε hf).dualTerm_of_get?_eq_some (Word.get?_inf _ k)]
  simp only [Word.take_inf, List.ofFn_const, List.reverse_replicate, uniqIFS_comp hε hf,
    IFS.nonlin]
  rfl

/-- Maps that agree on `[0,1]` and are differentiable at `x ∈ [0,1]` have the same derivative
at `x`. -/
private theorem hasDerivAt_unique_of_eqOn_I {u v : ℝ → ℝ} {a b x : ℝ} (hx : x ∈ I)
    (hu : HasDerivAt u a x) (hv : HasDerivAt v b x) (huv : ∀ y ∈ I, u y = v y) : a = b :=
  (uniqueDiffOn_Icc zero_lt_one x hx).eq_deriv _ hu.hasDerivWithinAt
    (hv.hasDerivWithinAt.congr huv (huv x hx))

/-- A function with zero derivative within `[0,1]` at every point of `[0,1]` is constant there. -/
private theorem eq_of_hasDerivWithinAt_zero_I_uniq {u : ℝ → ℝ}
    (hu : ∀ x ∈ I, HasDerivWithinAt u 0 I x) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    u x = u y := by
  have hdiff : DifferentiableOn ℝ u I := fun z hz => (hu z hz).differentiableWithinAt
  have h := constant_of_derivWithin_zero hdiff fun z hz =>
    (hu z (Ico_subset_Icc_self hz)).derivWithin
      (uniqueDiffOn_Icc zero_lt_one z (Ico_subset_Icc_self hz))
  rw [h x hx, h y hy]

/-- A complex number with zero imaginary part is real. -/
private theorem eq_ofReal_re_uniq {w : ℂ} (h : w.im = 0) : w = (w.re : ℂ) :=
  Complex.ext (by simp) (by simp [h])

/-! ## The main statements -/

/-- The real restriction of a map holomorphic on `B_ε` is analytic near `[0,1]`. -/
theorem analyticOnNhd_re_ofReal (hε : 0 < ε) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (nbhd ε)) :
    AnalyticOnNhd ℝ (fun x : ℝ => (g x).re) I := by
  intro x hx
  have ha : AnalyticAt ℝ g x :=
    (hg.analyticOnNhd (isOpen_nbhd ε) x (ofReal_mem_nbhd hε hx)).restrictScalars
  exact (Complex.reCLM.analyticAt _).comp (ha.comp (Complex.ofRealCLM.analyticAt x))

/-- `Ĥ_f = f''/f' + f' · Ĥ_f ∘ f`: `Ĥ_f` is fixed by the dual operator of `f`. -/
theorem hatH_eq_add (hε : 0 < ε) (hf : InClass ε f) {z : ℂ} (hz : z ∈ nbhd ε) :
    hatH f z = deriv (deriv f) z / deriv f z + deriv f z * hatH f (f z) := by
  -- the cocycle identity for the constant word `0 0 0 ⋯ = 0 (0 0 ⋯)` of the system `{f}`
  have hw : (Word.inf fun _ : ℕ => (0 : Fin 1)).prepend [0] = .inf fun _ => 0 := by
    simp only [Word.prepend]
    congr 1
    funext n
    exact Subsingleton.elim _ _
  have h := (uniqIFS hε hf).dualProj_prepend [0] (.inf fun _ => 0) (subset_closure hz)
  rw [hw, IFS.dualProj_singleton] at h
  rw [hatH_eq_dualProj_uniq hε hf, h]
  rfl

/-- Uniqueness of linearisations: if `φ` is analytic near `[0,1]` with `φ' ≠ 0` there and
`φ ∘ f = λ φ + t` on `[0,1]`, then `φ'' = Ĥ_f φ'` on `[0,1]`. -/
theorem deriv_deriv_eq_hatH_mul (hε : 0 < ε) (hf : InClass ε f) {φ : ℝ → ℝ}
    (hφ : AnalyticOnNhd ℝ φ I) (hφ' : ∀ x ∈ I, deriv φ x ≠ 0) {lam t : ℝ}
    (hconj : ∀ x ∈ I, φ (f x).re = lam * φ x + t) :
    ∀ x ∈ I, deriv (deriv φ) x = (hatH f x).re * deriv φ x := by
  have h2ε : 0 < 2 * ε := by linarith
  have hU := isOpen_nbhd (2 * ε)
  have hmem : ∀ {x : ℝ}, x ∈ I → (x : ℂ) ∈ nbhd ε := fun hx => ofReal_mem_nbhd hε hx
  have hmem2 : ∀ {x : ℝ}, x ∈ I → (x : ℂ) ∈ nbhd (2 * ε) := fun hx => ofReal_mem_nbhd h2ε hx
  have hf1 : DifferentiableOn ℂ (deriv f) (nbhd (2 * ε)) := hf.differentiableOn.deriv hU
  -- `F = Re f` on the real line, with `F' = Re f'` and `F'' = Re f''` on `I`
  set F : ℝ → ℝ := fun y => (f y).re with hF
  set F1 : ℝ → ℝ := fun y => (deriv f y).re with hF1
  set F2 : ℝ → ℝ := fun y => (deriv (deriv f) y).re with hF2
  have hFd : ∀ x ∈ I, HasDerivAt F (F1 x) x := fun x hx =>
    hasDerivAt_re_ofReal (hf.differentiableOn.differentiableAt (hU.mem_nhds (hmem2 hx)))
  have hF1d : ∀ x ∈ I, HasDerivAt F1 (F2 x) x := fun x hx =>
    hasDerivAt_re_ofReal (hf1.differentiableAt (hU.mem_nhds (hmem2 hx)))
  have hFI : ∀ x ∈ I, F x ∈ I := hf.re_mem_I
  have hfr : ∀ x ∈ I, f x = (F x : ℂ) := fun x hx =>
    eq_ofReal_re_uniq (hf.im_eq_zero x (hmem2 hx))
  have hf1r : ∀ x ∈ I, deriv f x = (F1 x : ℂ) := fun x hx =>
    eq_ofReal_re_uniq (im_deriv_eq_zero hU hf.differentiableOn hf.im_eq_zero (hmem2 hx))
  have hf2r : ∀ x ∈ I, deriv (deriv f) x = (F2 x : ℂ) := fun x hx =>
    eq_ofReal_re_uniq (im_deriv_eq_zero hU hf1
      (fun s hs => im_deriv_eq_zero hU hf.differentiableOn hf.im_eq_zero hs) (hmem2 hx))
  have hF1ne : ∀ x ∈ I, F1 x ≠ 0 := fun x hx h0 =>
    hf.deriv_ne_zero _ (subset_closure (hmem hx)) (by rw [hf1r x hx, h0, Complex.ofReal_zero])
  have hF1lt : ∀ x ∈ I, |F1 x| < 1 := fun x hx =>
    (Complex.abs_re_le_norm _).trans_lt (hf.norm_deriv_lt_one _ (subset_closure (hmem hx)))
  -- `φ` and `φ'` are differentiable near `I`
  have hφd : ∀ y ∈ I, HasDerivAt φ (deriv φ y) y := fun y hy =>
    (hφ y hy).differentiableAt.hasDerivAt
  have hφ1d : ∀ y ∈ I, HasDerivAt (deriv φ) (deriv (deriv φ) y) y := fun y hy =>
    (hφ y hy).deriv.differentiableAt.hasDerivAt
  -- differentiate `φ ∘ F = λ φ + t` twice within `I`
  have hA : ∀ x ∈ I, deriv φ (F x) * F1 x = lam * deriv φ x := fun x hx =>
    hasDerivAt_unique_of_eqOn_I hx ((hφd _ (hFI x hx)).comp x (hFd x hx))
      (((hφd x hx).const_mul lam).add_const t) hconj
  have hB : ∀ x ∈ I, deriv (deriv φ) (F x) * F1 x * F1 x + deriv φ (F x) * F2 x =
      lam * deriv (deriv φ) x := fun x hx =>
    hasDerivAt_unique_of_eqOn_I hx (((hφ1d _ (hFI x hx)).comp x (hFd x hx)).mul (hF1d x hx))
      ((hφ1d x hx).const_mul lam) hA
  -- `G = φ''/φ'` and `R = Re Ĥ_f` satisfy the same functional equation on `I`
  set G : ℝ → ℝ := fun y => deriv (deriv φ) y / deriv φ y with hG
  set R : ℝ → ℝ := fun y => (hatH f y).re with hR
  have hGeq : ∀ x ∈ I, G x = F1 x * G (F x) + F2 x / F1 x := by
    intro x hx
    have hA := hA x hx
    have hB := hB x hx
    have h1 := hφ' x hx
    have h2 := hφ' _ (hFI x hx)
    have h3 := hF1ne x hx
    simp only [hG]
    field_simp
    linear_combination (deriv (deriv φ) x) * hA - (deriv φ x) * hB
  have hReq : ∀ x ∈ I, R x = F1 x * R (F x) + F2 x / F1 x := by
    intro x hx
    simp only [hR]
    rw [hatH_eq_add hε hf (hmem hx), hf2r x hx, hf1r x hx, hfr x hx, ← Complex.ofReal_div,
      Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
    ring
  -- `D = G - R` satisfies `D = F' · D ∘ F` with `|F'| < 1`, so `D` vanishes where `|D|` is
  -- maximal
  set D : ℝ → ℝ := fun y => G y - R y with hD
  have hDeq : ∀ x ∈ I, D x = F1 x * D (F x) := fun x hx => by
    simp only [hD]
    rw [hGeq x hx, hReq x hx]
    ring
  have hGc : ContinuousOn G I := fun y hy =>
    ((hφ y hy).deriv.deriv.continuousAt.div (hφ y hy).deriv.continuousAt
      (hφ' y hy)).continuousWithinAt
  have hRc : ContinuousOn R I := fun y hy =>
    (analyticOnNhd_re_ofReal hε (differentiableOn_hatH hε hf) y hy).continuousAt.continuousWithinAt
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one)
    (hGc.sub hRc).abs
  have h0 : |D x₀| ≤ 0 := by
    have e : |D x₀| = |F1 x₀| * |D (F x₀)| := by rw [← abs_mul, ← hDeq x₀ hx₀]
    have hle : |D (F x₀)| ≤ |D x₀| := hmax (hFI x₀ hx₀)
    have hlt := hF1lt x₀ hx₀
    nlinarith [abs_nonneg (D x₀), abs_nonneg (F1 x₀), abs_nonneg (D (F x₀))]
  intro x hx
  have hDx : D x = 0 := abs_nonpos_iff.1 ((hmax hx).trans h0)
  have hGx : G x = R x := sub_eq_zero.1 hDx
  simp only [hG, hR] at hGx
  rw [div_eq_iff (hφ' x hx)] at hGx
  exact hGx

/-- Solutions of `φ'' = Ĥ_f φ'` on `[0,1]` are affine functions of the linearising map `ĝ`. -/
theorem eq_add_mul_koenigs (hε : 0 < ε) (hf : InClass ε f) {p : ℝ} (hp : p ∈ I) (hfp : f p = p)
    {φ : ℝ → ℝ} (hφ : AnalyticOnNhd ℝ φ I)
    (hode : ∀ x ∈ I, deriv (deriv φ) x = (hatH f x).re * deriv φ x) :
    ∀ x ∈ I, φ x = φ p + deriv φ p * (koenigs f p x).re := by
  have hmem : ∀ {x : ℝ}, x ∈ I → (x : ℂ) ∈ nbhd ε := fun hx => ofReal_mem_nbhd hε hx
  have hkd : DifferentiableOn ℂ (koenigs f p) (nbhd ε) := differentiableOn_koenigs hε hf hp hfp
  have hkat : ∀ {x : ℝ}, x ∈ I → DifferentiableAt ℂ (koenigs f p) x := fun hx =>
    hkd.differentiableAt ((isOpen_nbhd ε).mem_nhds (hmem hx))
  have hkre : ∀ x ∈ I, HasDerivAt (fun t : ℝ => (koenigs f p t).re)
      (deriv (koenigs f p) x).re x := fun x hx => hasDerivAt_re_ofReal (hkat hx)
  -- `G = Re ĝ'` is positive on `I` with `G' = Re Ĥ · G`
  set G : ℝ → ℝ := fun t => (deriv (koenigs f p) t).re with hG
  set c := deriv φ p
  have hGpos : ∀ x ∈ I, 0 < G x := fun x hx => (deriv_koenigs_ofReal hε hf hp hfp hx).2
  have hGp : G p = 1 := by simp [hG, deriv_koenigs_self hε hf hp hfp]
  have hGderiv : ∀ x ∈ I, HasDerivAt G ((hatH f x).re * G x) x := by
    intro x hx
    have h := hasDerivAt_re_ofReal ((hkd.deriv (isOpen_nbhd ε)).differentiableAt
      ((isOpen_nbhd ε).mem_nhds (hmem hx)))
    rwa [deriv_deriv_koenigs hε hf hp hfp (hmem hx), Complex.mul_re,
      (deriv_koenigs_ofReal hε hf hp hfp hx).1, mul_zero, sub_zero] at h
  -- `φ' / G` has zero derivative, so `φ' = c G` on `I`
  have hu : ∀ x ∈ I, HasDerivWithinAt (fun t => deriv φ t / G t) 0 I x := by
    intro x hx
    have h1 : HasDerivAt (deriv φ) ((hatH f x).re * deriv φ x) x := by
      rw [← hode x hx]
      exact (hφ x hx).deriv.differentiableAt.hasDerivAt
    convert (h1.div (hGderiv x hx) (hGpos x hx).ne').hasDerivWithinAt using 1
    ring
  have hφ'eq : ∀ x ∈ I, deriv φ x = c * G x := by
    intro x hx
    have h := eq_of_hasDerivWithinAt_zero_I_uniq hu hx hp
    rw [hGp, div_one, div_eq_iff (hGpos x hx).ne'] at h
    exact h
  -- `φ - c Re ĝ` has zero derivative, so `φ = φ(p) + c Re ĝ` on `I`
  have hv : ∀ x ∈ I, HasDerivWithinAt (fun t => φ t - c * (koenigs f p t).re) 0 I x := by
    intro x hx
    have h := ((hφ x hx).differentiableAt.hasDerivAt.sub
      ((hkre x hx).const_mul c)).hasDerivWithinAt (s := I)
    rwa [hφ'eq x hx, sub_self] at h
  intro x hx
  have h := eq_of_hasDerivWithinAt_zero_I_uniq hv hx hp
  rw [koenigs_self hε hf hp hfp, Complex.zero_re, mul_zero, sub_zero] at h
  linarith

/-- `Ĥ_f` depends only on `f` on `[0,1]`. -/
theorem hatH_eq_of_eqOn_I {ε' : ℝ} {g : ℂ → ℂ} (hε : 0 < ε) (hf : InClass ε f) (hε' : 0 < ε')
    (hg : InClass ε' g) (h : ∀ x ∈ I, f x = g x) : ∀ x ∈ I, hatH f x = hatH g x := by
  -- `δ = min ε ε'`
  obtain ⟨δ, hδ, hδε, hδε', hcase⟩ : ∃ δ, 0 < δ ∧ δ ≤ ε ∧ δ ≤ ε' ∧ (δ = ε ∨ δ = ε') :=
    ⟨min ε ε', lt_min hε hε', min_le_left _ _, min_le_right _ _, min_choice _ _⟩
  have h2δ : 0 < 2 * δ := by linarith
  have hU := isOpen_nbhd (2 * δ)
  have hδ2 : nbhd δ ⊆ nbhd (2 * δ) := nbhd_mono (by linarith)
  -- `f = g` on `B_{2δ}` by the identity theorem
  have hfg : EqOn f g (nbhd (2 * δ)) :=
    eqOn_nbhd_of_eqOn_Icc h2δ (hf.differentiableOn.mono (nbhd_mono (by linarith)))
      (hg.differentiableOn.mono (nbhd_mono (by linarith))) zero_lt_one subset_rfl h
  -- `f` maps `B_δ` into itself: for `δ = ε` by (B), and for `δ = ε'` since `f = g` there
  have hmaps : MapsTo f (nbhd δ) (nbhd δ) := by
    rcases hcase with rfl | rfl
    · exact fun z hz => hf.mapsTo (subset_closure hz)
    · intro z hz
      rw [hfg (hδ2 hz)]
      exact hg.mapsTo (subset_closure hz)
  have hiter : ∀ k, ∀ z ∈ nbhd δ, f^[k] z = g^[k] z ∧ f^[k] z ∈ nbhd δ := by
    intro k
    induction k with
    | zero => exact fun z hz => ⟨rfl, hz⟩
    | succ k ih =>
      intro z hz
      obtain ⟨h1, h2⟩ := ih (f z) (hmaps hz)
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← hfg (hδ2 hz)]
      exact ⟨h1, h2⟩
  have hd1 : EqOn (deriv f) (deriv g) (nbhd (2 * δ)) := hfg.deriv hU
  have hd2 : EqOn (deriv (deriv f)) (deriv (deriv g)) (nbhd (2 * δ)) := hd1.deriv hU
  have hdk : ∀ k, EqOn (deriv (f^[k])) (deriv (g^[k])) (nbhd δ) :=
    fun k => EqOn.deriv (fun z hz => (hiter k z hz).1) (isOpen_nbhd δ)
  intro x hx
  have hxδ := ofReal_mem_nbhd hδ hx
  refine tsum_congr fun k => ?_
  obtain ⟨h1, h2⟩ := hiter k x hxδ
  rw [hdk k hxδ, ← h1, hd1 (hδ2 h2), hd2 (hδ2 h2)]

end AnalyticESC
