module

public import AnalyticESC.Conjugation.Koenigs

@[expose] public section

/-!
# Lemma 5.1

A map of the class has a unique fixed point `p ∈ [0,1]`. For `a, b ∈ ℝ` with `b ≠ 0` there is an
invertible `g ∈ C^ω_ε([0,1])` with `g'' = Ĥ_f g'`, `g(p) = a` and `g'(p) = b`; and every solution
`g` of `g'' = Ĥ_f g'` on `[0,1]` conjugates `f` to the affine map `y ↦ f'(p) y + g(p)(1 - f'(p))`.
-/

namespace AnalyticESC

open Set Metric Filter Topology

variable {ε : ℝ} {f : ℂ → ℂ}

/-- A function with zero derivative within `[0,1]` at every point of `[0,1]` is constant there. -/
private theorem eq_of_hasDerivWithinAt_zero_I {u : ℝ → ℝ}
    (hu : ∀ x ∈ I, HasDerivWithinAt u 0 I x) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    u x = u y := by
  have hdiff : DifferentiableOn ℝ u I := fun z hz => (hu z hz).differentiableWithinAt
  have h := constant_of_derivWithin_zero hdiff fun z hz =>
    (hu z (Ico_subset_Icc_self hz)).derivWithin
      (uniqueDiffOn_Icc zero_lt_one z (Ico_subset_Icc_self hz))
  rw [h x hx, h y hy]

/-- A map of the class has a unique fixed point in `[0,1]`. -/
theorem existsUnique_fixedPoint (hε : 0 < ε) (hf : InClass ε f) :
    ∃! p : ℝ, p ∈ I ∧ f p = p := by
  have h2ε : 0 < 2 * ε := by linarith
  -- `F(x) = f(x) - x` on `I`, which is strictly decreasing since `|f'| < 1`
  set F : ℝ → ℝ := fun x => (f x).re - x with hF
  have hderiv : ∀ x ∈ I, HasDerivAt F ((deriv f x).re - 1) x := fun x hx =>
    (hasDerivAt_re_ofReal (hf.differentiableOn.differentiableAt
      ((isOpen_nbhd _).mem_nhds (ofReal_mem_nbhd h2ε hx)))).sub (hasDerivAt_id x)
  have hcont : ContinuousOn F I := fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hfix : ∀ x ∈ I, f x = x ↔ F x = 0 := by
    intro x hx
    have hreal : f x = ((f x).re : ℂ) :=
      Complex.ext (by simp) (by simp [hf.im_eq_zero x (ofReal_mem_nbhd h2ε hx)])
    rw [hreal, Complex.ofReal_inj, hF, sub_eq_zero]
  have hanti : StrictAntiOn F I := by
    refine strictAntiOn_of_deriv_neg (convex_Icc 0 1) hcont fun x hx => ?_
    have hxI : x ∈ I := interior_subset hx
    rw [(hderiv x hxI).deriv, sub_neg]
    exact (Complex.re_le_norm _).trans_lt
      (hf.norm_deriv_lt_one x (subset_closure (ofReal_mem_nbhd hε hxI)))
  -- the intermediate value theorem gives a zero of `F`
  obtain ⟨p, hp, hFp⟩ : (0 : ℝ) ∈ F '' I := by
    refine intermediate_value_Icc' zero_le_one hcont ⟨?_, ?_⟩
    · have := (hf.re_mem_I 1 (right_mem_Icc.2 zero_le_one)).2
      show (f ((1 : ℝ) : ℂ)).re - 1 ≤ 0
      linarith
    · have := (hf.re_mem_I 0 (left_mem_Icc.2 zero_le_one)).1
      show 0 ≤ (f ((0 : ℝ) : ℂ)).re - 0
      linarith
  refine ⟨p, ⟨hp, (hfix p hp).2 hFp⟩, fun q ⟨hq, hfq⟩ => hanti.injOn hq hp ?_⟩
  rw [(hfix q hq).1 hfq, hFp]

/-- Lemma 5.1. Here `p` is the fixed point of `f` in `[0,1]`. The map `g` is invertible as a map
on `[0,1]`, and the second part concerns maps `g` that are twice differentiable on `[0,1]`, with
one-sided derivatives at the end points. -/
theorem lemma_5_1 (hε : 0 < ε) (hf : InClass ε f) {p : ℝ} (hp : p ∈ I) (hfp : f p = p) :
    (∀ a b : ℝ, b ≠ 0 → ∃ g : ℂ → ℂ, toNbhd ε g ∈ analyticSpace ε ∧
        InjOn (fun x : ℝ => (g x).re) I ∧
        (∀ x ∈ I, deriv (deriv g) x = hatH f x * deriv g x) ∧ g p = a ∧ deriv g p = b) ∧
      ∀ g : ℝ → ℝ, DifferentiableOn ℝ g I → DifferentiableOn ℝ (derivWithin g I) I →
        (∀ x ∈ I, derivWithin (derivWithin g I) I x = (hatH f x).re * derivWithin g I x) →
        ∀ x ∈ I, g (f x).re = (deriv f p).re * g x + g p * (1 - (deriv f p).re) := by
  have hmem : ∀ {x : ℝ}, x ∈ I → (x : ℂ) ∈ nbhd ε := fun hx => ofReal_mem_nbhd hε hx
  have hkd : DifferentiableOn ℂ (koenigs f p) (nbhd ε) := differentiableOn_koenigs hε hf hp hfp
  have hkat : ∀ {x : ℝ}, x ∈ I → DifferentiableAt ℂ (koenigs f p) x := fun hx =>
    hkd.differentiableAt ((isOpen_nbhd ε).mem_nhds (hmem hx))
  -- the real restriction of `ĝ` has derivative `ĝ' > 0` on `I`, so it is strictly increasing
  have hkre : ∀ x ∈ I, HasDerivAt (fun t : ℝ => (koenigs f p t).re)
      (deriv (koenigs f p) x).re x := fun x hx => hasDerivAt_re_ofReal (hkat hx)
  have hmono : StrictMonoOn (fun t : ℝ => (koenigs f p t).re) I := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 1)
      (fun x hx => (hkre x hx).continuousAt.continuousWithinAt) fun x hx => ?_
    rw [(hkre x (interior_subset hx)).deriv]
    exact (deriv_koenigs_ofReal hε hf hp hfp (interior_subset hx)).2
  refine ⟨fun a b hb => ?_, fun g hg hg' hODE x hx => ?_⟩
  · -- `g = a + b ĝ`
    have hderiv : deriv (fun z => (a : ℂ) + b * koenigs f p z) =
        fun z => b * deriv (koenigs f p) z := by
      rw [deriv_const_add', deriv_const_mul_field']
    refine ⟨fun z => (a : ℂ) + b * koenigs f p z,
      ⟨_, (hkd.const_mul _).const_add _,
        ((continuousOn_koenigs hε hf hp hfp).const_mul _).const_add _,
        fun x hx => ?_, rfl⟩, ?_, fun x hx => ?_, ?_, ?_⟩
    · simp [im_koenigs_ofReal hε hf hp hfp (hmem hx)]
    · intro x hx y hy hxy
      have h : b * (koenigs f p x).re = b * (koenigs f p y).re := by simpa using hxy
      exact hmono.injOn hx hy (mul_left_cancel₀ hb h)
    · rw [hderiv, deriv_const_mul_field']
      dsimp only
      rw [deriv_deriv_koenigs hε hf hp hfp (hmem hx)]
      ring
    · simp [koenigs_self hε hf hp hfp]
    · rw [hderiv]
      simp [deriv_koenigs_self hε hf hp hfp]
  · -- `G = Re ĝ'` is positive on `I` with `G' = Re Ĥ · G`
    set G : ℝ → ℝ := fun t => (deriv (koenigs f p) t).re with hG
    set c := derivWithin g I p
    have hGpos : ∀ x ∈ I, 0 < G x := fun x hx => (deriv_koenigs_ofReal hε hf hp hfp hx).2
    have hGp : G p = 1 := by simp [hG, deriv_koenigs_self hε hf hp hfp]
    have hGderiv : ∀ x ∈ I, HasDerivAt G ((hatH f x).re * G x) x := by
      intro x hx
      have h := hasDerivAt_re_ofReal ((hkd.deriv (isOpen_nbhd ε)).differentiableAt
        ((isOpen_nbhd ε).mem_nhds (hmem hx)))
      rwa [deriv_deriv_koenigs hε hf hp hfp (hmem hx), Complex.mul_re,
        (deriv_koenigs_ofReal hε hf hp hfp hx).1, mul_zero, sub_zero] at h
    -- `g' / G` has zero derivative, so `g' = c G` on `I`
    have hu : ∀ x ∈ I, HasDerivWithinAt (fun t => derivWithin g I t / G t) 0 I x := by
      intro x hx
      have h1 : HasDerivWithinAt (derivWithin g I) ((hatH f x).re * derivWithin g I x) I x := by
        rw [← hODE x hx]
        exact (hg' x hx).hasDerivWithinAt
      convert h1.div (hGderiv x hx).hasDerivWithinAt (hGpos x hx).ne' using 1
      ring
    have hg'eq : ∀ x ∈ I, derivWithin g I x = c * G x := by
      intro x hx
      have h := eq_of_hasDerivWithinAt_zero_I hu hx hp
      rw [hGp, div_one, div_eq_iff (hGpos x hx).ne'] at h
      exact h
    -- `g - c Re ĝ` has zero derivative, so `g = g(p) + c Re ĝ` on `I`
    have hv : ∀ x ∈ I, HasDerivWithinAt (fun t => g t - c * (koenigs f p t).re) 0 I x := by
      intro x hx
      have h := (hg x hx).hasDerivWithinAt.sub ((hkre x hx).hasDerivWithinAt.const_mul c)
      rwa [hg'eq x hx, sub_self] at h
    have hgeq : ∀ x ∈ I, g x = g p + c * (koenigs f p x).re := by
      intro x hx
      have h := eq_of_hasDerivWithinAt_zero_I hv hx hp
      rw [koenigs_self hε hf hp hfp, Complex.zero_re, mul_zero, sub_zero] at h
      linarith
    -- `ĝ ∘ f = f'(p) ĝ`
    have hy : (f x).re ∈ I := hf.re_mem_I x hx
    have hfx : (((f x).re : ℝ) : ℂ) = f x := Complex.ext (by simp)
      (by simp [hf.im_eq_zero x (ofReal_mem_nbhd (by linarith) hx)])
    have hkfx : (koenigs f p (f x).re).re = (deriv f p).re * (koenigs f p x).re := by
      rw [hfx, koenigs_comp hε hf hp hfp (hmem hx), Complex.mul_re,
        im_koenigs_ofReal hε hf hp hfp (hmem hx), mul_zero, sub_zero]
    rw [hgeq _ hy, hkfx, hgeq x hx]
    ring

end AnalyticESC
