module

public import AnalyticESC.Basic

@[expose] public section

/-!
# The classes `S^ω_ε(I)` and `S^ω(I)`

The inclusion `f(cl B_ε) ⊆ B_ε` in condition (B) of the class `S^ω_ε(I)` follows from the other
conditions. Hence the classes `S^ω_ε(I)` decrease as `ε` increases, and their union `S^ω(I)` is
described by conditions on `[0,1]`.
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-- Every point of `cl B_ε` lies within distance `ε` of a point of `I`. -/
private theorem exists_mem_I_norm_sub_le {ε : ℝ} (hε : 0 ≤ ε) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    ∃ x ∈ I, ‖z - x‖ ≤ ε := by
  have hz' := closure_thickening_subset_cthickening ε _ hz
  rw [isCompact_image_I.cthickening_eq_biUnion_closedBall hε] at hz'
  obtain ⟨_, ⟨x, hx, rfl⟩, hzx⟩ := mem_iUnion₂.1 hz'
  exact ⟨x, hx, mem_closedBall_iff_norm.1 hzx⟩

/-- A map complex analytic on `B_{2ε}`, real at the real points of `B_{2ε}`, with
`f(I) ⊆ I` and `0 < |f'| < 1` on `cl B_ε`, lies in `S^ω_ε(I)`. -/
theorem InClass.of_deriv {ε : ℝ} (hε : 0 < ε) {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (nbhd (2 * ε)))
    (him : ∀ x : ℝ, (x : ℂ) ∈ nbhd (2 * ε) → (f x).im = 0)
    (hI : ∀ x ∈ I, (f x).re ∈ I)
    (hne : ∀ z ∈ closure (nbhd ε), deriv f z ≠ 0)
    (hlt : ∀ z ∈ closure (nbhd ε), ‖deriv f z‖ < 1) : InClass ε f := by
  refine ⟨hd, him, hI, ?_, hne, hlt⟩
  have hsub : closure (nbhd ε) ⊆ nbhd (2 * ε) := closure_nbhd_subset (by linarith)
  -- `|f'|` attains its maximum `c < 1` on the compact set `cl B_ε`
  have hcont : ContinuousOn (fun z => ‖deriv f z‖) (closure (nbhd ε)) :=
    ((hd.deriv (isOpen_nbhd _)).continuousOn.mono hsub).norm
  obtain ⟨w, hw, hmax⟩ := (isCompact_closure_nbhd ε).exists_isMaxOn
    ⟨0, zero_mem_closure_nbhd hε⟩ hcont
  have hc : ‖deriv f w‖ < 1 := hlt w hw
  intro z hz
  obtain ⟨x, hx, hzx⟩ := exists_mem_I_norm_sub_le hε.le hz
  have hxcl : (x : ℂ) ∈ closure (nbhd ε) := subset_closure (ofReal_mem_nbhd hε hx)
  -- the mean value inequality on the convex set `cl B_ε`
  have hmv : ‖f z - f x‖ ≤ ‖deriv f w‖ * ‖z - x‖ :=
    (convex_nbhd ε).closure.norm_image_sub_le_of_norm_deriv_le
      (fun y hy => hd.differentiableAt ((isOpen_nbhd _).mem_nhds (hsub hy)))
      (fun y hy => hmax hy) hxcl hz
  -- `f(x)` is the real point `(f x).re` of `I`
  have hfx : f x = ((f x).re : ℂ) :=
    Complex.ext rfl (by simp [him x (ofReal_mem_nbhd (by linarith) hx)])
  refine ball_subset_nbhd (hI x hx) (mem_ball_iff_norm.2 ?_)
  rw [← hfx]
  calc ‖f z - f x‖ ≤ ‖deriv f w‖ * ‖z - x‖ := hmv
    _ ≤ ‖deriv f w‖ * ε := mul_le_mul_of_nonneg_left hzx (norm_nonneg _)
    _ < 1 * ε := mul_lt_mul_of_pos_right hc hε
    _ = ε := one_mul ε

/-- Nesting of the classes: `S^ω_ε(I) ⊆ S^ω_{ε'}(I)` for `0 < ε' ≤ ε`. -/
theorem InClass.mono {ε ε' : ℝ} {f : ℂ → ℂ} (h : InClass ε f) (hε' : 0 < ε') (hle : ε' ≤ ε) :
    InClass ε' f := by
  have h2 : nbhd (2 * ε') ⊆ nbhd (2 * ε) := nbhd_mono (by linarith)
  have hcl : closure (nbhd ε') ⊆ closure (nbhd ε) := closure_mono (nbhd_mono hle)
  exact InClass.of_deriv hε' (h.differentiableOn.mono h2) (fun x hx => h.im_eq_zero x (h2 hx))
    h.re_mem_I (fun z hz => h.deriv_ne_zero z (hcl hz))
    (fun z hz => h.norm_deriv_lt_one z (hcl hz))

/-- The direction used for perturbations: a map complex analytic on an open
neighbourhood `U` of `I`, real at the real points of `U`, with `f(I) ⊆ I` and `0 < |f'| < 1` on
`I`, lies in `S^ω_ε(I)` for some `ε > 0`. -/
theorem exists_inClass {U : Set ℂ} (hU : IsOpen U) (hIU : ((↑) : ℝ → ℂ) '' I ⊆ U) {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f U) (him : ∀ x : ℝ, (x : ℂ) ∈ U → (f x).im = 0)
    (hI : ∀ x ∈ I, (f x).re ∈ I) (hne : ∀ x ∈ I, deriv f x ≠ 0)
    (hlt : ∀ x ∈ I, ‖deriv f x‖ < 1) : ∃ ε > 0, InClass ε f := by
  -- the open set `{z ∈ U : 0 < |f'(z)| < 1}` contains the compact set `I`
  set V := U ∩ deriv f ⁻¹' ({0}ᶜ ∩ ball 0 1)
  have hV : IsOpen V := (hd.deriv hU).continuousOn.isOpen_inter_preimage hU
    (isOpen_compl_singleton.inter isOpen_ball)
  have hIV : ((↑) : ℝ → ℂ) '' I ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hIU (mem_image_of_mem _ hx), hne x hx, mem_ball_zero_iff.2 (hlt x hx)⟩
  obtain ⟨δ, hδ, hδV⟩ := isCompact_image_I.exists_cthickening_subset_open hV hIV
  obtain ⟨δ', hδ', hδ'U⟩ := isCompact_image_I.exists_cthickening_subset_open hU hIU
  set ε := min δ (δ' / 2)
  have hε : 0 < ε := lt_min hδ (half_pos hδ')
  have h2 : nbhd (2 * ε) ⊆ U := fun z hz =>
    hδ'U (thickening_subset_cthickening_of_le (by linarith [min_le_right δ (δ' / 2)]) _ hz)
  have hcl : closure (nbhd ε) ⊆ V := fun z hz =>
    hδV (cthickening_mono (min_le_left _ _) _ (closure_thickening_subset_cthickening ε _ hz))
  exact ⟨ε, hε, InClass.of_deriv hε (hd.mono h2) (fun x hx => him x (h2 hx)) hI
    (fun z hz => (hcl hz).2.1) (fun z hz => mem_ball_zero_iff.1 (hcl hz).2.2)⟩

/-- `S^ω(I)` consists of the maps complex analytic on an open neighbourhood of
`I`, real at its real points, with `f(I) ⊆ I` and `0 < |f'| < 1` on `I`. -/
theorem exists_inClass_iff {f : ℂ → ℂ} :
    (∃ ε > 0, InClass ε f) ↔ ∃ U : Set ℂ, IsOpen U ∧ ((↑) : ℝ → ℂ) '' I ⊆ U ∧
      DifferentiableOn ℂ f U ∧ (∀ x : ℝ, (x : ℂ) ∈ U → (f x).im = 0) ∧
      (∀ x ∈ I, (f x).re ∈ I) ∧ ∀ x ∈ I, deriv f x ≠ 0 ∧ ‖deriv f x‖ < 1 := by
  constructor
  · rintro ⟨ε, hε, h⟩
    have hx : ∀ x ∈ I, (x : ℂ) ∈ closure (nbhd ε) := fun x hx =>
      subset_closure (ofReal_mem_nbhd hε hx)
    refine ⟨nbhd (2 * ε), isOpen_nbhd _, ?_, h.differentiableOn, h.im_eq_zero, h.re_mem_I,
      fun x hxI => ⟨h.deriv_ne_zero _ (hx x hxI), h.norm_deriv_lt_one _ (hx x hxI)⟩⟩
    rintro _ ⟨x, hxI, rfl⟩
    exact ofReal_mem_nbhd (by linarith) hxI
  · rintro ⟨U, hU, hIU, hd, him, hI, hder⟩
    exact exists_inClass hU hIU hd him hI (fun x hx => (hder x hx).1) fun x hx => (hder x hx).2

/-- Finitely many maps of `S^ω(I)` lie in a common class `S^ω_ε(I)`. -/
theorem exists_inClass_forall {N : ℕ} {f : Fin N → ℂ → ℂ}
    (h : ∀ i, ∃ ε > 0, InClass ε (f i)) : ∃ ε > 0, ∀ i, InClass ε (f i) := by
  choose ε hε hf using h
  rcases isEmpty_or_nonempty (Fin N) with hN | hN
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · obtain ⟨j, hj⟩ := Finite.exists_min ε
    exact ⟨ε j, hε j, fun i => (hf i).mono (hε j) (hj i)⟩

namespace IFS

variable {N : ℕ} {ε : ℝ}

/-- An IFS of `𝔖_N(ε)` as an IFS of `𝔖_N(ε')` for `0 < ε' ≤ ε`. -/
def restrict (Φ : IFS N ε) {ε' : ℝ} (hε' : 0 < ε') (hle : ε' ≤ ε) : IFS N ε' :=
  ⟨Φ.f, hε', fun i => (Φ.inClass i).mono hε' hle⟩

end IFS

end AnalyticESC
