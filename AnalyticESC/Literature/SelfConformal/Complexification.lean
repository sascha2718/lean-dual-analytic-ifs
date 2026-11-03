module

public import AnalyticESC.Literature.SelfConformal.Distortion
public import AnalyticESC.Dimension.Rapaport

@[expose] public section

/-!
# Complexification of a real analytic IFS

A real map that is analytic on a neighbourhood of `I = [0,1]` extends holomorphically to a complex
neighbourhood of `I`. For a system satisfying `AnalyticESC.RapaportHyp φ` this gives an analytic
IFS `AnalyticESC.IFS N ε` in the sense of Bárány–Kolossváry–Troscheit whose real restriction is
`φ`, as used in the proof of Lemma 2.1(2) of A. Rapaport, *Dimension of self-conformal measures
associated to an exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2.

## Main declarations

* `complexify`, `radius_complexify`: the complexification of a real one-variable power series.
* `exists_holomorphic_extension`: a real map analytic on a neighbourhood of `I` has a holomorphic
  extension to the open `ε`-neighbourhood `AnalyticESC.nbhd ε` of `I` in `ℂ`.
* `exists_IFS`: a system with `RapaportHyp φ` is the real restriction of an
  `AnalyticESC.IFS N ε`, with `ε ≤ ‖Φ_i'‖ ≤ 1 - ε` on the closed `ε`-neighbourhood.

Copied from the library `FractalGeometry` (module `FractalGeometry.SelfConformal.Complexification`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.SelfConformal

open MeasureTheory Set Filter Topology Metric
open AnalyticESC (I realComp RapaportHyp IsProbVec nbhd)
open scoped ENNReal NNReal

variable {N : ℕ} {φ : Fin N → ℝ → ℝ}

/-! ### Complexification of real power series -/

/-- The complexification `∑ (a_n : ℂ) z^n` of a real power series `∑ a_n x^n`. -/
noncomputable def complexify (P : FormalMultilinearSeries ℝ ℝ ℝ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ fun n => ((P.coeff n : ℝ) : ℂ)

/-- The complexification has the same coefficient norms. -/
theorem norm_complexify (P : FormalMultilinearSeries ℝ ℝ ℝ) (n : ℕ) :
    ‖complexify P n‖ = ‖P n‖ := by
  rw [complexify, FormalMultilinearSeries.ofScalars_norm, P.norm_apply_eq_norm_coef,
    Complex.norm_real]

/-- The complexification has the same radius of convergence. -/
theorem radius_complexify (P : FormalMultilinearSeries ℝ ℝ ℝ) :
    (complexify P).radius = P.radius := by
  simp only [FormalMultilinearSeries.radius, norm_complexify]

/-- At real points the complexified terms are the real terms. -/
theorem complexify_apply_ofReal (P : FormalMultilinearSeries ℝ ℝ ℝ) (n : ℕ) (t : ℝ) :
    (complexify P n fun _ => (t : ℂ)) = ((P n fun _ => t : ℝ) : ℂ) := by
  rw [complexify, FormalMultilinearSeries.ofScalars_apply_eq, P.apply_eq_pow_smul_coeff]
  simp [smul_eq_mul, mul_comm]

/-- The local holomorphic extension given by a real power series: `z ↦ ∑ a_n (z - x)^n` is
holomorphic on the complex disc of convergence and equals `f` at the real points of the disc. -/
theorem HasFPowerSeriesOnBall.complexify_sum {f : ℝ → ℝ} {P : FormalMultilinearSeries ℝ ℝ ℝ}
    {x : ℝ} {ρ : ℝ} (hf : HasFPowerSeriesOnBall f P x (ENNReal.ofReal ρ)) :
    DifferentiableOn ℂ (fun z => (complexify P).sum (z - x)) (ball (x : ℂ) ρ) ∧
      ∀ t : ℝ, |t - x| < ρ → (complexify P).sum ((t : ℂ) - x) = f t := by
  have hrad : ENNReal.ofReal ρ ≤ (complexify P).radius := (radius_complexify P).symm ▸ hf.r_le
  have hpos : 0 < (complexify P).radius := hf.r_pos.trans_le hrad
  have hsum := (complexify P).hasFPowerSeriesOnBall hpos
  have hmem : ∀ z ∈ ball (x : ℂ) ρ, z - x ∈ eball (0 : ℂ) (complexify P).radius := by
    intro z hz
    refine eball_subset_eball hrad ?_
    rw [eball_ofReal, mem_ball, dist_zero_right, ← dist_eq_norm]
    exact hz
  refine ⟨?_, fun t ht => ?_⟩
  · exact hsum.differentiableOn.comp (differentiableOn_id.sub_const _) hmem
  · have hreal : HasSum (fun n => P n fun _ => t - x) (f t) := by
      have := hf.hasSum (y := t - x) (by
        rw [eball_ofReal, mem_ball, dist_zero_right, Real.norm_eq_abs]
        exact ht)
      rwa [add_sub_cancel] at this
    have hcplx := (complexify P).hasSum (x := ((t - x : ℝ) : ℂ)) (by
      refine eball_subset_eball hrad ?_
      rw [eball_ofReal, mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      exact ht)
    simp_rw [complexify_apply_ofReal] at hcplx
    have h := hcplx.unique (Complex.hasSum_ofReal.2 hreal)
    rw [← h]
    push_cast
    rfl

/-! ### Gluing the local extensions -/

/-- The inclusion `ℝ → ℂ` maps punctured neighbourhoods into punctured neighbourhoods. -/
private theorem tendsto_ofReal_nhdsNE (c : ℝ) :
    Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] c) (𝓝[≠] (c : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  simpa using hx

/-- `dist (t : ℂ) (x : ℂ) = |t - x|`. -/
private theorem dist_ofReal (t x : ℝ) : dist (t : ℂ) (x : ℂ) = |t - x| := by
  rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- `|Re z - x| ≤ |z - x|` for real `x`. -/
private theorem dist_re_le (z : ℂ) (x : ℝ) : dist ((z.re : ℝ) : ℂ) (x : ℂ) ≤ dist z x := by
  rw [dist_ofReal, Complex.dist_eq]
  have : z.re - x = (z - x).re := by simp
  rw [this]
  exact Complex.abs_re_le_norm _

/-- **Holomorphic extension**: a real map analytic on a neighbourhood of `I` extends to a map
holomorphic on the open `ε`-neighbourhood `{z : ∃ x ∈ I, |z - x| < ε}` of `I` in `ℂ`, for some
`ε > 0`. -/
theorem exists_holomorphic_extension {f : ℝ → ℝ} (hf : AnalyticOnNhd ℝ f I) :
    ∃ ε > 0, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (nbhd ε) ∧
      ∀ x : ℝ, (x : ℂ) ∈ nbhd ε → F x = f x := by
  have hloc : ∀ x : I, ∃ P : FormalMultilinearSeries ℝ ℝ ℝ, ∃ ρ : ℝ, 0 < ρ ∧
      HasFPowerSeriesOnBall f P x (ENNReal.ofReal ρ) := by
    intro x
    obtain ⟨P, r, hr⟩ := hf x x.2
    obtain ⟨ρ, hρ0, hρr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hr.r_pos
    refine ⟨P, ρ, by exact_mod_cast hρ0, hr.mono (by simpa using hρ0) ?_⟩
    rw [ENNReal.ofReal_coe_nnreal]
    exact hρr.le
  choose P ρ hρ hP using hloc
  set G : I → ℂ → ℂ := fun x z => (complexify (P x)).sum (z - (x : ℝ)) with hG
  have hGd : ∀ x : I, DifferentiableOn ℂ (G x) (ball ((x : ℝ) : ℂ) (ρ x)) := fun x =>
    (HasFPowerSeriesOnBall.complexify_sum (hP x)).1
  have hGf : ∀ x : I, ∀ t : ℝ, |t - x| < ρ x → G x t = f t := fun x =>
    (HasFPowerSeriesOnBall.complexify_sum (hP x)).2
  have hcompat : ∀ x y : I, EqOn (G x) (G y)
      (ball ((x : ℝ) : ℂ) (ρ x) ∩ ball ((y : ℝ) : ℂ) (ρ y)) := by
    intro x y z hz
    set U := ball ((x : ℝ) : ℂ) (ρ x) ∩ ball ((y : ℝ) : ℂ) (ρ y) with hU
    have hUo : IsOpen U := isOpen_ball.inter isOpen_ball
    have hUc : IsPreconnected U := ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
    set c : ℝ := z.re
    have hc : (c : ℂ) ∈ U :=
      ⟨(dist_re_le z x).trans_lt hz.1, (dist_re_le z y).trans_lt hz.2⟩
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] c, G x t = G y t := by
      have h1 : ∀ᶠ t : ℝ in 𝓝 c, (t : ℂ) ∈ U :=
        Complex.continuous_ofReal.continuousAt.preimage_mem_nhds (hUo.mem_nhds hc)
      filter_upwards [nhdsWithin_le_nhds h1] with t ht
      rw [hGf x t (by rw [← dist_ofReal]; exact ht.1), hGf y t (by rw [← dist_ofReal]; exact ht.2)]
    have hfreq : ∃ᶠ w in 𝓝[≠] (c : ℂ), G x w = G y w :=
      (tendsto_ofReal_nhdsNE c).frequently hev.frequently
    refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq ?_ ?_ hUc hc hfreq hz
    · exact ((hGd x).mono inter_subset_left).analyticOnNhd hUo
    · exact ((hGd y).mono inter_subset_right).analyticOnNhd hUo
  set U := ⋃ x : I, ball ((x : ℝ) : ℂ) (ρ x) with hU
  have hUo : IsOpen U := isOpen_iUnion fun _ => isOpen_ball
  classical
  let F : ℂ → ℂ := fun z => if h : ∃ x : I, z ∈ ball ((x : ℝ) : ℂ) (ρ x) then G h.choose z else 0
  have hFG : ∀ x : I, ∀ z ∈ ball ((x : ℝ) : ℂ) (ρ x), F z = G x z := by
    intro x z hz
    have h : ∃ x : I, z ∈ ball ((x : ℝ) : ℂ) (ρ x) := ⟨x, hz⟩
    simp only [F, h, ↓reduceDIte]
    exact hcompat _ _ ⟨h.choose_spec, hz⟩
  have hFd : DifferentiableOn ℂ F U := by
    intro z hz
    obtain ⟨x, hx⟩ := mem_iUnion.1 hz
    have heq : G x =ᶠ[𝓝 z] F := by
      filter_upwards [isOpen_ball.mem_nhds hx] with w hw
      exact (hFG x w hw).symm
    exact (((hGd x).differentiableAt (isOpen_ball.mem_nhds hx)).congr_of_eventuallyEq
      heq.symm).differentiableWithinAt
  have hKU : ((↑) : ℝ → ℂ) '' I ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (hρ _)⟩
  obtain ⟨ε, hε, hεU⟩ := AnalyticESC.isCompact_image_I.exists_thickening_subset_open hUo hKU
  refine ⟨ε, hε, F, hFd.mono hεU, fun t ht => ?_⟩
  obtain ⟨x, hx⟩ := mem_iUnion.1 (hεU ht)
  rw [hFG x t hx]
  exact hGf x t (by rw [← dist_ofReal]; exact hx)

/-! ### The system as an analytic IFS in the sense of `AnalyticESC` -/

/-- The complex derivative of a holomorphic extension at a real point is the real derivative. -/
theorem deriv_extension_ofReal {f : ℝ → ℝ} {F : ℂ → ℂ} {ε : ℝ}
    (hF : DifferentiableOn ℂ F (nbhd ε)) (hFf : ∀ x : ℝ, (x : ℂ) ∈ nbhd ε → F x = f x)
    {x : ℝ} (hx : (x : ℂ) ∈ nbhd ε) : deriv F x = ((deriv f x : ℝ) : ℂ) := by
  have hU := AnalyticESC.isOpen_nbhd ε
  have hre : (deriv F x).re = deriv f x := by
    have h := AnalyticESC.hasDerivAt_re_ofReal (hF.differentiableAt (hU.mem_nhds hx))
    have heq : (fun t : ℝ => (F t).re) =ᶠ[𝓝 x] f := by
      filter_upwards [(AnalyticESC.isOpen_setOf_ofReal_mem hU).mem_nhds hx] with t ht
      rw [hFf t ht, Complex.ofReal_re]
    exact (h.congr_of_eventuallyEq heq.symm).deriv.symm
  have him : (deriv F x).im = 0 :=
    AnalyticESC.im_deriv_eq_zero hU hF (fun t ht => by rw [hFf t ht, Complex.ofReal_im]) hx
  exact Complex.ext (by simp [hre]) (by simp [him])

/-- **The bridge to `AnalyticESC`**: a system satisfying `RapaportHyp φ` is the real restriction
of an analytic IFS `Φ : AnalyticESC.IFS N ε`: the holomorphic extensions `Φ_i` of the `φ_i` are
defined on the `2ε`-neighbourhood of `I`, map the closed `ε`-neighbourhood into the open one and
satisfy `ε ≤ ‖Φ_i'‖ ≤ 1 - ε` there. -/
theorem exists_IFS (hφ : RapaportHyp φ) :
    ∃ ε > 0, ∃ Φ : AnalyticESC.IFS N ε,
      (∀ i, ∀ x : ℝ, (x : ℂ) ∈ nbhd (2 * ε) → Φ.f i x = φ i x) ∧
      ∀ i, ∀ z ∈ closure (nbhd ε), ε ≤ ‖deriv (Φ.f i) z‖ ∧ ‖deriv (Φ.f i) z‖ ≤ 1 - ε := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨1, one_pos, ⟨Fin.elim0, one_pos, fun i => i.elim0⟩, fun i => i.elim0,
      fun i => i.elim0⟩
  have hext := fun i => exists_holomorphic_extension (hφ.analytic i)
  choose ε₀ hε₀ F hFd hFf using hext
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciInf_of_finite (f := ε₀)
  set ε₁ := ⨅ i, ε₀ i with hε₁_def
  have hε₁ : 0 < ε₁ := hi₀ ▸ hε₀ i₀
  have hε₁le : ∀ i, ε₁ ≤ ε₀ i := fun i => ciInf_le (Set.finite_range _).bddBelow i
  have hF1 : ∀ i, DifferentiableOn ℂ (F i) (nbhd ε₁) := fun i =>
    (hFd i).mono (AnalyticESC.nbhd_mono (hε₁le i))
  have hFf1 : ∀ i, ∀ x : ℝ, (x : ℂ) ∈ nbhd ε₁ → F i x = φ i x := fun i x hx =>
    hFf i x (AnalyticESC.nbhd_mono (hε₁le i) hx)
  have hU := AnalyticESC.isOpen_nbhd ε₁
  have hcont : ∀ i, ContinuousOn (deriv (F i)) (nbhd ε₁) := fun i =>
    ((hF1 i).analyticOnNhd hU).deriv.continuousOn
  have hcmin := cmin_pos hφ hN
  have hcmax := cmax_lt_one hφ
  set a := cmin φ / 2 with ha
  set b := (1 + cmax φ) / 2 with hb
  set V := ⋂ i, nbhd ε₁ ∩ deriv (F i) ⁻¹' {w : ℂ | a < ‖w‖ ∧ ‖w‖ < b} with hV
  have hVo : IsOpen V := isOpen_iInter_of_finite fun i =>
    (hcont i).isOpen_inter_preimage hU ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const))
  have hKV : ((↑) : ℝ → ℂ) '' I ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    refine mem_iInter.2 fun i => ⟨AnalyticESC.ofReal_mem_nbhd hε₁ hx, ?_⟩
    have hd := deriv_extension_ofReal (hF1 i) (hFf1 i) (AnalyticESC.ofReal_mem_nbhd hε₁ hx)
    simp only [mem_preimage, mem_ofPred_eq, hd, Complex.norm_real, Real.norm_eq_abs]
    exact ⟨by linarith [cmin_le_abs_deriv (φ := φ) i hx], by linarith [abs_deriv_le_cmax hφ i hx]⟩
  obtain ⟨δ, hδ, hδV⟩ := AnalyticESC.isCompact_image_I.exists_thickening_subset_open hVo hKV
  set ε := min (min (ε₁ / 2) (δ / 2)) (min a ((1 - cmax φ) / 2)) with hε_def
  have hεpos : 0 < ε :=
    lt_min (lt_min (half_pos hε₁) (half_pos hδ)) (lt_min (half_pos hcmin) (by linarith))
  have hε2 : 2 * ε ≤ ε₁ := by
    have : ε ≤ ε₁ / 2 := (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have hεδ : ε < δ :=
    lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (half_lt_self hδ)
  have hεa : ε ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hεb : ε ≤ (1 - cmax φ) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hclV : closure (nbhd ε) ⊆ V := (AnalyticESC.closure_nbhd_subset hεδ).trans hδV
  have hbound : ∀ i, ∀ z ∈ closure (nbhd ε), a < ‖deriv (F i) z‖ ∧ ‖deriv (F i) z‖ < b :=
    fun i z hz => (mem_iInter.1 (hclV hz) i).2
  have hcl1 : closure (nbhd ε) ⊆ nbhd ε₁ := fun z hz => (mem_iInter.1 (hclV hz) i₀).1
  have hmaps : ∀ i, MapsTo (F i) (closure (nbhd ε)) (nbhd ε) := by
    intro i z hz
    have hz' : z ∈ cthickening ε (((↑) : ℝ → ℂ) '' I) :=
      closure_thickening_subset_cthickening ε _ hz
    rw [AnalyticESC.isCompact_image_I.cthickening_eq_biUnion_closedBall hεpos.le] at hz'
    obtain ⟨_, ⟨x, hx, rfl⟩, hzx⟩ := mem_iUnion₂.1 hz'
    have hball : closedBall (x : ℂ) ε ⊆ closure (nbhd ε) := by
      rw [← closure_ball (x : ℂ) hεpos.ne']
      exact closure_mono (AnalyticESC.ball_subset_nbhd hx)
    have hmvt := (convex_closedBall (x : ℂ) ε).norm_image_sub_le_of_norm_deriv_le
      (f := F i) (C := b)
      (fun w hw => (hF1 i).differentiableAt (hU.mem_nhds (hcl1 (hball hw))))
      (fun w hw => (hbound i w (hball hw)).2.le) (mem_closedBall_self hεpos.le) hzx
    rw [hFf1 i x (AnalyticESC.ofReal_mem_nbhd hε₁ hx)] at hmvt
    refine AnalyticESC.ball_subset_nbhd (hφ.mapsTo i hx) ?_
    rw [mem_ball, dist_eq_norm]
    have hzx' : ‖z - x‖ ≤ ε := by rwa [← dist_eq_norm, ← mem_closedBall]
    have hb1 : b < 1 := by linarith
    have hb0 : 0 ≤ b := by linarith [cmax_nonneg (φ := φ)]
    calc ‖F i z - φ i x‖ ≤ b * ‖z - x‖ := hmvt
      _ ≤ b * ε := mul_le_mul_of_nonneg_left hzx' hb0
      _ < ε := by nlinarith
  refine ⟨ε, hεpos, ⟨F, hεpos, fun i => ⟨(hF1 i).mono (AnalyticESC.nbhd_mono hε2),
    fun x hx => ?_, fun x hx => ?_, hmaps i, fun z hz => ?_, fun z hz => ?_⟩⟩,
    fun i x hx => hFf1 i x (AnalyticESC.nbhd_mono hε2 hx), fun i z hz => ⟨?_, ?_⟩⟩
  · rw [hFf1 i x (AnalyticESC.nbhd_mono hε2 hx), Complex.ofReal_im]
  · rw [hFf1 i x (AnalyticESC.ofReal_mem_nbhd hε₁ hx), Complex.ofReal_re]
    exact hφ.mapsTo i hx
  · exact norm_pos_iff.1 ((half_pos hcmin).trans (hbound i z hz).1)
  · exact (hbound i z hz).2.trans (by linarith)
  · exact hεa.trans (hbound i z hz).1.le
  · have := (hbound i z hz).2
    linarith

/-! ### Complex bounded distortion -/

/-- `Φ_i'` is Lipschitz on `B_ε`, uniformly in `i`. -/
theorem exists_lipschitz_deriv_f {ε : ℝ} (Φ : AnalyticESC.IFS N ε) :
    ∃ M, 0 ≤ M ∧ ∀ i, ∀ z ∈ nbhd ε, ∀ w ∈ nbhd ε,
      ‖deriv (Φ.f i) z - deriv (Φ.f i) w‖ ≤ M * ‖z - w‖ := by
  have hU := AnalyticESC.isOpen_nbhd (2 * ε)
  have han : ∀ i, AnalyticOnNhd ℂ (deriv (Φ.f i)) (nbhd (2 * ε)) := fun i =>
    ((Φ.differentiableOn_f i).analyticOnNhd hU).deriv
  have hb : ∀ i, ∃ M, ∀ z ∈ closure (nbhd ε), ‖deriv (deriv (Φ.f i)) z‖ ≤ M := fun i =>
    (AnalyticESC.isCompact_closure_nbhd ε).exists_bound_of_continuousOn
      ((han i).deriv.continuousOn.mono (AnalyticESC.IFS.closure_nbhd_subset_two (ε := ε)))
  choose M hM using hb
  obtain ⟨M₀, hM₀⟩ := (Set.finite_range M).bddAbove
  refine ⟨max M₀ 0, le_max_right _ _, fun i z hz w hw => ?_⟩
  have h := (AnalyticESC.convex_nbhd ε).norm_image_sub_le_of_norm_deriv_le
    (f := deriv (Φ.f i)) (C := max M₀ 0)
    (fun y hy => ((han i) y (AnalyticESC.IFS.nbhd_subset_two hy)).differentiableAt)
    (fun y hy => (hM i y (subset_closure hy)).trans
      ((hM₀ (mem_range_self i)).trans (le_max_left _ _))) hw hz
  exact h

/-- Points of `B_ε` are at distance less than `1 + 2ε`. -/
theorem norm_sub_lt_of_mem_nbhd {ε : ℝ} {z w : ℂ} (hz : z ∈ nbhd ε) (hw : w ∈ nbhd ε) :
    ‖z - w‖ < 1 + 2 * ε := by
  obtain ⟨_, ⟨x, hx, rfl⟩, hzx⟩ := mem_thickening_iff.1 hz
  obtain ⟨_, ⟨y, hy, rfl⟩, hwy⟩ := mem_thickening_iff.1 hw
  have hxy : dist (x : ℂ) (y : ℂ) ≤ 1 := by
    rw [dist_ofReal]
    exact abs_sub_le_one_of_mem_I hx hy
  rw [← dist_eq_norm]
  calc dist z w ≤ dist z x + dist (x : ℂ) y + dist (y : ℂ) w := dist_triangle4 _ _ _ _
    _ < ε + 1 + ε := by
        rw [dist_comm (y : ℂ) w]
        linarith
    _ = 1 + 2 * ε := by ring

/-- **Complex bounded distortion**: for an analytic IFS `Φ` there is `C₀ ≥ 1` with
`‖Φ_w'(z)‖ ≤ C₀ ‖Φ_w'(z')‖` for every finite word `w` and `z, z' ∈ B_ε`. -/
theorem exists_complex_distortion {ε : ℝ} (Φ : AnalyticESC.IFS N ε) :
    ∃ C₀, 1 ≤ C₀ ∧ ∀ (w : List (Fin N)), ∀ z ∈ nbhd ε, ∀ z' ∈ nbhd ε,
      ‖deriv (Φ.comp w) z‖ ≤ C₀ * ‖deriv (Φ.comp w) z'‖ := by
  obtain ⟨M, hM0, hM⟩ := exists_lipschitz_deriv_f Φ
  set K := M / Φ.cmin with hK
  set D := 1 + 2 * ε with hD
  have hK0 : 0 ≤ K := div_nonneg hM0 Φ.cmin_nonneg
  have hD0 : 0 ≤ D := by have := Φ.ε_pos; linarith
  have hc0 := Φ.cmax_nonneg
  have hc1 := Φ.cmax_lt_one
  have key : ∀ (w : List (Fin N)), ∀ z ∈ nbhd ε, ∀ z' ∈ nbhd ε,
      ‖deriv (Φ.comp w) z‖ ≤
        Real.exp (K * D * ∑ k ∈ Finset.range w.length, Φ.cmax ^ k) *
          ‖deriv (Φ.comp w) z'‖ := by
    intro w
    induction w with
    | nil =>
      intro z _ z' _
      simp [AnalyticESC.IFS.comp]
    | cons i v ih =>
      intro z hz z' hz'
      have hN : 0 < N := Nat.pos_of_ne_zero fun h => by subst h; exact i.elim0
      have ha := Φ.mapsTo_comp v hz
      have hb := Φ.mapsTo_comp v hz'
      rw [Φ.deriv_comp_cons i v (subset_closure hz), Φ.deriv_comp_cons i v (subset_closure hz'),
        norm_mul, norm_mul]
      have hcmin := Φ.cmin_pos hN
      have hFb := Φ.cmin_le_norm_deriv i (subset_closure hb)
      have hab : ‖Φ.comp v z - Φ.comp v z'‖ ≤ Φ.cmax ^ v.length * D :=
        (Φ.norm_comp_sub_le v hz hz').trans (mul_le_mul_of_nonneg_left
          (norm_sub_lt_of_mem_nbhd hz hz').le (pow_nonneg hc0 _))
      have h1 : ‖deriv (Φ.f i) (Φ.comp v z)‖ ≤
          Real.exp (K * D * Φ.cmax ^ v.length) * ‖deriv (Φ.f i) (Φ.comp v z')‖ := by
        have hlip := hM i _ ha _ hb
        have h2 : ‖deriv (Φ.f i) (Φ.comp v z)‖ ≤ ‖deriv (Φ.f i) (Φ.comp v z')‖ +
            M * ‖Φ.comp v z - Φ.comp v z'‖ := by
          have := norm_sub_norm_le (deriv (Φ.f i) (Φ.comp v z)) (deriv (Φ.f i) (Φ.comp v z'))
          linarith
        have h3 : M * ‖Φ.comp v z - Φ.comp v z'‖ ≤
            K * (Φ.cmax ^ v.length * D) * ‖deriv (Φ.f i) (Φ.comp v z')‖ := by
          rw [hK, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hcmin]
          calc M * ‖Φ.comp v z - Φ.comp v z'‖ * Φ.cmin
              ≤ M * (Φ.cmax ^ v.length * D) * ‖deriv (Φ.f i) (Φ.comp v z')‖ := by
                gcongr
          _ = _ := by ring
        have h4 : 1 + K * D * Φ.cmax ^ v.length ≤ Real.exp (K * D * Φ.cmax ^ v.length) := by
          have := Real.add_one_le_exp (K * D * Φ.cmax ^ v.length)
          linarith
        calc ‖deriv (Φ.f i) (Φ.comp v z)‖
            ≤ (1 + K * D * Φ.cmax ^ v.length) * ‖deriv (Φ.f i) (Φ.comp v z')‖ := by
              nlinarith
          _ ≤ _ := mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
      have h5 := ih z hz z' hz'
      rw [List.length_cons, Finset.sum_range_succ, mul_add, Real.exp_add]
      calc ‖deriv (Φ.f i) (Φ.comp v z)‖ * ‖deriv (Φ.comp v) z‖
          ≤ (Real.exp (K * D * Φ.cmax ^ v.length) * ‖deriv (Φ.f i) (Φ.comp v z')‖) *
            (Real.exp (K * D * ∑ k ∈ Finset.range v.length, Φ.cmax ^ k) *
              ‖deriv (Φ.comp v) z'‖) :=
            mul_le_mul h1 h5 (norm_nonneg _) (by positivity)
        _ = _ := by ring
  refine ⟨Real.exp (K * D * (1 - Φ.cmax)⁻¹), Real.one_le_exp (by
    have : 0 ≤ (1 - Φ.cmax)⁻¹ := inv_nonneg.2 (by linarith)
    positivity), fun w z hz z' hz' => (key w z hz z' hz').trans ?_⟩
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _)
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hK0 hD0)
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := w.length) hc0 hc1
  rwa [← Finset.range_eq_Ico, pow_zero, one_div] at h

/-! ### Lemma 2.1(2): derivative bounds by Cauchy's estimate -/

/-- The compositions of `φ` and of the real maps of an extension `Φ` of `φ` agree at the real
points of `B_ε`. -/
theorem realComp_eq_realComp_realMap {ε : ℝ} {Φ : AnalyticESC.IFS N ε}
    (hΦ : ∀ i, ∀ x : ℝ, (x : ℂ) ∈ nbhd (2 * ε) → Φ.f i x = φ i x) (u : List (Fin N)) {x : ℝ}
    (hx : (x : ℂ) ∈ nbhd ε) : realComp φ u x = realComp Φ.realMap u x := by
  induction u with
  | nil => rfl
  | cons i u ih =>
    show φ i (realComp φ u x) = Φ.realMap i (realComp Φ.realMap u x)
    rw [ih]
    have hy : ((realComp Φ.realMap u x : ℝ) : ℂ) ∈ nbhd ε := by
      rw [Φ.realComp_realMap u hx]
      have h : (((Φ.comp u x).re : ℝ) : ℂ) = Φ.comp u x :=
        Complex.ext (by simp) (by simp [Φ.im_comp_ofReal u hx])
      rw [h]
      exact Φ.mapsTo_comp u hx
    rw [AnalyticESC.IFS.realMap, hΦ i _ (AnalyticESC.IFS.nbhd_subset_two hy), Complex.ofReal_re]

/-- **Lemma 2.1(2)** of Rapaport: there is `C > 1` with
`|φ_u^{(k)}(x)| ≤ k! C^k |φ_u'(0)|` for every word `u`, every `k ≥ 1` and every `x ∈ I`. The proof
extends the system to a complex neighbourhood of `I` (`exists_IFS`), applies complex bounded
distortion (`exists_complex_distortion`) and Cauchy's estimate. -/
theorem exists_iteratedDeriv_realComp_le (hφ : RapaportHyp φ) :
    ∃ C > 1, ∀ (u : List (Fin N)) (k : ℕ), 1 ≤ k → ∀ x ∈ I,
      |iteratedDeriv k (realComp φ u) x| ≤ k.factorial * C ^ k * |deriv (realComp φ u) 0| := by
  obtain ⟨ε, hε, Φ, hΦ, -⟩ := exists_IFS hφ
  obtain ⟨C₀, hC₀, hdist⟩ := exists_complex_distortion Φ
  have hU := AnalyticESC.isOpen_nbhd ε
  have h0 : ((0 : ℝ) : ℂ) ∈ nbhd ε := AnalyticESC.ofReal_mem_nbhd hε zero_mem_I
  set A := C₀ * (1 + ε / 2) with hA_def
  have hA : 1 ≤ A := one_le_mul_of_one_le_of_one_le hC₀ (by linarith)
  have hC : 1 < A * (2 / ε) + 1 := by
    have : 0 < A * (2 / ε) := by positivity
    linarith
  refine ⟨A * (2 / ε) + 1, hC, fun u k hk x hx => ?_⟩
  have hx' : (x : ℂ) ∈ nbhd ε := AnalyticESC.ofReal_mem_nbhd hε hx
  have hev : realComp φ u =ᶠ[𝓝 x] fun t : ℝ => (Φ.comp u t).re := by
    filter_upwards [(AnalyticESC.isOpen_setOf_ofReal_mem hU).mem_nhds hx'] with t ht
    exact (realComp_eq_realComp_realMap hΦ u ht).trans (Φ.realComp_realMap u ht)
  have hd0 : |deriv (realComp φ u) 0| = ‖deriv (Φ.comp u) ((0 : ℝ) : ℂ)‖ := by
    have hev' : realComp φ u =ᶠ[𝓝 (0 : ℝ)] realComp Φ.realMap u := by
      filter_upwards [(AnalyticESC.isOpen_setOf_ofReal_mem hU).mem_nhds h0] with t ht
      exact realComp_eq_realComp_realMap hΦ u ht
    rw [hev'.deriv_eq]
    exact Φ.abs_deriv_realComp_realMap u h0
  have hkx : iteratedDeriv k (realComp φ u) x = (iteratedDeriv k (Φ.comp u) x).re := by
    rw [(hev.iteratedDeriv k).eq_of_nhds]
    exact AnalyticESC.iteratedDeriv_re_ofReal hU (Φ.differentiableOn_comp u) k hx'
  set d := ‖deriv (Φ.comp u) ((0 : ℝ) : ℂ)‖ with hd
  set g : ℂ → ℂ := fun z => -Φ.comp u ((0 : ℝ) : ℂ) + Φ.comp u z with hg
  have hgk : iteratedDeriv k g x = iteratedDeriv k (Φ.comp u) x :=
    iteratedDeriv_const_add (by omega) _
  set R := ε / 2 with hR_def
  have hR : 0 < R := half_pos hε
  have hcl : closedBall (x : ℂ) R ⊆ nbhd ε :=
    (closedBall_subset_ball (half_lt_self hε)).trans (AnalyticESC.ball_subset_nbhd hx)
  have hgd : DiffContOnCl ℂ g (ball (x : ℂ) R) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hR.ne']
    exact ((Φ.differentiableOn_comp u).const_add _).mono hcl
  have hbound : ∀ z ∈ sphere (x : ℂ) R, ‖g z‖ ≤ A * d := by
    intro z hz
    have hzU : z ∈ nbhd ε := hcl (sphere_subset_closedBall hz)
    have hmvt := (AnalyticESC.convex_nbhd ε).norm_image_sub_le_of_norm_deriv_le
      (f := Φ.comp u) (C := C₀ * d)
      (fun w hw => Φ.differentiableAt_comp u (subset_closure hw))
      (fun w hw => hdist u w hw _ h0) h0 hzU
    have hz1 : ‖z - ((0 : ℝ) : ℂ)‖ ≤ 1 + ε / 2 := by
      rw [Complex.ofReal_zero, sub_zero]
      have h1 := norm_sub_norm_le z (x : ℂ)
      have h2 : ‖z - x‖ = R := mem_sphere_iff_norm.1 hz
      have h3 : ‖(x : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
        exact hx.2
      linarith
    calc ‖g z‖ = ‖Φ.comp u z - Φ.comp u ((0 : ℝ) : ℂ)‖ := by
          show ‖-Φ.comp u ((0 : ℝ) : ℂ) + Φ.comp u z‖ = _
          rw [neg_add_eq_sub]
      _ ≤ C₀ * d * ‖z - ((0 : ℝ) : ℂ)‖ := hmvt
      _ ≤ C₀ * d * (1 + ε / 2) := mul_le_mul_of_nonneg_left hz1 (by positivity)
      _ = A * d := by rw [hA_def]; ring
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR hgd hbound
  rw [hgk] at hcauchy
  rw [hkx, hd0]
  refine (Complex.abs_re_le_norm _).trans (hcauchy.trans ?_)
  have hpow : A * (2 / ε) ^ k ≤ (A * (2 / ε) + 1) ^ k :=
    calc A * (2 / ε) ^ k ≤ A ^ k * (2 / ε) ^ k :=
          mul_le_mul_of_nonneg_right (le_self_pow₀ hA (by omega)) (by positivity)
      _ = (A * (2 / ε)) ^ k := (mul_pow _ _ _).symm
      _ ≤ (A * (2 / ε) + 1) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
  have hRk : (k.factorial : ℝ) * (A * d) / R ^ k = k.factorial * (A * (2 / ε) ^ k) * d := by
    rw [hR_def, div_pow, div_pow]
    field_simp
  rw [hRk]
  have hk0 : (0 : ℝ) ≤ k.factorial := Nat.cast_nonneg _
  have hd0' : 0 ≤ d := norm_nonneg _
  calc (k.factorial : ℝ) * (A * (2 / ε) ^ k) * d
      ≤ k.factorial * (A * (2 / ε) + 1) ^ k * d := by gcongr
    _ = _ := rfl

/-! ### Taylor's theorem for the compositions -/

/-- `φ_u` is real analytic at the points of `I`. -/
theorem analyticAt_realComp (hφ : RapaportHyp φ) (u : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    AnalyticAt ℝ (realComp φ u) x := by
  induction u with
  | nil => exact analyticAt_id
  | cons i u ih =>
    show AnalyticAt ℝ (φ i ∘ realComp φ u) x
    exact (hφ.analytic i _ (mapsTo_realComp hφ u hx)).comp ih

/-- Lemma 2.1(2) together with **Taylor's theorem** (Lagrange remainder) for `φ_u` on `I`:
there is `C > 1` with `|φ_u^{(k)}(x)| ≤ k! C^k |φ_u'(0)|` for `k ≥ 1`, `x ∈ I`, and
`|φ_u(y) - ∑_{j ≤ k} φ_u^{(j)}(a) (y - a)^j / j!| ≤ |y - a|^{k+1} C^{k+1} |φ_u'(0)|` for
`a, y ∈ I`. -/
theorem exists_taylor_bounds (hφ : RapaportHyp φ) :
    ∃ C > 1, (∀ (u : List (Fin N)) (k : ℕ), 1 ≤ k → ∀ x ∈ I,
        |iteratedDeriv k (realComp φ u) x| ≤ k.factorial * C ^ k * |deriv (realComp φ u) 0|) ∧
      ∀ (u : List (Fin N)) (k : ℕ), ∀ a ∈ I, ∀ y ∈ I,
        |realComp φ u y - ∑ j ∈ Finset.range (k + 1),
          iteratedDeriv j (realComp φ u) a / j.factorial * (y - a) ^ j| ≤
        |y - a| ^ (k + 1) * C ^ (k + 1) * |deriv (realComp φ u) 0| := by
  obtain ⟨C, hC, hder⟩ := exists_iteratedDeriv_realComp_le hφ
  refine ⟨C, hC, hder, fun u k a ha y hy => ?_⟩
  rcases eq_or_ne a y with rfl | hay
  · simp [Finset.sum_range_succ']
  have huI : uIcc a y ⊆ I := uIcc_subset_Icc ha hy
  have hcd : ContDiffOn ℝ (k + 1) (realComp φ u) (uIcc a y) := fun z hz =>
    (analyticAt_realComp hφ u (huI hz)).contDiffAt.contDiffWithinAt
  obtain ⟨x', hx', htay⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hay hcd
  have hsum : taylorWithinEval (realComp φ u) k (uIcc a y) a y = ∑ j ∈ Finset.range (k + 1),
      iteratedDeriv j (realComp φ u) a / j.factorial * (y - a) ^ j := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hay)
      (analyticAt_realComp hφ u ha).contDiffAt left_mem_uIcc, smul_eq_mul]
    ring
  rw [← hsum, htay, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  have hx'I : x' ∈ I := huI (uIoo_subset_uIcc_self hx')
  have hb := hder u (k + 1) (by omega) x' hx'I
  have hfac : (0 : ℝ) < (k + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  rw [div_le_iff₀ hfac]
  calc |iteratedDeriv (k + 1) (realComp φ u) x'| * |y - a| ^ (k + 1)
      ≤ ((k + 1).factorial * C ^ (k + 1) * |deriv (realComp φ u) 0|) * |y - a| ^ (k + 1) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = |y - a| ^ (k + 1) * C ^ (k + 1) * |deriv (realComp φ u) 0| * (k + 1).factorial := by
        ring

end FractalGeometry.SelfConformal
