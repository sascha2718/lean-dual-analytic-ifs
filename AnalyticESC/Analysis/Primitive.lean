module

public import AnalyticESC.Basic

@[expose] public section

/-!
# Integration on a convex complex neighbourhood

Straight-segment integration constructs the primitives used in the ODE-first proof of
Lemma 5.1. Differentiating the integral gives the integrand; continuity extends to the
closed neighbourhood when the integrand is continuous there.
-/

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory
open scoped Interval

/-- The integral of `f` on the straight segment from `p` to `z`. -/
noncomputable def segmentPrimitive (f : ℂ → ℂ) (p z : ℂ) : ℂ :=
  ∫ t : ℝ in 0..1, (z - p) * f (p + (t : ℂ) * (z - p))

@[simp] theorem segmentPrimitive_self (f : ℂ → ℂ) (p : ℂ) : segmentPrimitive f p p = 0 := by
  simp [segmentPrimitive]

theorem segment_point_mem {U : Set ℂ} (hU : Convex ℝ U) {p z : ℂ}
    (hp : p ∈ U) (hz : z ∈ U) {t : ℝ} (ht : t ∈ Icc 0 1) :
    p + (t : ℂ) * (z - p) ∈ U := by
  simpa only [Complex.real_smul] using hU.add_smul_sub_mem hp hz ht

/-- Segment integration preserves continuity on a convex set, including its boundary. -/
theorem continuousOn_segmentPrimitive {U : Set ℂ} (hU : Convex ℝ U) {f : ℂ → ℂ}
    (hf : ContinuousOn f U) {p : ℂ} (hp : p ∈ U) : ContinuousOn (segmentPrimitive f p) U := by
  let T (t : ℝ) : ℝ := projIcc 0 1 zero_le_one t
  have hT : Continuous T := continuous_subtype_val.comp continuous_projIcc
  have hF : Continuous (fun w : U × ℝ => ((w.1 : ℂ) - p) *
      f (p + (T w.2 : ℂ) * ((w.1 : ℂ) - p))) := by
    apply Continuous.mul (by fun_prop)
    apply hf.comp_continuous (by fun_prop)
    intro w
    exact segment_point_mem hU hp w.1.2 (projIcc 0 1 zero_le_one w.2).2
  have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun (z : U) t => ((z : ℂ) - p) * f (p + (T t : ℂ) * ((z : ℂ) - p))) hF 0 1
  rw [continuousOn_iff_continuous_domRestrict]
  apply hcont.congr
  intro z
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  simp only [T, projIcc_of_mem zero_le_one ht', Subtype.coe_mk]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A holomorphic function on an open convex set has the straight-segment primitive. -/
theorem hasDerivAt_segmentPrimitive {U : Set ℂ} (hUo : IsOpen U) (hUc : Convex ℝ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {p z : ℂ} (hp : p ∈ U) (hz : z ∈ U) :
    HasDerivAt (segmentPrimitive f p) (f z) z := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hUo.mem_nhds hz)
  let P (w : ℂ) (t : ℝ) := p + (t : ℂ) * (w - p)
  let F (w : ℂ) (t : ℝ) := (w - p) * f (P w t)
  let G (w : ℂ) (t : ℝ) := f (P w t) + (w - p) * (deriv f (P w t) * t)
  have hP : ∀ w ∈ closedBall z r, ∀ t ∈ Icc (0 : ℝ) 1, P w t ∈ U :=
    fun w hw t ht => segment_point_mem hUc hp (hball hw) ht
  have hfc : ContinuousOn (Function.uncurry F) (closedBall z r ×ˢ Icc 0 1) := by
    apply ContinuousOn.mul (by fun_prop)
    exact hf.continuousOn.comp (by fun_prop) (fun w hw => hP w.1 hw.1 w.2 hw.2)
  have hgc : ContinuousOn (Function.uncurry G) (closedBall z r ×ˢ Icc 0 1) := by
    apply ContinuousOn.add
    · exact hf.continuousOn.comp (by fun_prop) (fun w hw => hP w.1 hw.1 w.2 hw.2)
    · apply ContinuousOn.mul (by fun_prop)
      apply ContinuousOn.mul
      · exact (hf.deriv hUo).continuousOn.comp (by fun_prop)
          (fun w hw => hP w.1 hw.1 w.2 hw.2)
      · fun_prop
  obtain ⟨B, hB⟩ := ((isCompact_closedBall z r).prod isCompact_Icc).exists_bound_of_continuousOn hgc
  have hFcont : ∀ w ∈ closedBall z r, ContinuousOn (F w) (Icc 0 1) :=
    fun w hw => hfc.comp (f := fun t : ℝ => (w, t)) (by fun_prop) (fun t ht => ⟨hw, ht⟩)
  have hGcont : ContinuousOn (G z) (Icc 0 1) :=
    hgc.comp (f := fun t : ℝ => (z, t)) (by fun_prop) (fun t ht => ⟨mem_closedBall_self hr.le, ht⟩)
  have hder : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ closedBall z r,
      HasDerivAt (fun w => F w t) (G w t) w := by
    intro t ht w hw
    have hfd := (hf.differentiableAt (hUo.mem_nhds (hP w hw t ht))).hasDerivAt
    have hpath := (((hasDerivAt_id w).sub_const p).const_mul (t : ℂ)).const_add p
    convert! ((hasDerivAt_id w).sub_const p).mul (hfd.comp w hpath) using 1
    dsimp [F, G, P]
    ring
  have hInt := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 1) (F := F) (F' := G) (bound := fun _ => B) (closedBall_mem_nhds z hr)
    (by
      filter_upwards [closedBall_mem_nhds z hr] with w hw
      simpa only [uIoc_of_le zero_le_one] using
        ((hFcont w hw).mono Ioc_subset_Icc_self).aestronglyMeasurable (μ := volume) measurableSet_Ioc)
    (ContinuousOn.intervalIntegrable (by
      simpa only [uIcc_of_le zero_le_one] using hFcont z (mem_closedBall_self hr.le)))
    (by simpa using (hGcont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    (Eventually.of_forall fun t ht w hw => hB (w, t) ⟨hw, by simpa using Ioc_subset_Icc_self ht⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun t ht w hw => hder t (by simpa using Ioc_subset_Icc_self ht) w hw)
  have hFTC : (∫ t : ℝ in 0..1, G z t) = f z := by
    have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => (t : ℂ) * f (P z t)) (G z t) t := by
      intro t ht
      have hpt := hP z (mem_closedBall_self hr.le) t (by simpa using ht)
      have hfd := (hf.differentiableAt (hUo.mem_nhds hpt)).hasDerivAt
      have hpder := ((hasDerivAt_id (t : ℂ)).mul_const (z - p)).const_add p
      convert ((hasDerivAt_id (t : ℂ)).mul (hfd.comp (t : ℂ) hpder)).comp_ofReal using 1 <;>
        dsimp [G, P]; ring
    simpa [P] using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hInt.1
  convert! hInt.2 using 1
  exact hFTC.symm

/-- The integrand in straight-segment integration is continuous. -/
theorem continuousOn_segment_integrand {U : Set ℂ} (hUc : Convex ℝ U) {f : ℂ → ℂ}
    (hf : ContinuousOn f U) {p z : ℂ} (hp : p ∈ U) (hz : z ∈ U) :
    ContinuousOn (fun t : ℝ => (z - p) * f (p + (t : ℂ) * (z - p))) (uIcc 0 1) := by
  apply ContinuousOn.mul continuousOn_const
  apply hf.comp (by fun_prop)
  intro t ht
  exact segment_point_mem hUc hp hz (by simpa using ht)

/-- The fundamental theorem of calculus on a complex segment. -/
theorem segmentPrimitive_eq_sub {U : Set ℂ} (hUc : Convex ℝ U) {f g : ℂ → ℂ}
    (hf : ContinuousOn f U) (hg : ∀ w ∈ U, HasDerivAt g (f w) w)
    {p z : ℂ} (hp : p ∈ U) (hz : z ∈ U) : segmentPrimitive f p z = g z - g p := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => g (p + (t : ℂ) * (z - p)))
        ((z - p) * f (p + (t : ℂ) * (z - p))) t := by
    intro t ht
    have h := hg _ (segment_point_mem hUc hp hz (by simpa using ht))
    convert! (h.comp (t : ℂ)
      (((hasDerivAt_id (t : ℂ)).mul_const (z - p)).const_add p)).comp_ofReal using 1
    ring
  simpa [segmentPrimitive] using intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (continuousOn_segment_integrand hUc hf hp hz).intervalIntegrable

/-- Uniform bounds and pointwise convergence allow the limit to pass through segment integration. -/
theorem tendsto_segmentPrimitive {U : Set ℂ} (hUc : Convex ℝ U) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, ContinuousOn (F n) U) {B : ℝ} (hB : ∀ n, ∀ w ∈ U, ‖F n w‖ ≤ B)
    (hlim : ∀ w ∈ U, Tendsto (fun n => F n w) atTop (𝓝 (f w)))
    {p z : ℂ} (hp : p ∈ U) (hz : z ∈ U) :
    Tendsto (fun n => segmentPrimitive (F n) p z) atTop (𝓝 (segmentPrimitive f p z)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => ‖z - p‖ * B)
  · exact Eventually.of_forall fun n =>
      ((continuousOn_segment_integrand hUc (hF n) hp hz).mono uIoc_subset_uIcc).aestronglyMeasurable
        measurableSet_uIoc
  · exact Eventually.of_forall fun n => Eventually.of_forall fun t ht => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB n _
        (segment_point_mem hUc hp hz (by simpa using uIoc_subset_uIcc ht))) (norm_nonneg _)
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun t ht => (hlim _
      (segment_point_mem hUc hp hz (by simpa using uIoc_subset_uIcc ht))).const_mul _

/-- A primitive is real along real segments when the integrand is real there. -/
theorem im_segmentPrimitive_eq_zero {U : Set ℂ} (hUc : Convex ℝ U) {f : ℂ → ℂ}
    (hf : ContinuousOn f U) (hreal : ∀ x : ℝ, (x : ℂ) ∈ U → (f x).im = 0)
    {p x : ℝ} (hp : (p : ℂ) ∈ U) (hx : (x : ℂ) ∈ U) :
    (segmentPrimitive f p x).im = 0 := by
  have hint : IntervalIntegrable (fun t : ℝ => ((x : ℂ) - p) *
      f (p + (t : ℂ) * (x - p))) volume 0 1 :=
    (continuousOn_segment_integrand hUc hf hp hx).intervalIntegrable
  change Complex.imCLM (∫ t : ℝ in 0..1, ((x : ℂ) - p) * f (p + (t : ℂ) * (x - p))) = 0
  rw [← Complex.imCLM.intervalIntegral_comp_comm hint]
  calc _ = ∫ _ : ℝ in 0..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have hm := segment_point_mem hUc hp hx (t := t) (by simpa using ht)
        have he : (p : ℂ) + t * ((x : ℂ) - p) = ((p + t * (x - p) : ℝ) : ℂ) := by push_cast; rfl
        change (((x : ℂ) - p) * f (p + (t : ℂ) * (x - p))).im = 0
        rw [he] at hm ⊢
        rw [Complex.mul_im, hreal _ hm]
        simp
    _ = 0 := by simp

end AnalyticESC
