module

public import AnalyticESC.Basic

@[expose] public section

/-!
# Hutchinson's construction for the dual IFS

The finite-union operator is a contraction on the complete Hausdorff space of nonempty
compact sets. Applied to the complete space of holomorphic functions continuous on the
closed neighbourhood and real on `I`, this gives Lemma 2.1 before the coding description.
-/

namespace AnalyticESC

open Set Metric Filter Topology TopologicalSpace
open scoped NNReal UniformConvergence

/-- Hutchinson's theorem, proved by applying the contraction mapping theorem to nonempty
compact sets with their Hausdorff metric. -/
theorem existsUnique_compact_invariant {X A : Type*} [MetricSpace X] [CompleteSpace X]
    [Nonempty X] [Fintype A] [Nonempty A] (F : A → X → X) {c : ℝ≥0}
    (hc : c < 1) (hF : ∀ i, LipschitzWith c (F i)) :
    ∃! K : NonemptyCompacts X, (K : Set X) = ⋃ i, F i '' (K : Set X) := by
  let T (K : NonemptyCompacts X) : NonemptyCompacts X :=
    ⟨⟨⋃ i, F i '' (K : Set X), isCompact_iUnion fun i =>
      K.isCompact.image (hF i).continuous⟩,
      ⟨F (Classical.arbitrary A) K.nonempty.choose,
        mem_iUnion.2 ⟨_, mem_image_of_mem _ K.nonempty.choose_spec⟩⟩⟩
  have hnear : ∀ (K L : NonemptyCompacts X) x, x ∈ T K →
      ∃ y ∈ T L, dist x y ≤ c * dist K L := by
    intro K L x hx
    obtain ⟨i, a, ha, rfl⟩ := mem_iUnion.1 hx
    obtain ⟨b, hb, hab⟩ := L.isCompact.exists_infDist_eq_dist L.nonempty a
    refine ⟨F i b, mem_iUnion.2 ⟨i, mem_image_of_mem _ hb⟩, ?_⟩
    calc dist (F i a) (F i b) ≤ c * dist a b := (hF i).dist_le_mul _ _
      _ ≤ c * dist K L := by
        rw [← hab, TopologicalSpace.NonemptyCompacts.dist_eq]
        exact mul_le_mul_of_nonneg_left
          (infDist_le_hausdorffDist_of_mem ha (edist_ne_top K L)) c.coe_nonneg
  have hT : ContractingWith c T := ⟨hc, LipschitzWith.of_dist_le_mul fun K L => by
    rw [TopologicalSpace.NonemptyCompacts.dist_eq]
    apply hausdorffDist_le_of_mem_dist (by positivity) (hnear K L)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hnear L K x hx
    exact ⟨y, hy, by simpa only [dist_comm] using hxy⟩⟩
  refine ⟨hT.fixedPoint T, ?_, fun K hK => ?_⟩
  · exact congrArg (fun K : NonemptyCompacts X => (K : Set X)) hT.fixedPoint_isFixedPt.symm
  · exact hT.fixedPoint_unique (NonemptyCompacts.ext hK.symm)

/-! The manuscript's function space, represented by continuous functions on the closure.
The supremum on the closure equals the supremum on the dense open neighbourhood. -/

namespace ClosedAnalyticSpace

variable {ε : ℝ}

instance compactClosure (ε : ℝ) : CompactSpace (closure (nbhd ε)) :=
  isCompact_iff_compactSpace.1 (isCompact_closure_nbhd ε)

abbrev Ambient (ε : ℝ) := C(closure (nbhd ε), ℂ)

/-- Extend a continuous function on the closure by zero outside it. -/
noncomputable def extend (g : Ambient ε) (z : ℂ) : ℂ :=
  open Classical in if hz : z ∈ closure (nbhd ε) then g ⟨z, hz⟩ else 0

@[simp] theorem extend_apply (g : Ambient ε) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    extend g z = g ⟨z, hz⟩ := by simp only [extend, dite_eq_left hz]

theorem continuousOn_extend (g : Ambient ε) : ContinuousOn (extend g) (closure (nbhd ε)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun z : closure (nbhd ε) => extend g z)
  convert g.continuous using 1
  ext z
  exact extend_apply g z.2

/-- Holomorphy in the interior and real values on `I`. Boundary continuity is in `Ambient`. -/
def carrier (ε : ℝ) : Set (Ambient ε) :=
  {g | DifferentiableOn ℂ (extend g) (nbhd ε) ∧ ∀ x ∈ I, (extend g x).im = 0}

theorem isClosed_carrier (ε : ℝ) : IsClosed (carrier ε) := by
  rw [← isSeqClosed_iff_isClosed]
  intro g h hg hlim
  have hUnif : TendstoUniformlyOn (fun n => extend (g n)) (extend h) atTop (nbhd ε) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [hlim.eventually (Metric.ball_mem_nhds h hδ)] with n hn z hz
    rw [extend_apply _ (subset_closure hz), extend_apply _ (subset_closure hz)]
    exact (ContinuousMap.dist_apply_le_dist (f := h) (g := g n) ⟨z, subset_closure hz⟩).trans_lt (by
      simpa only [Metric.mem_ball, dist_comm] using hn)
  refine ⟨hUnif.tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall fun n => (hg n).1) (isOpen_nbhd ε), fun x hx => ?_⟩
  by_cases hz : (x : ℂ) ∈ closure (nbhd ε)
  · have ht : Tendsto (fun n => (g n ⟨x, hz⟩).im) atTop (𝓝 (h ⟨x, hz⟩).im) := by
      exact (Complex.continuous_im.tendsto _).comp
        ((continuous_eval_const (⟨(x : ℂ), hz⟩ : closure (nbhd ε))).tendsto h |>.comp hlim)
    have he : ∀ n, (g n ⟨x, hz⟩).im = 0 := fun n => by
      simpa only [extend_apply _ hz] using (hg n).2 x hx
    rw [extend_apply _ hz]
    exact tendsto_nhds_unique ht (by simpa only [he] using tendsto_const_nhds)
  · simp [extend, hz]

abbrev Space (ε : ℝ) := carrier ε

instance completeSpace (ε : ℝ) : CompleteSpace (Space ε) :=
  (isClosed_carrier ε).completeSpace_coe

instance nonempty (ε : ℝ) : Nonempty (Space ε) := by
  refine ⟨⟨0, ?_, ?_⟩⟩
  · have he : extend (0 : Ambient ε) = 0 := by ext z; simp [extend]
    rw [he]
    exact differentiableOn_const _
  · intro x hx
    simp [extend]

/-- The restriction to the open neighbourhood used by `analyticSpace`. -/
noncomputable def restrict (g : Space ε) : nbhd ε →ᵤ ℂ := toNbhd ε (extend g.1)

theorem restrict_mem (g : Space ε) : restrict g ∈ analyticSpace ε :=
  ⟨extend g.1, g.2.1, continuousOn_extend g.1, g.2.2, rfl⟩

theorem continuous_restrict : Continuous (restrict : Space ε → nbhd ε →ᵤ ℂ) := by
  rw [continuous_iff_continuousAt]
  intro g
  rw [ContinuousAt, UniformFun.tendsto_iff_tendstoUniformly, Metric.tendstoUniformly_iff]
  intro δ hδ
  filter_upwards [Metric.ball_mem_nhds g hδ] with h hh z
  change dist (extend g.1 z) (extend h.1 z) < δ
  rw [extend_apply _ (subset_closure z.2), extend_apply _ (subset_closure z.2)]
  exact (ContinuousMap.dist_apply_le_dist (f := g.1) (g := h.1) ⟨z, subset_closure z.2⟩).trans_lt (by
    simpa only [Metric.mem_ball, Subtype.dist_eq, dist_comm] using hh)

/-- A uniform distance bound on the open neighbourhood extends to its closure. -/
theorem dist_le_of_restrict_le {g h : Space ε} {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ z : nbhd ε, dist (UniformFun.toFun (restrict g) z)
      (UniformFun.toFun (restrict h) z) ≤ δ) : dist g h ≤ δ := by
  change dist g.1 h.1 ≤ δ
  rw [ContinuousMap.dist_le hδ]
  intro z
  have hc := le_on_closure (s := nbhd ε) (f := fun z => dist (extend g.1 z) (extend h.1 z))
    (g := fun _ => δ) (fun z hz => hb ⟨z, hz⟩)
    (by simpa only [dist_eq_norm, Pi.sub_apply] using
      ((continuousOn_extend g.1).sub (continuousOn_extend h.1)).norm) continuousOn_const z.2
  simpa only [extend_apply _ z.2] using hc

theorem restrict_injective : Function.Injective (restrict : Space ε → nbhd ε →ᵤ ℂ) := by
  intro g h heq
  apply dist_le_zero.1
  exact dist_le_of_restrict_le le_rfl fun z => by rw [heq, dist_self]

theorem tendsto_of_restrict {ι : Type*} {l : Filter ι} {g : ι → Space ε} {h : Space ε}
    (hg : Tendsto (restrict ∘ g) l (𝓝 (restrict h))) : Tendsto g l (𝓝 h) := by
  rw [UniformFun.tendsto_iff_tendstoUniformly, Metric.tendstoUniformly_iff] at hg
  rw [Metric.tendsto_nhds]
  intro δ hδ
  filter_upwards [hg (δ / 2) (half_pos hδ)] with n hn
  exact (dist_le_of_restrict_le (half_pos hδ).le (fun z => (by
    simpa only [Function.comp_apply, dist_comm] using (hn z).le))).trans_lt (half_lt_self hδ)

theorem isEmbedding_restrict : Topology.IsEmbedding (restrict : Space ε → nbhd ε →ᵤ ℂ) := by
  refine ⟨Topology.isInducing_iff_nhds.2 fun g => le_antisymm
    (continuous_restrict.tendsto g).le_comap ?_, restrict_injective⟩
  exact tendsto_of_restrict (g := id) tendsto_comap

theorem range_restrict (hε : 0 < ε) : range (restrict : Space ε → nbhd ε →ᵤ ℂ) = analyticSpace ε := by
  apply Subset.antisymm
  · rintro _ ⟨g, rfl⟩
    exact restrict_mem g
  · rintro u ⟨g, hgd, hgc, hgr, rfl⟩
    let G : Ambient ε := ⟨fun z => g z, continuousOn_iff_continuous_domRestrict.1 hgc⟩
    have hGe : ∀ z ∈ closure (nbhd ε), extend G z = g z :=
      fun z hz => extend_apply G hz
    have hG : G ∈ carrier ε :=
      ⟨hgd.congr (fun z hz => hGe z (subset_closure hz)), fun x hx => by
        rw [hGe x (subset_closure (ofReal_mem_nbhd hε hx))]; exact hgr x hx⟩
    refine ⟨⟨G, hG⟩, ?_⟩
    apply UniformFun.toFun.injective
    funext z
    exact hGe z (subset_closure z.2)

variable {N : ℕ} (Φ : IFS N ε)

/-- The dual operator on continuous functions on the closed neighbourhood. -/
noncomputable def opAmbient (i : Fin N) (g : Ambient ε) : Ambient ε := by
  refine ⟨fun z => deriv (Φ.f i) z *
    g ⟨Φ.f i z, subset_closure ((Φ.inClass i).mapsTo z.2)⟩ + Φ.nonlin i z, ?_⟩
  have hd : Continuous (fun z : closure (nbhd ε) => deriv (Φ.f i) z) :=
    continuousOn_iff_continuous_domRestrict.1
      ((Φ.continuousOn_deriv_f i).mono IFS.closure_nbhd_subset_two)
  have hf : Continuous (fun z : closure (nbhd ε) => Φ.f i z) :=
    continuousOn_iff_continuous_domRestrict.1
      ((Φ.differentiableOn_f i).continuousOn.mono IFS.closure_nbhd_subset_two)
  obtain ⟨U, -, hU, -, hn⟩ := Φ.exists_differentiableOn_nonlin i
  exact (hd.mul (g.continuous.comp (hf.subtype_mk _))).add
    (continuousOn_iff_continuous_domRestrict.1 (hn.continuousOn.mono hU))

theorem extend_opAmbient (i : Fin N) (g : Ambient ε) {z : ℂ}
    (hz : z ∈ closure (nbhd ε)) :
    extend (opAmbient Φ i g) z = Φ.dualOp i (extend g) z := by
  simp only [extend_apply _ hz, opAmbient, ContinuousMap.coe_mk, IFS.dualOp,
    extend_apply _ (subset_closure ((Φ.inClass i).mapsTo hz))]

/-- The dual operator preserves holomorphy and real values. -/
noncomputable def op (i : Fin N) (g : Space ε) : Space ε := by
  refine ⟨opAmbient Φ i g.1, ?_, ?_⟩
  · obtain ⟨U, -, hU, -, hn⟩ := Φ.exists_differentiableOn_nonlin i
    have hd := ((Φ.differentiableOn_f i).deriv (isOpen_nbhd _)).mono IFS.nbhd_subset_two
    have hf := (Φ.differentiableOn_f i).mono IFS.nbhd_subset_two
    exact ((hd.mul (g.2.1.comp hf (Φ.mapsTo_f i))).add
      (hn.mono (subset_closure.trans hU))).congr
      (fun z hz => extend_opAmbient Φ i g.1 (subset_closure hz))
  · intro x hx
    rw [extend_opAmbient Φ i g.1 (subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)), IFS.dualOp,
      Complex.add_im, Complex.mul_im, Φ.im_deriv_f_ofReal i
        (ofReal_mem_nbhd (by linarith [Φ.ε_pos]) hx),
      Φ.im_nonlin_ofReal i (ofReal_mem_nbhd Φ.ε_pos hx)]
    have hfx : Φ.f i x = ((Φ.f i x).re : ℂ) :=
      Complex.ext (by simp) (by simp [Φ.im_f_ofReal i
        (ofReal_mem_nbhd (by linarith [Φ.ε_pos]) hx)])
    rw [hfx, g.2.2 _ ((Φ.inClass i).re_mem_I x hx)]
    ring

theorem lipschitz_op (i : Fin N) : LipschitzWith ⟨Φ.cmax, Φ.cmax_nonneg⟩ (op Φ i) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  change dist (opAmbient Φ i g.1) (opAmbient Φ i h.1) ≤ Φ.cmax * dist g.1 h.1
  rw [ContinuousMap.dist_le (mul_nonneg Φ.cmax_nonneg dist_nonneg)]
  intro z
  change dist (deriv (Φ.f i) z * g.1 _ + Φ.nonlin i z)
    (deriv (Φ.f i) z * h.1 _ + Φ.nonlin i z) ≤ _
  rw [dist_eq_norm, add_sub_add_right_eq_sub, ← mul_sub, norm_mul]
  exact mul_le_mul (Φ.norm_deriv_le_cmax i z.2)
    (show ‖g.1 _ - h.1 _‖ ≤ dist g.1 h.1 from
      by simpa only [dist_eq_norm] using
        (ContinuousMap.dist_apply_le_dist (f := g.1) (g := h.1)
          ⟨Φ.f i z, subset_closure ((Φ.inClass i).mapsTo z.2)⟩)) (norm_nonneg _) Φ.cmax_nonneg

theorem restrict_op (i : Fin N) (g : Space ε) :
    restrict (op Φ i g) = Φ.dualOpU i (restrict g) := by
  apply UniformFun.toFun.injective
  funext z
  change extend (opAmbient Φ i g.1) z = _
  rw [extend_opAmbient Φ i g.1 (subset_closure z.2)]
  rfl

end ClosedAnalyticSpace

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

private theorem lift_dualAttractor {Λ : Set (nbhd ε →ᵤ ℂ)} (hΛ : Φ.IsDualAttractor Λ) :
    ∃ K : NonemptyCompacts (ClosedAnalyticSpace.Space ε),
      ClosedAnalyticSpace.restrict '' (K : Set _) = Λ ∧
      (K : Set _) = ⋃ i, ClosedAnalyticSpace.op Φ i '' (K : Set _) := by
  let R := ClosedAnalyticSpace.restrict (ε := ε)
  have hrange : Λ ⊆ range R := by
    rw [ClosedAnalyticSpace.range_restrict Φ.ε_pos]
    exact hΛ.1
  have himage : R '' (R ⁻¹' Λ) = Λ := image_preimage_eq_of_subset hrange
  have hc : IsCompact (R ⁻¹' Λ) :=
    ClosedAnalyticSpace.isEmbedding_restrict.isCompact_iff.2 (himage.symm ▸ hΛ.2.2.1)
  have hne : (R ⁻¹' Λ).Nonempty := by
    obtain ⟨u, hu⟩ := hΛ.2.1
    obtain ⟨g, rfl⟩ := hrange hu
    exact ⟨g, hu⟩
  refine ⟨⟨⟨R ⁻¹' Λ, hc⟩, hne⟩, himage, ?_⟩
  change R ⁻¹' Λ = ⋃ i, ClosedAnalyticSpace.op Φ i '' (R ⁻¹' Λ)
  ext g
  constructor
  · intro hg
    have hg' : R g ∈ ⋃ i, Φ.dualOpU i '' Λ := hΛ.2.2.2 ▸ hg
    obtain ⟨i, u, hu, hgu⟩ := mem_iUnion.1 hg'
    obtain ⟨h, rfl⟩ := hrange hu
    refine mem_iUnion.2 ⟨i, h, hu, ?_⟩
    exact ClosedAnalyticSpace.restrict_injective ((ClosedAnalyticSpace.restrict_op Φ i h).trans hgu)
  · intro hg
    obtain ⟨i, h, hh, rfl⟩ := mem_iUnion.1 hg
    change R (ClosedAnalyticSpace.op Φ i h) ∈ Λ
    rw [hΛ.2.2.2]
    change ClosedAnalyticSpace.restrict (ClosedAnalyticSpace.op Φ i h) ∈ _
    rw [ClosedAnalyticSpace.restrict_op]
    exact mem_iUnion.2 ⟨i, R h, hh, rfl⟩

/-- Lemma 2.1 by Hutchinson's contraction on compact sets, independently of coding. -/
theorem existsUnique_isDualAttractor_hutchinson (hN : 0 < N) : ∃! Λ, Φ.IsDualAttractor Λ := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨K, hK, hunique⟩ := existsUnique_compact_invariant (ClosedAnalyticSpace.op Φ)
    (show (⟨Φ.cmax, Φ.cmax_nonneg⟩ : ℝ≥0) < 1 from Φ.cmax_lt_one)
    (ClosedAnalyticSpace.lipschitz_op Φ)
  let R := ClosedAnalyticSpace.restrict (ε := ε)
  refine ⟨R '' (K : Set _), ⟨?_, K.nonempty.image R,
    K.isCompact.image ClosedAnalyticSpace.continuous_restrict, ?_⟩, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact ClosedAnalyticSpace.restrict_mem g
  · conv_lhs => rw [hK]
    rw [image_iUnion]
    congr 1
    funext i
    rw [image_image, image_image]
    congr 1
    funext g
    exact ClosedAnalyticSpace.restrict_op Φ i g
  · intro Λ hΛ
    obtain ⟨L, hL, hLR⟩ := Φ.lift_dualAttractor hΛ
    rw [← hL, hunique L hLR]

end IFS

end AnalyticESC
