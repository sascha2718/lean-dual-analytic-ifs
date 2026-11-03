module

public import AnalyticESC.Literature.SelfConformal.Toolkit
public import AnalyticESC.Literature.SelfConformal.FengHu.Hyp
public import AnalyticESC.Literature.SelfConformal.FengHu.EntropyRate
public import AnalyticESC.Literature.SelfSimilar.FengHu

@[expose] public section

/-!
# Branch measures and fibre measures of a self-conformal measure

For a conformal system `φ` (`ConformalIFS`), a positive probability vector `p`, the Bernoulli
measure `β = p^ℕ`, the coding map `Π` and the self-conformal measure `μ = Π β`, this file proves
the facts about the first-letter branch measures `μ_a = Π (β|_{[a]})` and the disintegration
`x ↦ β_x` of `β` over `Π` (the conditional measures of D.-J. Feng and H. Hu, *Dimension theory of
iterated function systems*, Comm. Pure Appl. Math. 62 (2009), Section 4) that the proof of
Theorem 2.8 and Proposition 4.10 of Feng–Hu uses:

* `map_shift_restrict`, `lintegral_restrict_head_shift`: the first letter and the tail are
  independent (from `bernoulli_inter_shift` of the toolkit `Bernoulli.lean`).
* `kQ_apply`: `μ_a(E) = p_a β{η : φ_a(Π η) ∈ E}`.
* `bernoulli_inter_eq_setLIntegral`, `map_restrict_eq_withDensity`, `rnDeriv_map_restrict`:
  `β(Π⁻¹ A ∩ s) = ∫_A β_x(s) dμ(x)`, so `x ↦ β_x(s)` is the density of `Π (β|_s)` with respect
  to `μ`.
* `ae_ae_fibre_of_ae`: a property of `(Π ω, ω)` holding `β`-a.e. holds `β_x`-a.e. for `μ`-a.e.
  `x`.
* `ae_fibre_cylinder_pos`: `β_{Π ω}[ω|_l] > 0` for `β`-a.e. `ω`.
* `ae_fibre_cocycle`: the cocycle identity `β_{Π ω}[ω|_{l+1}] = β_{Π ω}[ω_0] β_{Π σ ω}[(σ ω)|_l]`
  for `β`-a.e. `ω`.

The basic facts on the Bernoulli shift, the coding map and the disintegration come from the
toolkit files `FractalGeometry/SelfConformal/{Bernoulli,Coding,Fibre}.lean`.

Copied from the library `FractalGeometry` (module `FractalGeometry.SelfConformal.FengHu.Branch`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.SelfConformal.FengHu

open MeasureTheory ProbabilityTheory Set Filter Topology
open AnalyticESC (I realComp IsProbVec)

variable {N : ℕ}

/-! ### Bernoulli measures -/

/-- The first-letter cylinder `{ω : ω_0 = a}` is measurable. -/
theorem measurableSet_head (a : Fin N) : MeasurableSet {ω : ℕ → Fin N | ω 0 = a} :=
  measurableSet_eq_fun (measurable_pi_apply 0) measurable_const

/-- `σ (β|_{[a]}) = p_a β`. -/
theorem map_shift_restrict {p : Fin N → ℝ} (hp : IsProbVec p) (a : Fin N) :
    ((bernoulli p hp).restrict {ω | ω 0 = a}).map shift =
      ENNReal.ofReal (p a) • bernoulli p hp := by
  ext S hS
  rw [Measure.map_apply measurable_shift hS, Measure.restrict_apply (measurable_shift hS),
    Measure.smul_apply, smul_eq_mul, Set.inter_comm, bernoulli_inter_shift hp a hS]

/-- `∫_{[a]} f(σ ω) dβ(ω) = p_a ∫ f dβ`. -/
theorem lintegral_restrict_head_shift {p : Fin N → ℝ} (hp : IsProbVec p) (a : Fin N)
    {f : (ℕ → Fin N) → ENNReal} (hf : Measurable f) :
    ∫⁻ ω in {ω | ω 0 = a}, f (shift ω) ∂bernoulli p hp =
      ENNReal.ofReal (p a) * ∫⁻ η, f η ∂bernoulli p hp := by
  rw [← lintegral_map hf measurable_shift, map_shift_restrict hp a, lintegral_smul_measure,
    smul_eq_mul]

/-- The law of the first letter: `∫ g(ω_0) dβ = ∑_a p_a g(a)`. -/
theorem integral_head {p : Fin N → ℝ} (hp : IsProbVec p) (g : Fin N → ℝ) :
    ∫ ω, g (ω 0) ∂bernoulli p hp = ∑ a, p a * g a := by
  rw [← integral_map (measurable_pi_apply 0).aemeasurable
    (measurable_of_finite g).aestronglyMeasurable, map_eval_bernoulli hp 0, integral_step p hp]

/-! ### The coding map and the branch measures -/

variable {φ : Fin N → ℝ → ℝ} {c L : ℝ} {p : Fin N → ℝ}

/-- A continuous extension of `φ_a|_I` to the line. -/
noncomputable def extMap (φ : Fin N → ℝ → ℝ) (a : Fin N) : ℝ → ℝ :=
  Set.IccExtend zero_le_one fun y : I => φ a y

/-- The extension `extMap φ a` is continuous. -/
theorem continuous_extMap (hφ : ConformalIFS φ c L) (a : Fin N) : Continuous (extMap φ a) :=
  ((hφ.continuousOn a).domRestrict).Icc_extend'

/-- The extension `extMap φ a` agrees with `φ_a` on `I`. -/
theorem extMap_of_mem (a : Fin N) {y : ℝ} (hy : y ∈ I) : extMap φ a y = φ a y :=
  Set.IccExtend_of_mem zero_le_one _ hy

/-- `η ↦ φ_a(Π η)` is measurable. -/
theorem measurable_map_coding (hφ : ConformalIFS φ c L) (a : Fin N) :
    Measurable fun η : ℕ → Fin N => φ a (coding φ η) := by
  have h : (fun η : ℕ → Fin N => φ a (coding φ η)) = extMap φ a ∘ coding φ :=
    funext fun η => (extMap_of_mem a (hφ.coding_mem η)).symm
  rw [h]
  exact (continuous_extMap hφ a).measurable.comp (measurable_coding φ)

/-- The branch measure `μ_a = Π (β|_{[a]})` of the first letter `a`. -/
noncomputable def kQ (φ : Fin N → ℝ → ℝ) (p : Fin N → ℝ) (hp : IsProbVec p) (a : Fin N) :
    Measure ℝ :=
  FractalGeometry.SelfSimilar.FengHu.branch (bernoulli p hp) (fun ω => ω 0) (coding φ) a

/-- The branch measures are finite. -/
instance (hp : IsProbVec p) (a : Fin N) : IsFiniteMeasure (kQ φ p hp a) := by
  unfold kQ
  infer_instance

/-- The branch measure as an image measure. -/
theorem kQ_eq (hp : IsProbVec p) (a : Fin N) :
    kQ φ p hp a = ((bernoulli p hp).restrict {ω | ω 0 = a}).map (coding φ) := rfl

/-- `μ_a ≤ μ`. -/
theorem kQ_le (hp : IsProbVec p) (a : Fin N) : kQ φ p hp a ≤ selfConformal φ p hp :=
  FractalGeometry.SelfSimilar.FengHu.branch_le _ _ (measurable_coding φ) a

/-- `μ_a(E) = p_a β{η : φ_a(Π η) ∈ E}`. -/
theorem kQ_apply (hφ : ConformalIFS φ c L) (hp : IsProbVec p) (a : Fin N) {E : Set ℝ}
    (hE : MeasurableSet E) :
    kQ φ p hp a E = ENNReal.ofReal (p a) * bernoulli p hp {η | φ a (coding φ η) ∈ E} := by
  rw [kQ_eq, Measure.map_apply (measurable_coding φ) hE,
    Measure.restrict_apply (measurable_coding φ hE)]
  have hset : coding φ ⁻¹' E ∩ {ω | ω 0 = a} =
      {ω | ω 0 = a} ∩ shift ⁻¹' {η | φ a (coding φ η) ∈ E} := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    rw [hφ.coding_eq ω]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h2 ▸ h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1 ▸ h2, h1⟩
  rw [hset]
  exact bernoulli_inter_shift hp a (S := {η | φ a (coding φ η) ∈ E})
    (measurable_map_coding hφ a hE)

/-- `μ(I) = 1`. -/
theorem selfConformal_I (hφ : ConformalIFS φ c L) (hp : IsProbVec p) :
    selfConformal φ p hp I = 1 := by
  rw [selfConformal_apply φ hp measurableSet_Icc]
  have : coding φ ⁻¹' I = univ := eq_univ_of_forall hφ.coding_mem
  rw [this, measure_univ]

/-! ### The fibre measures -/

variable [NeZero N]

/-- `x ↦ β_x(s)` is measurable for measurable `s`. -/
theorem measurable_fibre_apply (φ : Fin N → ℝ → ℝ) (hp : IsProbVec p) {s : Set (ℕ → Fin N)}
    (hs : MeasurableSet s) : Measurable fun x => fibre φ p hp x s :=
  Kernel.measurable_coe _ hs

omit [NeZero N] in
/-- The graph measure of a product set: `ρ(A × s) = β(Π⁻¹ A ∩ s)`. -/
theorem graphMeasure_prod (φ : Fin N → ℝ → ℝ) (hp : IsProbVec p) {A : Set ℝ}
    (hA : MeasurableSet A) {s : Set (ℕ → Fin N)} (hs : MeasurableSet s) :
    graphMeasure φ p hp (A ×ˢ s) = bernoulli p hp (coding φ ⁻¹' A ∩ s) := by
  unfold graphMeasure
  rw [Measure.map_apply ((measurable_coding φ).prodMk measurable_id :
    Measurable fun ω => (coding φ ω, ω)) (hA.prod hs)]
  rfl

/-- `β(Π⁻¹ A ∩ s) = ∫_A β_x(s) dμ(x)`. -/
theorem bernoulli_inter_eq_setLIntegral (φ : Fin N → ℝ → ℝ) (hp : IsProbVec p) {A : Set ℝ}
    (hA : MeasurableSet A) {s : Set (ℕ → Fin N)} (hs : MeasurableSet s) :
    bernoulli p hp (coding φ ⁻¹' A ∩ s) = ∫⁻ x in A, fibre φ p hp x s ∂selfConformal φ p hp := by
  have h := Measure.compProd_apply_prod (μ := selfConformal φ p hp)
    (κ := (graphMeasure φ p hp).condKernel) hA hs
  rw [compProd_fibre, graphMeasure_prod φ hp hA hs] at h
  exact h

/-- `Π (β|_s) = β_·(s) μ`. -/
theorem map_restrict_eq_withDensity (φ : Fin N → ℝ → ℝ) (hp : IsProbVec p)
    {s : Set (ℕ → Fin N)} (hs : MeasurableSet s) :
    ((bernoulli p hp).restrict s).map (coding φ) =
      (selfConformal φ p hp).withDensity fun x => fibre φ p hp x s := by
  ext A hA
  rw [Measure.map_apply (measurable_coding φ) hA,
    Measure.restrict_apply (measurable_coding φ hA), withDensity_apply _ hA,
    bernoulli_inter_eq_setLIntegral φ hp hA hs]

/-- The density of `Π (β|_s)` with respect to `μ` is `x ↦ β_x(s)`. -/
theorem rnDeriv_map_restrict (φ : Fin N → ℝ → ℝ) (hp : IsProbVec p) {s : Set (ℕ → Fin N)}
    (hs : MeasurableSet s) :
    (((bernoulli p hp).restrict s).map (coding φ)).rnDeriv (selfConformal φ p hp) =ᵐ[
      selfConformal φ p hp] fun x => fibre φ p hp x s := by
  rw [map_restrict_eq_withDensity φ hp hs]
  exact Measure.rnDeriv_withDensity _ (measurable_fibre_apply φ hp hs)

/-- A property of `(Π ω, ω)` holding `β`-a.e. holds `β_x`-a.e. for `μ`-a.e. `x`. -/
theorem ae_ae_fibre_of_ae (φ : Fin N → ℝ → ℝ) (hp : IsProbVec p)
    {P : ℝ → (ℕ → Fin N) → Prop} (h : ∀ᵐ ω ∂bernoulli p hp, P (coding φ ω) ω) :
    ∀ᵐ x ∂selfConformal φ p hp, ∀ᵐ ω ∂fibre φ p hp x, P x ω := by
  obtain ⟨T, hT, hTm, hTP⟩ := h.exists_measurable_mem
  have hmeas : MeasurableSet {q : ℝ × (ℕ → Fin N) | q.1 = coding φ q.2 ∧ q.2 ∈ T} :=
    (measurableSet_eq_fun measurable_fst ((measurable_coding φ).comp measurable_snd)).inter
      (measurable_snd hTm)
  have hG : ∀ᵐ q ∂graphMeasure φ p hp, q.1 = coding φ q.2 ∧ q.2 ∈ T := by
    unfold graphMeasure
    rw [ae_map_iff ((measurable_coding φ).prodMk measurable_id :
      Measurable fun ω => (coding φ ω, ω)).aemeasurable hmeas]
    filter_upwards [hT] with ω hω using ⟨rfl, hω⟩
  rw [← compProd_fibre φ hp] at hG
  filter_upwards [Measure.ae_ae_of_ae_compProd hG] with x hx
  filter_upwards [hx] with ω hω
  rw [hω.1]
  exact hTP ω hω.2

/-- `β_{Π ω}[ω|_l] > 0` for `β`-a.e. `ω` and all `l`. -/
theorem ae_fibre_cylinder_pos (φ : Fin N → ℝ → ℝ) (hp : IsProbVec p) :
    ∀ᵐ ω ∂bernoulli p hp, ∀ l, 0 < fibre φ p hp (coding φ ω) (cylinder (pre l ω)) := by
  have hu : ∀ l (u : Fin l → Fin N), ∀ᵐ ω ∂bernoulli p hp,
      ω ∈ cylinder u → fibre φ p hp (coding φ ω) (cylinder u) ≠ 0 := by
    intro l u
    set Z : Set ℝ := {x | fibre φ p hp x (cylinder u) = 0} with hZ
    have hZm : MeasurableSet Z :=
      measurable_fibre_apply φ hp (measurableSet_cylinder u) (measurableSet_singleton 0)
    have h0 : bernoulli p hp (coding φ ⁻¹' Z ∩ cylinder u) = 0 := by
      rw [bernoulli_inter_eq_setLIntegral φ hp hZm (measurableSet_cylinder u)]
      rw [setLIntegral_congr_fun hZm (g := fun _ => 0) fun x hx => hx]
      simp
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω hωu hzero
    exact hω ⟨hzero, hωu⟩
  have hall : ∀ᵐ ω ∂bernoulli p hp, ∀ l (u : Fin l → Fin N),
      ω ∈ cylinder u → fibre φ p hp (coding φ ω) (cylinder u) ≠ 0 :=
    ae_all_iff.2 fun l => ae_all_iff.2 fun u => hu l u
  filter_upwards [hall] with ω hω l
  exact pos_iff_ne_zero.2 (hω l _ (mem_cylinder_pre l ω))

/-! ### The cocycle identity for the fibre measures -/

omit [NeZero N] in
/-- `[a v] = [a] ∩ σ⁻¹ [v]`. -/
theorem cylinder_cons (a : Fin N) {l : ℕ} (v : Fin l → Fin N) :
    cylinder (Fin.cons a v : Fin (l + 1) → Fin N) = {ω | ω 0 = a} ∩ shift ⁻¹' cylinder v := by
  ext ω
  simp only [cylinder, mem_ofPred_eq, mem_inter_iff, mem_preimage]
  constructor
  · intro h
    refine ⟨by simpa using h 0, fun k => ?_⟩
    simpa [shift] using h k.succ
  · rintro ⟨h0, h⟩ k
    refine Fin.cases ?_ (fun k => ?_) k
    · simpa using h0
    · simpa [shift] using h k

omit [NeZero N] in
/-- `ω|_{l+1} = ω_0 (σ ω)|_l`. -/
theorem pre_succ (l : ℕ) (ω : ℕ → Fin N) :
    pre (l + 1) ω = Fin.cons (ω 0) (pre l (shift ω)) := by
  funext k
  refine Fin.cases rfl (fun k => ?_) k
  simp [pre, shift]

omit [NeZero N] in
/-- The cylinder of `ω|_1` is the first-letter cylinder of `ω_0`. -/
theorem cylinder_pre_one (ω : ℕ → Fin N) : cylinder (pre 1 ω) = {η | η 0 = ω 0} := by
  ext η
  simp only [cylinder, mem_ofPred_eq, pre]
  constructor
  · intro h
    exact h 0
  · intro h k
    rw [Fin.fin_one_eq_zero k]
    exact h

omit [NeZero N] in
/-- A measurable left inverse of `φ_a` on `I`. -/
theorem exists_measurable_leftInverse (hφ : ConformalIFS φ c L) (a : Fin N) :
    ∃ g : ℝ → ℝ, Measurable g ∧ ∀ y ∈ I, g (φ a y) = y := by
  set e : I → ℝ := fun y => φ a y with he
  have hcont : Continuous e := (hφ.continuousOn a).domRestrict
  have hinj : Function.Injective e := fun y z h => Subtype.ext (hφ.injOn a y.2 z.2 h)
  have hemb : MeasurableEmbedding e := (hcont.isClosedEmbedding hinj).measurableEmbedding
  refine ⟨Function.extend e (fun y : I => (y : ℝ)) fun _ => 0,
    hemb.measurable_extend measurable_subtype_coe measurable_const, fun y hy => ?_⟩
  exact hinj.extend_apply (fun y : I => (y : ℝ)) (fun _ => (0 : ℝ)) ⟨y, hy⟩

/-- The one-letter cocycle identity: for `β`-a.e. `ω` with `ω_0 = a`,
`β_{Π ω}[a v] = β_{Π ω}[a] β_{Π σ ω}[v]`. -/
theorem ae_fibre_cons (hφ : ConformalIFS φ c L) (hp : IsProbVec p) (a : Fin N) {l : ℕ}
    (v : Fin l → Fin N) :
    ∀ᵐ ω ∂bernoulli p hp, ω 0 = a →
      fibre φ p hp (coding φ ω) (cylinder (Fin.cons a v : Fin (l + 1) → Fin N)) =
        fibre φ p hp (coding φ ω) {η | η 0 = a} *
          fibre φ p hp (coding φ (shift ω)) (cylinder v) := by
  obtain ⟨g, hg, hgφ⟩ := exists_measurable_leftInverse hφ a
  set μ := selfConformal φ p hp with hμ
  set β := bernoulli p hp with hβ
  set Ca : Set (ℕ → Fin N) := {η | η 0 = a} with hCa
  have hCam : MeasurableSet Ca := measurableSet_head a
  have hCv : MeasurableSet (cylinder v) := measurableSet_cylinder v
  set F : ℝ → ENNReal := fun x => fibre φ p hp x (cylinder (Fin.cons a v : Fin (l + 1) → Fin N))
  set G : ℝ → ENNReal := fun x => fibre φ p hp x Ca
  set H : ℝ → ENNReal := fun x => fibre φ p hp x (cylinder v)
  have hF : Measurable F := measurable_fibre_apply φ hp (measurableSet_cylinder _)
  have hG : Measurable G := measurable_fibre_apply φ hp hCam
  have hH : Measurable H := measurable_fibre_apply φ hp hCv
  have hext := continuous_extMap hφ a
  have key : F =ᵐ[μ] fun x => G x * H (g x) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hF (hG.mul (hH.comp hg))
      fun A hA _ => ?_
    have hA' : MeasurableSet (extMap φ a ⁻¹' A) := hext.measurable hA
    -- the left-hand side
    have hL : ∫⁻ x in A, F x ∂μ = ENNReal.ofReal (p a) * ∫⁻ y in extMap φ a ⁻¹' A, H y ∂μ := by
      rw [← bernoulli_inter_eq_setLIntegral φ hp hA (measurableSet_cylinder _),
        ← bernoulli_inter_eq_setLIntegral φ hp hA' hCv, cylinder_cons]
      have hset : coding φ ⁻¹' A ∩ (Ca ∩ shift ⁻¹' cylinder v) =
          Ca ∩ shift ⁻¹' (coding φ ⁻¹' (extMap φ a ⁻¹' A) ∩ cylinder v) := by
        ext ω
        simp only [mem_inter_iff, mem_preimage, hCa, mem_ofPred_eq]
        rw [extMap_of_mem a (hφ.coding_mem _), hφ.coding_eq ω]
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h2, h2 ▸ h1, h3⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1 ▸ h2, h1, h3⟩
      rw [hset, bernoulli_inter_shift hp a
        (((measurable_coding φ) hA').inter hCv)]
    -- the right-hand side
    have hR : ∫⁻ x in A, G x * H (g x) ∂μ =
        ENNReal.ofReal (p a) * ∫⁻ y in extMap φ a ⁻¹' A, H y ∂μ := by
      have h1 : ∫⁻ x in A, G x * H (g x) ∂μ = ∫⁻ x in A, H (g x) ∂kQ φ p hp a := by
        rw [kQ_eq, map_restrict_eq_withDensity φ hp hCam,
          setLIntegral_withDensity_eq_setLIntegral_mul _ hG (g := fun x => H (g x))
            (hH.comp hg) hA]
        rfl
      rw [h1, kQ_eq, ← lintegral_indicator hA, lintegral_map
        (f := A.indicator fun x => H (g x)) ((hH.comp hg).indicator hA)
        (measurable_coding φ)]
      have h2 : ∀ᵐ ω ∂β.restrict Ca, A.indicator (fun x => H (g x)) (coding φ ω) =
          (fun η => (extMap φ a ⁻¹' A).indicator H (coding φ η)) (shift ω) := by
        filter_upwards [ae_restrict_mem hCam] with ω hω
        have hω' : ω 0 = a := hω
        have hc : coding φ ω = φ a (coding φ (shift ω)) := by rw [hφ.coding_eq ω, hω']
        rw [hc]
        have hy := hφ.coding_mem (shift ω)
        by_cases hA1 : φ a (coding φ (shift ω)) ∈ A
        · have hA2 : coding φ (shift ω) ∈ extMap φ a ⁻¹' A := by
            rw [mem_preimage, extMap_of_mem a hy]
            exact hA1
          rw [Set.indicator_of_mem hA1, Set.indicator_of_mem hA2, hgφ _ hy]
        · have hA2 : coding φ (shift ω) ∉ extMap φ a ⁻¹' A := by
            rw [mem_preimage, extMap_of_mem a hy]
            exact hA1
          rw [Set.indicator_of_notMem hA1, Set.indicator_of_notMem hA2]
      rw [lintegral_congr_ae h2, lintegral_restrict_head_shift hp a
        (f := fun η => (extMap φ a ⁻¹' A).indicator H (coding φ η))
        ((hH.indicator hA').comp (measurable_coding φ)), hμ, selfConformal,
        ← lintegral_map (hH.indicator hA') (measurable_coding φ), lintegral_indicator hA']
    rw [hL, hR]
  have key' := ae_of_ae_map (measurable_coding φ).aemeasurable key
  filter_upwards [key'] with ω hω hω0
  have hc : coding φ ω = φ a (coding φ (shift ω)) := by rw [hφ.coding_eq ω, hω0]
  have := hω
  simp only [F, G, H] at this
  rw [this, hc, hgφ _ (hφ.coding_mem _)]

/-- The cocycle identity `β_{Π ω}[ω|_{l+1}] = β_{Π ω}[ω|_1] β_{Π σ ω}[(σ ω)|_l]`, for `β`-a.e.
`ω` and all `l`. -/
theorem ae_fibre_cocycle (hφ : ConformalIFS φ c L) (hp : IsProbVec p) :
    ∀ᵐ ω ∂bernoulli p hp, ∀ l,
      fibre φ p hp (coding φ ω) (cylinder (pre (l + 1) ω)) =
        fibre φ p hp (coding φ ω) (cylinder (pre 1 ω)) *
          fibre φ p hp (coding φ (shift ω)) (cylinder (pre l (shift ω))) := by
  have h : ∀ᵐ ω ∂bernoulli p hp, ∀ a, ∀ l, ∀ v : Fin l → Fin N, ω 0 = a →
      fibre φ p hp (coding φ ω) (cylinder (Fin.cons a v : Fin (l + 1) → Fin N)) =
        fibre φ p hp (coding φ ω) {η | η 0 = a} *
          fibre φ p hp (coding φ (shift ω)) (cylinder v) :=
    ae_all_iff.2 fun a => ae_all_iff.2 fun l => ae_all_iff.2 fun v => ae_fibre_cons hφ hp a v
  filter_upwards [h] with ω hω l
  rw [pre_succ, cylinder_pre_one]
  exact hω (ω 0) l _ rfl

end FractalGeometry.SelfConformal.FengHu
