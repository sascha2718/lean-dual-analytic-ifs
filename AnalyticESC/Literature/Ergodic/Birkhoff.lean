module


/-
Birkhoff's maximal and pointwise ergodic theorems.

For an integrable real function on a finite measure space, the ergodic
averages converge almost everywhere to conditional expectation on the
invariant sigma algebra. In the ergodic probability case the limit is
the integral. The maximal inequality is also proved.

Reference: George D. Birkhoff, Proof of the ergodic theorem,
PNAS 17(12) (1931), 656-660. See the README for the exact implemented scope.
-/

public import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
public import Mathlib.Dynamics.Ergodic.Function
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants
public import Mathlib.MeasureTheory.Order.Lattice

/-!
Copied from the library `FractalGeometry` (module `FractalGeometry.Ergodic.Birkhoff`), with the module names of the
imports adapted.
-/

@[expose] public section

namespace FractalGeometry.Ergodic

open MeasureTheory Filter Topology Set

section Pointwise

variable {X : Type*}

noncomputable def birkhoffMax (T : X → X) (h : X → ℝ) (N : ℕ) (x : X) : ℝ :=
  (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one fun k => birkhoffSum T h k x

theorem birkhoffSum_le_birkhoffMax (T : X → X) (h : X → ℝ) {k N : ℕ} (hk : k ≤ N) (x : X) :
    birkhoffSum T h k x ≤ birkhoffMax T h N x :=
  Finset.le_sup' (fun k => birkhoffSum T h k x) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

theorem birkhoffMax_nonneg (T : X → X) (h : X → ℝ) (N : ℕ) (x : X) :
    0 ≤ birkhoffMax T h N x := by
  simpa using birkhoffSum_le_birkhoffMax T h (Nat.zero_le N) x

theorem exists_birkhoffMax_eq (T : X → X) (h : X → ℝ) (N : ℕ) (x : X) :
    ∃ k ≤ N, birkhoffMax T h N x = birkhoffSum T h k x := by
  obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
    fun k => birkhoffSum T h k x
  exact ⟨k, Nat.lt_succ_iff.1 (Finset.mem_range.1 hk), hkeq⟩

theorem birkhoffMax_mono (T : X → X) (h : X → ℝ) {N N' : ℕ} (hN : N ≤ N') (x : X) :
    birkhoffMax T h N x ≤ birkhoffMax T h N' x := by
  obtain ⟨k, hk, hkeq⟩ := exists_birkhoffMax_eq T h N x
  exact hkeq ▸ birkhoffSum_le_birkhoffMax T h (hk.trans hN) x

theorem birkhoffMax_le_add (T : X → X) (h : X → ℝ) (N : ℕ) {x : X}
    (hx : 0 < birkhoffMax T h N x) :
    birkhoffMax T h N x ≤ h x + birkhoffMax T h N (T x) := by
  obtain ⟨k, hk, hkeq⟩ := exists_birkhoffMax_eq T h N x
  rcases k with _ | j
  · rw [hkeq, birkhoffSum_zero] at hx
    exact absurd hx (lt_irrefl _)
  · rw [hkeq, birkhoffSum_succ_apply']
    gcongr
    exact birkhoffSum_le_birkhoffMax T h (Nat.le_of_succ_le hk) (T x)

theorem exists_birkhoffSum_pos_iff (T : X → X) (h : X → ℝ) (x : X) :
    (∃ n, 0 < birkhoffSum T h n x) ↔ ∃ N, 0 < birkhoffMax T h N x := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.trans_le (birkhoffSum_le_birkhoffMax T h le_rfl x)⟩
  · rintro ⟨N, hN⟩
    obtain ⟨k, -, hkeq⟩ := exists_birkhoffMax_eq T h N x
    exact ⟨k, hkeq ▸ hN⟩

def birkhoffUnbounded (T : X → X) (h : X → ℝ) : Set X :=
  {x | ∀ c : ℝ, ∃ n, c < birkhoffSum T h n x}

theorem preimage_birkhoffUnbounded (T : X → X) (h : X → ℝ) :
    T ⁻¹' birkhoffUnbounded T h = birkhoffUnbounded T h := by
  ext x
  constructor
  · intro hx c
    obtain ⟨n, hn⟩ := hx (c - h x)
    refine ⟨n + 1, ?_⟩
    rw [birkhoffSum_succ_apply']
    linarith
  · intro hx c
    obtain ⟨n, hn⟩ := hx (max (c + h x) 0)
    rcases n with _ | m
    · rw [birkhoffSum_zero] at hn
      exact absurd (le_max_right _ _) (not_le.2 hn)
    · refine ⟨m, ?_⟩
      rw [birkhoffSum_succ_apply'] at hn
      have := (le_max_left (c + h x) 0).trans_lt hn
      linarith

theorem birkhoffUnbounded_subset (T : X → X) (h : X → ℝ) :
    birkhoffUnbounded T h ⊆ {x | ∃ n, 0 < birkhoffSum T h n x} :=
  fun _ hx => hx 0

theorem birkhoffSum_sub_of_comp_eq {T : X → X} {f g : X → ℝ} (hg : g ∘ T = g) (n : ℕ)
    (x : X) : birkhoffSum T (fun y => f y - g y) n x = birkhoffSum T f n x - n * g x := by
  have : (fun y => f y - g y) = f - g := rfl
  rw [this, birkhoffSum_sub_apply, birkhoffSum_apply_of_comp_eq hg]
  simp

theorem tendsto_inv_mul_of_forall_exists_le {u : ℕ → ℝ} {a : ℝ}
    (hu : ∀ k : ℕ, ∃ c : ℝ, ∀ n : ℕ, u n - n * (a + 1 / (k + 1)) ≤ c)
    (hl : ∀ k : ℕ, ∃ c : ℝ, ∀ n : ℕ, -u n - n * (-a + 1 / (k + 1)) ≤ c) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * u n) atTop (𝓝 a) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
  obtain ⟨c₁, hc₁⟩ := hu k
  obtain ⟨c₂, hc₂⟩ := hl k
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * max c₁ c₂ / ε)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hnN : (N : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := (Nat.cast_nonneg N).trans_lt hnN
  have hcn : max c₁ c₂ < ε / 2 * n := by
    have := hN.trans hnN
    rw [div_lt_iff₀ hε] at this
    linarith
  have h1 := hc₁ n
  have h2 := hc₂ n
  have h3 := le_max_left c₁ c₂
  have h4 := le_max_right c₁ c₂
  have h5 : (n : ℝ) * (1 / ((k : ℝ) + 1)) < n * (ε / 2) := mul_lt_mul_of_pos_left hk hn0
  have key : (n : ℝ)⁻¹ * u n - a = (u n - n * a) / n := by field_simp
  rw [Real.dist_eq, key, abs_lt, lt_div_iff₀ hn0, div_lt_iff₀ hn0]
  constructor <;> nlinarith

end Pointwise

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X} {h : X → ℝ}

theorem measurable_birkhoffSum (hT : Measurable T) (hh : Measurable h) (n : ℕ) :
    Measurable (birkhoffSum T h n) :=
  Finset.measurable_sum _ fun k _ => hh.comp (hT.iterate k)

theorem integrable_birkhoffSum (hT : MeasurePreserving T μ μ) (hh : Integrable h μ) (n : ℕ) :
    Integrable (birkhoffSum T h n) μ :=
  integrable_finsetSum _ fun k _ => (hT.iterate k).integrable_comp_of_integrable hh

theorem measurable_birkhoffMax (hT : Measurable T) (hh : Measurable h) (N : ℕ) :
    Measurable (birkhoffMax T h N) :=
  Finset.measurable_range_sup'' fun k _ => measurable_birkhoffSum hT hh k

theorem integrable_birkhoffMax (hT : MeasurePreserving T μ μ) (hh : Integrable h μ) (N : ℕ) :
    Integrable (birkhoffMax T h N) μ := by
  have : birkhoffMax T h N = (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      fun k => birkhoffSum T h k := by
    ext x
    simp [birkhoffMax, Finset.sup'_apply]
  rw [this]
  exact Finset.sup'_induction (p := fun g : X → ℝ => Integrable g μ) _ _
    (fun _ h₁ _ h₂ => h₁.sup h₂) fun k _ => integrable_birkhoffSum hT hh k

theorem measurableSet_birkhoffUnbounded (hT : Measurable T) (hh : Measurable h) :
    MeasurableSet (birkhoffUnbounded T h) := by
  have : birkhoffUnbounded T h = ⋂ c : ℕ, ⋃ n : ℕ, {x | (c : ℝ) < birkhoffSum T h n x} := by
    ext x
    simp only [birkhoffUnbounded, mem_ofPred_eq, mem_iInter, mem_iUnion]
    refine ⟨fun hx c => hx c, fun hx c => ?_⟩
    obtain ⟨m, hm⟩ := exists_nat_gt c
    obtain ⟨n, hn⟩ := hx m
    exact ⟨n, hm.trans hn⟩
  rw [this]
  exact MeasurableSet.iInter fun c => MeasurableSet.iUnion fun n =>
    measurableSet_lt measurable_const (measurable_birkhoffSum hT hh n)

theorem setIntegral_birkhoffMax_pos_nonneg (hT : MeasurePreserving T μ μ) (hh : Integrable h μ)
    (hm : Measurable h) (N : ℕ) : 0 ≤ ∫ x in {x | 0 < birkhoffMax T h N x}, h x ∂μ := by
  have hMm : Measurable (birkhoffMax T h N) := measurable_birkhoffMax hT.measurable hm N
  have hMi : Integrable (birkhoffMax T h N) μ := integrable_birkhoffMax hT hh N
  have hEm : MeasurableSet {x | 0 < birkhoffMax T h N x} :=
    measurableSet_lt measurable_const hMm
  have hMTi : Integrable (fun x => birkhoffMax T h N (T x)) μ :=
    hT.integrable_comp_of_integrable hMi
  have h1 : ∫ x in {x | 0 < birkhoffMax T h N x},
        (birkhoffMax T h N x - birkhoffMax T h N (T x)) ∂μ
      ≤ ∫ x in {x | 0 < birkhoffMax T h N x}, h x ∂μ := by
    refine setIntegral_mono_on (hMi.sub hMTi).integrableOn hh.integrableOn hEm fun x hx => ?_
    have := birkhoffMax_le_add T h N hx
    linarith
  have h2 : ∫ x in {x | 0 < birkhoffMax T h N x}, birkhoffMax T h N x ∂μ
      = ∫ x, birkhoffMax T h N x ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    exact le_antisymm (not_lt.1 hx) (birkhoffMax_nonneg T h N x)
  have h3 : ∫ x in {x | 0 < birkhoffMax T h N x}, birkhoffMax T h N (T x) ∂μ
      ≤ ∫ x, birkhoffMax T h N (T x) ∂μ :=
    setIntegral_le_integral hMTi (Eventually.of_forall fun x => birkhoffMax_nonneg T h N (T x))
  have h4 : ∫ x, birkhoffMax T h N (T x) ∂μ = ∫ x, birkhoffMax T h N x ∂μ := by
    rw [← integral_map hT.aemeasurable (hT.map_eq.symm ▸ hMi.aestronglyMeasurable), hT.map_eq]
  rw [integral_sub hMi.integrableOn hMTi.integrableOn] at h1
  linarith

theorem maximal_ergodic_of_measurable (hT : MeasurePreserving T μ μ) (hh : Integrable h μ)
    (hm : Measurable h) : 0 ≤ ∫ x in {x | ∃ n, 0 < birkhoffSum T h n x}, h x ∂μ := by
  have hset : {x | ∃ n, 0 < birkhoffSum T h n x} = ⋃ N, {x | 0 < birkhoffMax T h N x} := by
    ext x
    simp [exists_birkhoffSum_pos_iff]
  rw [hset]
  have hmono : Monotone fun N => {x | 0 < birkhoffMax T h N x} :=
    fun N N' hN x hx => lt_of_lt_of_le hx (birkhoffMax_mono T h hN x)
  have hlim := tendsto_setIntegral_of_monotone
    (fun N => measurableSet_lt measurable_const (measurable_birkhoffMax hT.measurable hm N))
    hmono hh.integrableOn
  exact ge_of_tendsto' hlim fun N => setIntegral_birkhoffMax_pos_nonneg hT hh hm N

theorem maximal_ergodic (hT : MeasurePreserving T μ μ) (hh : Integrable h μ) :
    0 ≤ ∫ x in {x | ∃ n, 0 < birkhoffSum T h n x}, h x ∂μ := by
  have hh' : h =ᵐ[μ] hh.1.mk h := hh.1.ae_eq_mk
  have hS : ∀ᵐ x ∂μ, ∀ n : ℕ, birkhoffSum T h n x = birkhoffSum T (hh.1.mk h) n x :=
    ae_all_iff.2 fun n => hT.quasiMeasurePreserving.birkhoffSum_ae_eq_of_ae_eq hh' n
  have hE : {x | ∃ n, 0 < birkhoffSum T h n x}
      =ᵐ[μ] {x | ∃ n, 0 < birkhoffSum T (hh.1.mk h) n x} :=
    eventuallyEqSet_iff.2 (hS.mono fun x hx => by simp only [mem_ofPred_eq, hx])
  rw [setIntegral_congr_set hE, integral_congr_ae (ae_restrict_of_ae hh')]
  exact maximal_ergodic_of_measurable hT (hh.congr hh') hh.1.stronglyMeasurable_mk.measurable

theorem setIntegral_birkhoffUnbounded_nonneg (hT : MeasurePreserving T μ μ)
    (hh : Integrable h μ) (hm : Measurable h) :
    0 ≤ ∫ x in birkhoffUnbounded T h, h x ∂μ := by
  have hBm := measurableSet_birkhoffUnbounded hT.measurable hm
  have hTB : MeasurePreserving T (μ.restrict (birkhoffUnbounded T h))
      (μ.restrict (birkhoffUnbounded T h)) := by
    have := hT.restrict_preimage hBm
    rwa [preimage_birkhoffUnbounded] at this
  have hEm : MeasurableSet {x | ∃ n, 0 < birkhoffSum T h n x} := by
    have : {x | ∃ n, 0 < birkhoffSum T h n x} = ⋃ n, {x | 0 < birkhoffSum T h n x} := by
      ext x
      simp
    rw [this]
    exact MeasurableSet.iUnion fun n =>
      measurableSet_lt measurable_const (measurable_birkhoffSum hT.measurable hm n)
  have := maximal_ergodic hTB hh.integrableOn
  rwa [Measure.restrict_restrict hEm,
    inter_eq_self_of_subset_right (birkhoffUnbounded_subset T h)] at this

open MeasurableSpace in

theorem measure_birkhoffUnbounded_eq_zero [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    {f g : X → ℝ} (hf : Integrable f μ) (hfm : Measurable f) (hg : Integrable g μ)
    (hgm : Measurable[invariants T] g)
    (hfg : ∀ s, MeasurableSet[invariants T] s → ∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ)
    {ε : ℝ} (hε : 0 < ε) :
    μ (birkhoffUnbounded T fun x => f x - (g x + ε)) = 0 := by
  have hgm' : Measurable g := hgm.mono (invariants_le T) le_rfl
  have hgε : Integrable (fun x => g x + ε) μ := hg.add (integrable_const ε)
  have hhi : Integrable (fun x => f x - (g x + ε)) μ := hf.sub hgε
  have hhm : Measurable fun x => f x - (g x + ε) := hfm.sub (hgm'.add measurable_const)
  have hBm := measurableSet_birkhoffUnbounded hT.measurable hhm
  have hBinv : MeasurableSet[invariants T] (birkhoffUnbounded T fun x => f x - (g x + ε)) :=
    ⟨hBm, preimage_birkhoffUnbounded T _⟩
  have h0 := setIntegral_birkhoffUnbounded_nonneg hT hhi hhm
  rw [integral_sub hf.integrableOn hgε.integrableOn,
    integral_add hg.integrableOn (integrable_const ε).integrableOn, hfg _ hBinv,
    setIntegral_const, smul_eq_mul] at h0
  have h1 : μ.real (birkhoffUnbounded T fun x => f x - (g x + ε)) ≤ 0 := by
    by_contra hcon
    rw [not_le] at hcon
    nlinarith
  exact (measureReal_eq_zero_iff).1 (le_antisymm h1 measureReal_nonneg)

open MeasurableSpace in

theorem birkhoff_ae_of_measurable [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : X → ℝ} (hf : Integrable f μ) (hfm : Measurable f) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => birkhoffAverage ℝ T f n x) atTop
      (𝓝 ((μ[f | invariants T]) x)) := by
  set g := μ[f | invariants T] with hg
  have hgm : Measurable[invariants T] g := stronglyMeasurable_condExp.measurable
  have hgi : Integrable g μ := integrable_condExp
  have hgT : g ∘ T = g := comp_eq_of_measurable_invariants hgm
  have hfg : ∀ s, MeasurableSet[invariants T] s → ∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ :=
    fun s hs => setIntegral_condExp (invariants_le T) hf hs
  have hfg' : ∀ s, MeasurableSet[invariants T] s →
      ∫ x in s, (-g) x ∂μ = ∫ x in s, (-f) x ∂μ := fun s hs => by
    simp only [Pi.neg_apply, integral_neg, hfg s hs]
  have hu : ∀ᵐ x ∂μ, ∀ k : ℕ,
      x ∉ birkhoffUnbounded T fun y => f y - (g y + 1 / ((k : ℝ) + 1)) :=
    ae_all_iff.2 fun k => measure_eq_zero_iff_ae_notMem.1
      (measure_birkhoffUnbounded_eq_zero hT hf hfm hgi hgm hfg Nat.one_div_pos_of_nat)
  have hl : ∀ᵐ x ∂μ, ∀ k : ℕ,
      x ∉ birkhoffUnbounded T fun y => (-f) y - ((-g) y + 1 / ((k : ℝ) + 1)) :=
    ae_all_iff.2 fun k => measure_eq_zero_iff_ae_notMem.1
      (measure_birkhoffUnbounded_eq_zero hT hf.neg hfm.neg hgi.neg hgm.neg hfg'
        Nat.one_div_pos_of_nat)
  filter_upwards [hu, hl] with x hxu hxl
  have key := tendsto_inv_mul_of_forall_exists_le (u := fun n => birkhoffSum T f n x)
    (a := g x) (fun k => ?_) (fun k => ?_)
  · simpa [birkhoffAverage] using key
  · have := hxu k
    simp only [birkhoffUnbounded, mem_ofPred_eq, not_forall, not_exists, not_lt] at this
    obtain ⟨c, hc⟩ := this
    refine ⟨c, fun n => ?_⟩
    have hgk : (fun y => g y + 1 / ((k : ℝ) + 1)) ∘ T = fun y => g y + 1 / ((k : ℝ) + 1) := by
      ext y
      simpa using congrFun hgT y
    have := hc n
    rwa [birkhoffSum_sub_of_comp_eq hgk] at this
  · have := hxl k
    simp only [birkhoffUnbounded, mem_ofPred_eq, not_forall, not_exists, not_lt] at this
    obtain ⟨c, hc⟩ := this
    refine ⟨c, fun n => ?_⟩
    have hgk : (fun y => (-g) y + 1 / ((k : ℝ) + 1)) ∘ T
        = fun y => (-g) y + 1 / ((k : ℝ) + 1) := by
      ext y
      simpa using congrFun hgT y
    have := hc n
    rw [birkhoffSum_sub_of_comp_eq hgk, birkhoffSum_neg] at this
    simpa using this

theorem birkhoff_ae {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ) {f : X → ℝ} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => birkhoffAverage ℝ T f n x) atTop
      (𝓝 ((μ[f | MeasurableSpace.invariants T]) x)) := by
  have hff' : f =ᵐ[μ] hf.1.mk f := hf.1.ae_eq_mk
  have h1 := birkhoff_ae_of_measurable hT (hf.congr hff') hf.1.stronglyMeasurable_mk.measurable
  have h2 : μ[f | MeasurableSpace.invariants T]
      =ᵐ[μ] μ[hf.1.mk f | MeasurableSpace.invariants T] := condExp_congr_ae hff'
  have h3 : ∀ᵐ x ∂μ, ∀ n : ℕ,
      birkhoffAverage ℝ T f n x = birkhoffAverage ℝ T (hf.1.mk f) n x :=
    ae_all_iff.2 fun n => hT.quasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ hff' n
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  simp only [hx3, hx2]
  exact hx1

theorem birkhoff_ergodic {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {T : X → X} (hT : Ergodic T μ) {f : X → ℝ} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => birkhoffAverage ℝ T f n x) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hgm : Measurable[MeasurableSpace.invariants T] (μ[f | MeasurableSpace.invariants T]) :=
    stronglyMeasurable_condExp.measurable
  obtain ⟨c, hc⟩ := hT.toPreErgodic.ae_eq_const_of_ae_eq_comp
    (hgm.mono (MeasurableSpace.invariants_le T) le_rfl)
    (MeasurableSpace.comp_eq_of_measurable_invariants hgm)
  have hcf : c = ∫ x, f x ∂μ := by
    rw [← integral_condExp (MeasurableSpace.invariants_le T), integral_congr_ae hc]
    simp
  filter_upwards [birkhoff_ae hT.toMeasurePreserving hf, hc] with x hx hxc
  rw [← hcf]
  rwa [hxc] at hx

end FractalGeometry.Ergodic
