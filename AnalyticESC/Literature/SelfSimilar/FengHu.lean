module

public import AnalyticESC.Literature.Ergodic.Birkhoff
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.ExactDimensionTransfer
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.BallInformationEnvelope
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.TriangularAverages
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.TerminalAverages

/-!
# Feng–Hu exact dimensionality on the real line

Independent self-similar specialisation of Theorem 2.8 in De-Jun Feng and
Huyi Hu, *Dimension theory of iterated function systems*, Communications on
Pure and Applied Mathematics 62 (2009), 1435–1500, doi:10.1002/cpa.20276.

`FengHu.Coding` consists of a measurable dynamical system, a finite alphabet,
and a bounded real coding satisfying a uniformly contractive similarity
recursion. For every invariant ergodic probability measure, its image under
the coding has an almost-everywhere constant local dimension. No separation
condition is assumed. This module proves the existence of that dimension;
it does not yet identify the information integral with projection entropy.

Copied from the library `FractalGeometry` (module `FractalGeometry.SelfSimilar.FengHu`), with the module names of the
imports adapted.
-/

@[expose] public section

namespace FractalGeometry.SelfSimilar

open FractalGeometry.Ergodic

open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

universe u

namespace FengHu

noncomputable def ratioInfo (κ μ : Measure ℝ) (z ρ : ℝ) : ℝ :=
  -Real.log (κ (closedBall z ρ) / μ (closedBall z ρ)).toReal

noncomputable def densityInfo (κ μ : Measure ℝ) (z : ℝ) : ℝ :=
  -Real.log (κ.rnDeriv μ z).toReal

theorem measurable_densityInfo (κ μ : Measure ℝ) : Measurable (densityInfo κ μ) :=
  (Measure.measurable_rnDeriv κ μ).ennreal_toReal.log.neg

theorem measurable_ratioInfo (κ μ : Measure ℝ) [IsFiniteMeasure κ] [IsFiniteMeasure μ]
    {β : Type*} [MeasurableSpace β] {c r : β → ℝ} (hc : Measurable c) (hr : Measurable r) :
    Measurable fun x => ratioInfo κ μ (c x) (r x) :=
  (((ExactOverlaps.measurable_closedBall_measure κ hc hr).div
    (ExactOverlaps.measurable_closedBall_measure μ hc hr)).ennreal_toReal.log).neg

theorem ae_tendsto_ratioInfo (κ μ : Measure ℝ) [IsFiniteMeasure κ] [IsFiniteMeasure μ]
    (h : κ ≤ μ) :
    ∀ᵐ z ∂κ, Tendsto (fun ρ => ratioInfo κ μ z ρ) (𝓝[>] 0) (𝓝 (densityInfo κ μ z)) := by
  have hac : κ ≪ μ := Measure.absolutelyContinuous_of_le h
  filter_upwards [hac.ae_le (Besicovitch.ae_tendsto_rnDeriv κ μ), Measure.rnDeriv_pos hac,
    hac.ae_le (Measure.rnDeriv_lt_top κ μ)] with z hz hpos hfin
  have hr := (ENNReal.continuousAt_toReal hfin.ne).tendsto.comp hz
  have hp : (κ.rnDeriv μ z).toReal ≠ 0 := (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  simpa only [Function.comp_def, ratioInfo, densityInfo] using (hr.log hp).neg

section Triangular

variable {Ω : Type*} [MeasurableSpace Ω] {m : Measure Ω} [IsProbabilityMeasure m] {T : Ω → Ω}

theorem ae_tendsto_triangularAverage (hT : Ergodic T m) {F : ℕ → Ω → ℝ} {f G : Ω → ℝ}
    (hFm : ∀ n, Measurable (F n)) (hfm : Measurable f) (hGi : Integrable G m)
    (hbound : ∀ᵐ x ∂m, (∀ n, |F n x| ≤ G x) ∧ |f x| ≤ G x)
    (hlim : ∀ᵐ x ∂m, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    ∀ᵐ x ∂m, Tendsto (fun n => ExactOverlaps.Ergodic.triangularAverage T F n x) atTop
      (𝓝 (∫ v, f v ∂m)) := by
  let H := ExactOverlaps.Ergodic.tailOscillation F f
  have hHm : ∀ k, Measurable (H k) := ExactOverlaps.Ergodic.measurable_tailOscillation hFm hfm
  have hHi : ∀ k, Integrable (H k) m := by
    intro k
    apply (hGi.const_mul 2).mono' (hHm k).aestronglyMeasurable
    filter_upwards [hbound] with x hx
    have hh := ExactOverlaps.Ergodic.tailOscillation_bounds hx.1 hx.2 k
    change ‖ExactOverlaps.Ergodic.tailOscillation F f k x‖ ≤ 2 * G x
    simpa only [Real.norm_eq_abs, abs_of_nonneg hh.1] using hh.2
  have hfi : Integrable f m := by
    apply hGi.mono' hfm.aestronglyMeasurable
    simpa only [Real.norm_eq_abs] using hbound.mono (fun _ h => h.2)
  have hHint : Tendsto (fun k => ∫ x, H k x ∂m) atTop (𝓝 0) :=
    ExactOverlaps.Ergodic.integral_tailOscillation_tendsto_zero hFm hfm hGi hbound hlim
  have hborbit : ∀ᵐ x ∂m, ∀ j : ℕ,
      (∀ n, |F n (T^[j] x)| ≤ G (T^[j] x)) ∧ |f (T^[j] x)| ≤ G (T^[j] x) := by
    apply ae_all_iff.mpr
    intro j
    exact (hT.toMeasurePreserving.iterate j).quasiMeasurePreserving.ae hbound
  have hHave : ∀ᵐ x ∂m, ∀ k : ℕ,
      Tendsto (fun n => birkhoffAverage ℝ T (H k) n x) atTop (𝓝 (∫ v, H k v ∂m)) :=
    ae_all_iff.mpr (fun k => birkhoff_ergodic hT (hHi k))
  filter_upwards [hborbit, hHave, birkhoff_ergodic hT hfi, birkhoff_ergodic hT hGi]
    with x hb hH hf hG
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k, hk⟩ :=
    (hHint.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))).exists
  have eH := (hH k).eventually (gt_mem_nhds
    (show (∫ v, H k v ∂m) < (∫ v, H k v ∂m) + ε / 4 by linarith))
  have ht := (ExactOverlaps.Ergodic.terminal_orbit_sum_div_tendsto_zero T G x hG k).const_mul 2
  simp only [mul_zero] at ht
  have eT := ht.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))
  have ef := (Metric.tendsto_nhds.mp hf) (ε / 4) (by positivity)
  filter_upwards [eH, eT, ef, eventually_ge_atTop k] with n hnH hnT hnf hkn
  rw [Real.dist_eq] at hnf ⊢
  have herr := ExactOverlaps.Ergodic.triangularAverage_error_le T (fun j => (hb j).1)
    (fun j => (hb j).2) hkn
  have htri := abs_sub_le (ExactOverlaps.Ergodic.triangularAverage T F n x)
    (birkhoffAverage ℝ T f n x) (∫ v, f v ∂m)
  change birkhoffAverage ℝ T (ExactOverlaps.Ergodic.tailOscillation F f k) n x < _ at hnH
  linarith

end Triangular

section Branch

variable {Ω A : Type*}

def cyl (s : Ω → A) (a : A) : Set Ω := s ⁻¹' {a}

theorem iUnion_cyl (s : Ω → A) : ⋃ a, cyl s a = univ := by
  ext x
  simp [cyl]

variable [MeasurableSpace Ω]

noncomputable def branch (m : Measure Ω) (s : Ω → A) (q : Ω → ℝ) (a : A) : Measure ℝ :=
  (m.restrict (cyl s a)).map q

instance (m : Measure Ω) [IsFiniteMeasure m] (s : Ω → A) (q : Ω → ℝ) (a : A) :
    IsFiniteMeasure (branch m s q a) := by
  unfold branch
  infer_instance

theorem branch_le (m : Measure Ω) (s : Ω → A) {q : Ω → ℝ} (hq : Measurable q) (a : A) :
    branch m s q a ≤ m.map q :=
  Measure.map_mono Measure.restrict_le_self hq

variable [MeasurableSpace A]

theorem measurableSet_cyl [MeasurableSingletonClass A] {s : Ω → A} (hs : Measurable s) (a : A) :
    MeasurableSet (cyl s a) :=
  hs (measurableSet_singleton a)

variable [Countable A] [MeasurableSingletonClass A]

theorem ae_of_branch {m : Measure Ω} {s : Ω → A} (hs : Measurable s) {q : Ω → ℝ}
    (hq : Measurable q) {P : A → ℝ → Prop} (h : ∀ a, ∀ᵐ z ∂branch m s q a, P a z) :
    ∀ᵐ x ∂m, P (s x) (q x) := by
  have h' : ∀ a, ∀ᵐ x ∂m.restrict (cyl s a), P (s x) (q x) := by
    intro a
    filter_upwards [ae_of_ae_map hq.aemeasurable (h a),
      ae_restrict_mem (measurableSet_cyl hs a)] with x hx hxa
    rw [show s x = a from hxa]
    exact hx
  have h'' := (ae_restrict_iUnion_iff (cyl s) _).2 h'
  rwa [iUnion_cyl, Measure.restrict_univ] at h''

theorem measurable_of_index {s : Ω → A} (hs : Measurable s) {q : Ω → ℝ} (hq : Measurable q)
    {G : A → ℝ → ℝ} (hG : ∀ a, Measurable (G a)) : Measurable fun x => G (s x) (q x) :=
  (measurable_from_prod_countable_right (f := fun z : A × ℝ => G z.1 z.2) hG).comp
    (hs.prodMk hq)

theorem measurable_of_index' {s : Ω → A} (hs : Measurable s) {F : A → Ω → ℝ}
    (hF : ∀ a, Measurable (F a)) : Measurable fun x => F (s x) x :=
  (measurable_from_prod_countable_right (f := fun z : A × Ω => F z.1 z.2) hF).comp
    (hs.prodMk measurable_id)

omit [Countable A] in

theorem integrable_of_branch [Finite A] {m : Measure Ω} {s : Ω → A} (hs : Measurable s)
    {q : Ω → ℝ} (hq : Measurable q) {G : A → ℝ → ℝ} (hGm : ∀ a, Measurable (G a))
    (hGi : ∀ a, Integrable (G a) (branch m s q a)) :
    Integrable (fun x => G (s x) (q x)) m := by
  rw [← integrableOn_univ, ← iUnion_cyl s, integrableOn_finite_iUnion]
  intro a
  have h1 : Integrable (G a ∘ q) (m.restrict (cyl s a)) :=
    (integrable_map_measure (hGm a).aestronglyMeasurable hq.aemeasurable).1 (hGi a)
  refine h1.congr ?_
  filter_upwards [ae_restrict_mem (measurableSet_cyl hs a)] with x hx
  simp [show s x = a from hx]

end Branch

/-- A bounded real coding satisfying `p x = c (s x) * p (T x) + t (s x)`,
with nonzero similarity ratios bounded in absolute value by a constant below one. -/
structure Coding (Ω A : Type*) [MeasurableSpace Ω] [MeasurableSpace A] where

  T : Ω → Ω

  s : Ω → A

  p : Ω → ℝ

  c : A → ℝ

  t : A → ℝ

  r : ℝ

  B : ℝ

  measurable_T : Measurable T

  measurable_s : Measurable s

  measurable_p : Measurable p

  c_ne_zero : ∀ a, c a ≠ 0

  abs_c_le : ∀ a, |c a| ≤ r

  r_lt_one : r < 1

  abs_p_le : ∀ x, |p x| ≤ B

  p_eq : ∀ x, p x = c (s x) * p (T x) + t (s x)

namespace Coding

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] (C : Coding Ω A)
  (m : Measure Ω)

def R0 : ℝ := 2 * |C.B| + 1

theorem R0_pos : 0 < C.R0 := by
  unfold R0
  positivity

noncomputable def rad (n : ℕ) (x : Ω) : ℝ :=
  C.R0 * ∏ j ∈ Finset.range n, |C.c (C.s (C.T^[j] x))|

@[simp] theorem rad_zero (x : Ω) : C.rad 0 x = C.R0 := by
  simp [rad]

theorem rad_succ (n : ℕ) (x : Ω) : C.rad (n + 1) x = |C.c (C.s x)| * C.rad n (C.T x) := by
  simp only [rad, Finset.prod_range_succ', Function.iterate_succ_apply,
    Function.iterate_zero_apply]
  ring

theorem rad_succ' (n : ℕ) (x : Ω) :
    C.rad (n + 1) x = C.rad n x * |C.c (C.s (C.T^[n] x))| := by
  simp only [rad, Finset.prod_range_succ]
  ring

theorem rad_pos (n : ℕ) (x : Ω) : 0 < C.rad n x :=
  mul_pos C.R0_pos (Finset.prod_pos fun _ _ => abs_pos.2 (C.c_ne_zero _))

theorem abs_c_le_one (a : A) : |C.c a| ≤ 1 :=
  (C.abs_c_le a).trans C.r_lt_one.le

theorem rad_le (n : ℕ) (x : Ω) : C.rad n x ≤ C.R0 := by
  unfold rad
  calc C.R0 * ∏ j ∈ Finset.range n, |C.c (C.s (C.T^[j] x))| ≤ C.R0 * 1 :=
        mul_le_mul_of_nonneg_left
          (Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun _ _ => C.abs_c_le_one _)
          C.R0_pos.le
    _ = C.R0 := mul_one _

theorem rad_antitone (x : Ω) : Antitone fun n => C.rad n x := by
  apply antitone_nat_of_succ_le
  intro n
  rw [rad_succ']
  exact mul_le_of_le_one_right (C.rad_pos n x).le (C.abs_c_le_one _)

theorem rad_le_pow (n : ℕ) (x : Ω) : C.rad n x ≤ C.R0 * C.r ^ n := by
  unfold rad
  apply mul_le_mul_of_nonneg_left _ C.R0_pos.le
  calc ∏ j ∈ Finset.range n, |C.c (C.s (C.T^[j] x))| ≤ ∏ _j ∈ Finset.range n, C.r :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun _ _ => C.abs_c_le _
    _ = C.r ^ n := by simp

theorem tendsto_rad (x : Ω) : Tendsto (fun n => C.rad n x) atTop (𝓝[>] 0) := by
  have hr : 0 ≤ C.r := (abs_nonneg _).trans (C.abs_c_le (C.s x))
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Eventually.of_forall fun n => C.rad_pos n x⟩
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr C.r_lt_one).const_mul C.R0
  rw [mul_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun n => (C.rad_pos n x).le) (fun n => C.rad_le_pow n x)

noncomputable def proj : Measure ℝ := m.map C.p

noncomputable def kQ (a : A) : Measure ℝ := branch m C.s C.p a

noncomputable def kR (a : A) : Measure ℝ := branch m C.s (C.p ∘ C.T) a

instance [IsFiniteMeasure m] : IsFiniteMeasure (C.proj m) := by
  unfold proj
  infer_instance

instance [IsFiniteMeasure m] (a : A) : IsFiniteMeasure (C.kQ m a) := by
  unfold kQ
  infer_instance

instance [IsFiniteMeasure m] (a : A) : IsFiniteMeasure (C.kR m a) := by
  unfold kR
  infer_instance

theorem kQ_le (a : A) : C.kQ m a ≤ C.proj m :=
  branch_le m C.s C.measurable_p a

theorem kR_le (hm : MeasurePreserving C.T m m) (a : A) : C.kR m a ≤ C.proj m := by
  have h := branch_le m C.s (C.measurable_p.comp C.measurable_T) a
  rwa [← Measure.map_map C.measurable_p C.measurable_T, hm.map_eq] at h

theorem dist_p_of_s_eq {x y : Ω} (h : C.s y = C.s x) :
    dist (C.p y) (C.p x) = |C.c (C.s x)| * dist (C.p (C.T y)) (C.p (C.T x)) := by
  rw [Real.dist_eq, Real.dist_eq, C.p_eq y, C.p_eq x, h, ← abs_mul]
  congr 1
  ring

theorem branch_closedBall_scaled [MeasurableSingletonClass A] (x : Ω) (ρ : ℝ) :
    C.kQ m (C.s x) (closedBall (C.p x) (|C.c (C.s x)| * ρ)) =
      C.kR m (C.s x) (closedBall (C.p (C.T x)) ρ) := by
  have hpT : Measurable (C.p ∘ C.T) := C.measurable_p.comp C.measurable_T
  unfold kQ kR branch
  rw [Measure.map_apply C.measurable_p measurableSet_closedBall,
    Measure.map_apply hpT measurableSet_closedBall,
    Measure.restrict_apply (C.measurable_p measurableSet_closedBall),
    Measure.restrict_apply (hpT measurableSet_closedBall)]
  congr 1
  ext y
  simp only [mem_inter_iff, mem_preimage, mem_closedBall, cyl, mem_singleton_iff,
    Function.comp_apply]
  refine and_congr_left fun hy => ?_
  rw [C.dist_p_of_s_eq hy]
  exact mul_le_mul_iff_right₀ (abs_pos.2 (C.c_ne_zero _))

noncomputable def info (x : Ω) (ρ : ℝ) : ℝ :=
  ExactOverlaps.ballInformation (C.proj m) (C.p x) ρ

theorem info_R0 [IsProbabilityMeasure m] (x : Ω) : C.info m x C.R0 = 0 := by
  have h : C.p ⁻¹' closedBall (C.p x) C.R0 = univ := by
    ext y
    simp only [mem_preimage, mem_closedBall, Real.dist_eq, mem_univ, iff_true]
    have hy := (C.abs_p_le y).trans (le_abs_self C.B)
    have hx := (C.abs_p_le x).trans (le_abs_self C.B)
    calc |C.p y - C.p x| ≤ |C.p y| + |C.p x| := abs_sub _ _
      _ ≤ C.R0 := by unfold R0; linarith
  unfold info ExactOverlaps.ballInformation proj
  rw [Measure.map_apply C.measurable_p measurableSet_closedBall, h, measure_univ]
  simp

theorem info_step [MeasurableSingletonClass A] (hm : MeasurePreserving C.T m m)
    [IsFiniteMeasure m] {x : Ω} {ρ : ℝ}
    (hpos : 0 < C.kR m (C.s x) (closedBall (C.p (C.T x)) ρ)) :
    C.info m x (|C.c (C.s x)| * ρ) =
      C.info m (C.T x) ρ + ratioInfo (C.kR m (C.s x)) (C.proj m) (C.p (C.T x)) ρ -
        ratioInfo (C.kQ m (C.s x)) (C.proj m) (C.p x) (|C.c (C.s x)| * ρ) := by
  have hK := C.branch_closedBall_scaled m x ρ
  set K := C.kR m (C.s x) (closedBall (C.p (C.T x)) ρ) with hKdef
  set U := C.proj m (closedBall (C.p x) (|C.c (C.s x)| * ρ)) with hU
  set V := C.proj m (closedBall (C.p (C.T x)) ρ) with hV
  have hKU : K ≤ U := hK ▸ C.kQ_le m (C.s x) _
  have hKV : K ≤ V := C.kR_le m hm (C.s x) _
  have hKt : K ≠ ⊤ := measure_ne_top _ _
  have hUt : U ≠ ⊤ := measure_ne_top _ _
  have hVt : V ≠ ⊤ := measure_ne_top _ _
  have hK0 : 0 < K.toReal := ENNReal.toReal_pos hpos.ne' hKt
  have hU0 : 0 < U.toReal := hK0.trans_le (ENNReal.toReal_mono hUt hKU)
  have hV0 : 0 < V.toReal := hK0.trans_le (ENNReal.toReal_mono hVt hKV)
  unfold info ratioInfo ExactOverlaps.ballInformation
  rw [hK, ENNReal.toReal_div, ENNReal.toReal_div, Real.log_div hK0.ne' hV0.ne',
    Real.log_div hK0.ne' hU0.ne']
  ring

noncomputable def incr : ℕ → Ω → ℝ
  | 0, _ => 0
  | k + 1, x => ratioInfo (C.kR m (C.s x)) (C.proj m) (C.p (C.T x)) (C.rad k (C.T x)) -
      ratioInfo (C.kQ m (C.s x)) (C.proj m) (C.p x) (C.rad (k + 1) x)

noncomputable def incrLim (x : Ω) : ℝ :=
  densityInfo (C.kR m (C.s x)) (C.proj m) (C.p (C.T x)) -
    densityInfo (C.kQ m (C.s x)) (C.proj m) (C.p x)

theorem info_rad_eq_sum [MeasurableSingletonClass A] (hm : MeasurePreserving C.T m m)
    [IsProbabilityMeasure m] :
    ∀ (n : ℕ) (x : Ω), (∀ j : ℕ, ∀ ρ : ℝ, 0 < ρ →
      0 < C.kR m (C.s (C.T^[j] x)) (closedBall (C.p (C.T (C.T^[j] x))) ρ)) →
      C.info m x (C.rad n x) =
        ∑ j ∈ Finset.range n, C.incr m (n - j) (C.T^[j] x)
  | 0, x, _ => by simp [C.info_R0 m x]
  | n + 1, x, hall => by
    have ih := info_rad_eq_sum hm n (C.T x) fun j ρ hρ => by
      simpa only [Function.iterate_succ_apply] using hall (j + 1) ρ hρ
    rw [Finset.sum_range_succ', rad_succ,
      C.info_step m hm (by simpa using hall 0 (C.rad n (C.T x)) (C.rad_pos n (C.T x))), ih]
    simp only [Function.iterate_succ_apply, Nat.add_sub_add_right, Nat.sub_zero,
      Function.iterate_zero_apply, incr, rad_succ]
    ring

section Finite

variable [Fintype A] [MeasurableSingletonClass A]

theorem measurable_rad (n : ℕ) : Measurable (C.rad n) := by
  unfold rad
  refine measurable_const.mul (Finset.measurable_prod _ fun j _ => ?_)
  exact (Measurable.of_discrete (f := fun a => |C.c a|)).comp
    (C.measurable_s.comp (C.measurable_T.iterate j))

theorem measurable_incr [IsFiniteMeasure m] (k : ℕ) : Measurable (C.incr m k) := by
  cases k with
  | zero => exact measurable_const
  | succ k =>
    have hpT : Measurable (C.p ∘ C.T) := C.measurable_p.comp C.measurable_T
    have h1 : Measurable fun x =>
        ratioInfo (C.kR m (C.s x)) (C.proj m) (C.p (C.T x)) (C.rad k (C.T x)) :=
      measurable_of_index' C.measurable_s fun _ =>
        measurable_ratioInfo _ _ hpT ((C.measurable_rad k).comp C.measurable_T)
    have h2 : Measurable fun x =>
        ratioInfo (C.kQ m (C.s x)) (C.proj m) (C.p x) (C.rad (k + 1) x) :=
      measurable_of_index' C.measurable_s fun _ =>
        measurable_ratioInfo _ _ C.measurable_p (C.measurable_rad (k + 1))
    exact h1.sub h2

theorem measurable_incrLim : Measurable (C.incrLim m) :=
  (measurable_of_index C.measurable_s (C.measurable_p.comp C.measurable_T)
      fun _ => measurable_densityInfo _ _).sub
    (measurable_of_index C.measurable_s C.measurable_p fun _ => measurable_densityInfo _ _)

theorem ae_tendsto_incr (hm : MeasurePreserving C.T m m) [IsFiniteMeasure m] :
    ∀ᵐ x ∂m, Tendsto (fun k => C.incr m k x) atTop (𝓝 (C.incrLim m x)) := by
  have hpT : Measurable (C.p ∘ C.T) := C.measurable_p.comp C.measurable_T
  have hQ := ae_of_branch C.measurable_s C.measurable_p
    (P := fun a z => Tendsto (fun ρ => ratioInfo (C.kQ m a) (C.proj m) z ρ) (𝓝[>] 0)
      (𝓝 (densityInfo (C.kQ m a) (C.proj m) z)))
    fun a => ae_tendsto_ratioInfo _ _ (C.kQ_le m a)
  have hR := ae_of_branch C.measurable_s hpT
    (P := fun a z => Tendsto (fun ρ => ratioInfo (C.kR m a) (C.proj m) z ρ) (𝓝[>] 0)
      (𝓝 (densityInfo (C.kR m a) (C.proj m) z)))
    fun a => ae_tendsto_ratioInfo _ _ (C.kR_le m hm a)
  filter_upwards [hQ, hR] with x hx hx'
  rw [← tendsto_add_atTop_iff_nat 1]
  have h1 := hx'.comp (C.tendsto_rad (C.T x))
  have h2 := hx.comp ((tendsto_add_atTop_iff_nat 1).2 (C.tendsto_rad x))
  exact h1.sub h2

theorem exists_incr_envelope (hm : MeasurePreserving C.T m m) [IsProbabilityMeasure m] :
    ∃ G : Ω → ℝ, Integrable G m ∧
      ∀ᵐ x ∂m, (∀ k, |C.incr m k x| ≤ G x) ∧ |C.incrLim m x| ≤ G x := by
  have hpT : Measurable (C.p ∘ C.T) := C.measurable_p.comp C.measurable_T
  choose GQ hGQm hGQi hGQ0 hGQ using fun a =>
    ExactOverlaps.exists_integrable_ballInformation_envelope (C.kQ m a) (C.proj m)
      (C.kQ_le m a) C.R0
  choose GR hGRm hGRi hGR0 hGR using fun a =>
    ExactOverlaps.exists_integrable_ballInformation_envelope (C.kR m a) (C.proj m)
      (C.kR_le m hm a) C.R0
  refine ⟨fun x => GR (C.s x) (C.p (C.T x)) + GQ (C.s x) (C.p x),
    (integrable_of_branch C.measurable_s hpT hGRm hGRi).add
      (integrable_of_branch C.measurable_s C.measurable_p hGQm hGQi), ?_⟩
  have hQ := ae_of_branch C.measurable_s C.measurable_p (P := fun a z => ∀ ρ : ℝ, 0 < ρ →
      ρ ≤ C.R0 → |Real.log (C.kQ m a (closedBall z ρ) / C.proj m (closedBall z ρ)).toReal| ≤
        GQ a z) hGQ
  have hR := ae_of_branch C.measurable_s hpT (P := fun a z => ∀ ρ : ℝ, 0 < ρ →
      ρ ≤ C.R0 → |Real.log (C.kR m a (closedBall z ρ) / C.proj m (closedBall z ρ)).toReal| ≤
        GR a z) hGR
  have hk : ∀ᵐ x ∂m, ∀ k,
      |C.incr m k x| ≤ GR (C.s x) (C.p (C.T x)) + GQ (C.s x) (C.p x) := by
    filter_upwards [hQ, hR] with x hx hx'
    intro k
    cases k with
    | zero => simpa [incr] using add_nonneg (hGR0 _ _) (hGQ0 _ _)
    | succ k =>
      simp only [incr]
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · simpa only [ratioInfo, abs_neg, Function.comp_apply] using
          hx' _ (C.rad_pos k (C.T x)) (C.rad_le k (C.T x))
      · simpa only [ratioInfo, abs_neg] using hx _ (C.rad_pos (k + 1) x) (C.rad_le (k + 1) x)
  filter_upwards [hk, C.ae_tendsto_incr m hm] with x hx hlim
  exact ⟨hx, le_of_tendsto ((continuous_abs.tendsto _).comp hlim) (Eventually.of_forall hx)⟩

end Finite

noncomputable def logRatio (x : Ω) : ℝ := Real.log |C.c (C.s x)|

theorem logRatio_le (x : Ω) : C.logRatio x ≤ C.r - 1 := by
  have h := Real.log_le_sub_one_of_pos (abs_pos.2 (C.c_ne_zero (C.s x)))
  unfold logRatio
  linarith [C.abs_c_le (C.s x)]

section Finite

variable [Fintype A] [MeasurableSingletonClass A]

theorem measurable_logRatio : Measurable C.logRatio :=
  (Measurable.of_discrete (f := fun a => Real.log |C.c a|)).comp C.measurable_s

theorem integrable_logRatio [IsFiniteMeasure m] : Integrable C.logRatio m := by
  refine Integrable.of_bound C.measurable_logRatio.aestronglyMeasurable
    (∑ a, abs (Real.log |C.c a|)) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun a => abs (Real.log |C.c a|))
    (fun _ _ => abs_nonneg _) (Finset.mem_univ (C.s x))

theorem lyap_pos [IsProbabilityMeasure m] : 0 < -∫ x, C.logRatio x ∂m := by
  have h : ∫ x, C.logRatio x ∂m ≤ ∫ _x, (C.r - 1) ∂m :=
    integral_mono (C.integrable_logRatio m) (integrable_const _) C.logRatio_le
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  linarith [C.r_lt_one]

theorem ae_tendsto_log_rad [IsProbabilityMeasure m] (hT : Ergodic C.T m) :
    ∀ᵐ x ∂m, Tendsto (fun n : ℕ => -Real.log (C.rad n x) / n) atTop
      (𝓝 (-∫ x, C.logRatio x ∂m)) := by
  filter_upwards [birkhoff_ergodic hT (C.integrable_logRatio m)] with x hx
  have h0 : Tendsto (fun n : ℕ => -Real.log C.R0 / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h := h0.sub hx
  rw [zero_sub] at h
  refine h.congr fun n => ?_
  have hprod : Real.log (∏ j ∈ Finset.range n, |C.c (C.s (C.T^[j] x))|) =
      birkhoffSum C.T C.logRatio n x := by
    rw [Real.log_prod fun j _ => (abs_pos.2 (C.c_ne_zero _)).ne']
    rfl
  rw [rad, Real.log_mul C.R0_pos.ne'
    (Finset.prod_pos fun j _ => abs_pos.2 (C.c_ne_zero _)).ne', hprod, birkhoffAverage,
    smul_eq_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · field_simp
    ring

/-- The image of an ergodic invariant probability measure under a finite
self-similar coding on the real line is exact-dimensional. -/
theorem exists_isExactDim [IsProbabilityMeasure m] (hT : Ergodic C.T m) :
    ∃ d : ℝ, ExactOverlaps.HasExactDimension (m.map C.p) d := by
  have hm := hT.toMeasurePreserving
  have : IsProbabilityMeasure (C.proj m) := by
    unfold proj
    infer_instance
  obtain ⟨G, hGi, hG⟩ := C.exists_incr_envelope m hm
  have htri := ae_tendsto_triangularAverage hT (C.measurable_incr m) (C.measurable_incrLim m)
    hGi hG (C.ae_tendsto_incr m hm)
  have hbase := ae_of_branch C.measurable_s (C.measurable_p.comp C.measurable_T)
    (P := fun a z => ∀ ρ : ℝ, 0 < ρ → 0 < C.kR m a (closedBall z ρ))
    fun _ => ExactOverlaps.ae_closedBall_measure_pos _
  have hall : ∀ᵐ x ∂m, ∀ j : ℕ, ∀ ρ : ℝ, 0 < ρ →
      0 < C.kR m (C.s (C.T^[j] x)) (closedBall (C.p (C.T (C.T^[j] x))) ρ) :=
    ae_all_iff.2 fun j => (hm.iterate j).quasiMeasurePreserving.ae hbase
  have hball : ∀ᵐ x ∂m, ∀ t : ℝ, 0 < t → 0 < C.proj m (closedBall (C.p x) t) :=
    ae_of_ae_map C.measurable_p.aemeasurable (ExactOverlaps.ae_closedBall_measure_pos _)
  refine ⟨(∫ x, C.incrLim m x ∂m) / (-∫ x, C.logRatio x ∂m),
    ExactOverlaps.hasExactDimension_of_map_ae_local_limit m (C.proj m) C.measurable_p rfl ?_⟩
  filter_upwards [htri, hall, hball, C.ae_tendsto_log_rad m hT] with x hx hxall hxball hxrate
  refine ExactOverlaps.local_dimension_of_sampled_information (C.proj m) (C.p x) hxball
    (C.rad_pos · x) (C.rad_antitone x) (tendsto_nhdsWithin_iff.1 (C.tendsto_rad x)).1
    (C.lyap_pos m) (hx.congr fun n => ?_) hxrate
  rw [ExactOverlaps.Ergodic.triangularAverage, ← C.info_rad_eq_sum m hm n x hxall]
  rfl

end Finite

end Coding

end FengHu

end FractalGeometry.SelfSimilar
