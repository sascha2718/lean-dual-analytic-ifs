module

public import Mathlib.Dynamics.BirkhoffSum.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Continuity

set_option maxSynthPendingDepth 3

/-!
The finite Hopf maximal inequality for a measure-preserving transformation.
This is the maximal estimate needed to pass from finite-block strong laws
to pointwise averaging for integrable Bernoulli observables.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.MaximalErgodic`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps.Ergodic

variable {Ω : Type*}

/-- Maximum of the first `n` orbit sums, including the empty sum. -/
noncomputable def orbitMaximum (T : Ω → Ω) (f : Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n + 1, x => max 0 (f x + orbitMaximum T f n (T x))

theorem orbitMaximum_nonneg (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (x : Ω) :
    0 ≤ orbitMaximum T f n x := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_left _ _

theorem orbitMaximum_mono (T : Ω → Ω) (f : Ω → ℝ) (x : Ω) :
    Monotone (fun n ↦ orbitMaximum T f n x) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n generalizing x with
  | zero => exact orbitMaximum_nonneg T f 1 x
  | succ n ih => exact max_le_max le_rfl (add_le_add le_rfl (ih (T x)))

theorem birkhoffSum_le_orbitMaximum (T : Ω → Ω) (f : Ω → ℝ)
    {k n : ℕ} (hkn : k ≤ n) (x : Ω) :
    birkhoffSum T f k x ≤ orbitMaximum T f n x := by
  induction n generalizing k x with
  | zero => simpa only [Nat.le_zero.mp hkn, birkhoffSum_zero_apply] using
      orbitMaximum_nonneg T f 0 x
  | succ n ih =>
      cases k with
      | zero => simpa using orbitMaximum_nonneg T f (n + 1) x
      | succ k =>
          rw [birkhoffSum_succ_apply', orbitMaximum]
          exact le_trans (add_le_add le_rfl (ih (Nat.le_of_succ_le_succ hkn) (T x)))
            (le_max_right _ _)

theorem orbitMaximum_attained (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (x : Ω) :
    ∃ k ≤ n, orbitMaximum T f n x = birkhoffSum T f k x := by
  induction n generalizing x with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
      by_cases h : f x + orbitMaximum T f n (T x) ≤ 0
      · exact ⟨0, Nat.zero_le _, by simp [orbitMaximum, max_eq_left h]⟩
      · obtain ⟨k, hk, heq⟩ := ih (T x)
        refine ⟨k + 1, Nat.add_le_add_right hk 1, ?_⟩
        rw [orbitMaximum, max_eq_right (le_of_not_ge h), birkhoffSum_succ_apply', heq]

theorem orbitMaximum_pos_iff (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (x : Ω) :
    0 < orbitMaximum T f n x ↔ ∃ k ≤ n, 0 < birkhoffSum T f k x := by
  constructor
  · intro h
    obtain ⟨k, hk, heq⟩ := orbitMaximum_attained T f n x
    exact ⟨k, hk, heq ▸ h⟩
  · rintro ⟨k, hk, hpos⟩
    exact lt_of_lt_of_le hpos (birkhoffSum_le_orbitMaximum T f hk x)

/-- The pointwise telescoping estimate in Hopf's argument. -/
theorem orbitMaximum_indicator_bound (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (x : Ω) :
    orbitMaximum T f n x - orbitMaximum T f n (T x) ≤
      {y | 0 < orbitMaximum T f n y}.indicator f x := by
  classical
  by_cases h : 0 < orbitMaximum T f n x
  · rw [Set.indicator_of_mem (show x ∈ {y | 0 < orbitMaximum T f n y} from h)]
    cases n with
    | zero => simp [orbitMaximum] at h
    | succ n =>
        have hp : 0 < f x + orbitMaximum T f n (T x) := by
          simpa only [orbitMaximum, lt_max_iff, lt_self_iff_false, false_or] using h
        rw [orbitMaximum, max_eq_right hp.le]
        have hm := orbitMaximum_mono T f (T x) (Nat.le_succ n)
        linarith
  · rw [Set.indicator_of_notMem (show x ∉ {y | 0 < orbitMaximum T f n y} from h)]
    have hz : orbitMaximum T f n x = 0 :=
      le_antisymm (le_of_not_gt h) (orbitMaximum_nonneg T f n x)
    rw [hz]
    linarith [orbitMaximum_nonneg T f n (T x)]

variable [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω} {f : Ω → ℝ}

theorem measurable_orbitMaximum (hT : Measurable T) (hf : Measurable f) (n : ℕ) :
    Measurable (orbitMaximum T f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_const.max (hf.add (ih.comp hT))

theorem integrable_orbitMaximum (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    (n : ℕ) : Integrable (orbitMaximum T f n) μ := by
  induction n with
  | zero => exact integrable_zero _ _ _
  | succ n ih =>
      exact (integrable_zero Ω ℝ μ).sup (hf.add (hT.integrable_comp_of_integrable ih))

/-- Hopf's finite maximal ergodic inequality. -/
theorem integral_positive_orbitMaximum_nonneg (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) (n : ℕ) :
    0 ≤ ∫ x in {y | 0 < orbitMaximum T f n y}, f x ∂μ := by
  have hF := integrable_orbitMaximum hT hf n
  have hE : MeasurableSet {y | 0 < orbitMaximum T f n y} :=
    measurableSet_lt measurable_const (measurable_orbitMaximum hT.measurable hfm n)
  have hsame : ∫ x, orbitMaximum T f n (T x) ∂μ = ∫ x, orbitMaximum T f n x ∂μ := by
    have hFm : AEStronglyMeasurable (orbitMaximum T f n) (Measure.map T μ) := by
      rw [hT.map_eq]
      exact hF.aestronglyMeasurable
    rw [← integral_map hT.measurable.aemeasurable hFm, hT.map_eq]
  have h := integral_mono (hF.sub (hT.integrable_comp_of_integrable hF))
    (hf.indicator hE) (orbitMaximum_indicator_bound T f n)
  change (∫ x, orbitMaximum T f n x - orbitMaximum T f n (T x) ∂μ) ≤
    ∫ x, {y | 0 < orbitMaximum T f n y}.indicator f x ∂μ at h
  have hcomp : Integrable (fun x ↦ orbitMaximum T f n (T x)) μ := by
    simpa only [Function.comp_def] using hT.integrable_comp_of_integrable hF
  rw [integral_sub hF hcomp, hsame, sub_self,
    integral_indicator hE] at h
  exact h

end ExactOverlaps.Ergodic
