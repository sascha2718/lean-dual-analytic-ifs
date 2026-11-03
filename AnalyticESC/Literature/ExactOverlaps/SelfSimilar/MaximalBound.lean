module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.MaximalErgodic
public import Mathlib.Dynamics.BirkhoffSum.Average

set_option maxSynthPendingDepth 3

/-!
The weak L1 bound for the maximal orbit average, deduced from the finite
Hopf inequality and continuity of measure for increasing unions.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.MaximalBound`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace ExactOverlaps.Ergodic

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {T : Ω → Ω} {g : Ω → ℝ}

theorem measure_positive_orbitMaximum_le (hT : MeasurePreserving T μ μ)
    (hgm : Measurable g) (hg : Integrable g μ) (hg0 : 0 ≤ᵐ[μ] g)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    μ {x | 0 < orbitMaximum T (fun y ↦ g y - ε) n x} ≤
      ENNReal.ofReal ((∫ x, g x ∂μ) / ε) := by
  let E : Set Ω := {x | 0 < orbitMaximum T (fun y ↦ g y - ε) n x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    (measurable_orbitMaximum hT.measurable (hgm.sub measurable_const) n)
  have hh := integral_positive_orbitMaximum_nonneg hT (hgm.sub measurable_const)
    (hg.sub (integrable_const ε)) n
  change 0 ≤ ∫ x in E, g x - ε ∂μ at hh
  rw [integral_sub hg.integrableOn (integrable_const ε), setIntegral_const,
    smul_eq_mul] at hh
  have hle : ∫ x in E, g x ∂μ ≤ ∫ x, g x ∂μ := by
    rw [← integral_indicator hE]
    apply integral_mono_ae (hg.indicator hE) hg
    filter_upwards [hg0] with x hx
    change 0 ≤ g x at hx
    by_cases he : x ∈ E
    · simp only [Set.indicator_of_mem he, le_refl]
    · simpa only [Set.indicator_of_notMem he] using hx
  have hb : (μ E).toReal ≤ (∫ x, g x ∂μ) / ε := by
    apply (le_div_iff₀ hε).2
    change μ.real E * ε ≤ _
    linarith
  have h := ENNReal.ofReal_le_ofReal hb
  simpa only [ENNReal.ofReal_toReal (measure_ne_top μ E)] using h

omit [MeasurableSpace Ω] in
theorem birkhoffSum_sub_const (T : Ω → Ω) (g : Ω → ℝ) (ε : ℝ) (n : ℕ) (x : Ω) :
    birkhoffSum T (fun y ↦ g y - ε) n x = birkhoffSum T g n x - (n : ℝ) * ε := by
  simp [birkhoffSum, Finset.sum_sub_distrib]

omit [MeasurableSpace Ω] in
theorem exists_positive_orbitMaximum_iff (T : Ω → Ω) (g : Ω → ℝ)
    {ε : ℝ} (hε : 0 < ε) (x : Ω) :
    (∃ n, 0 < orbitMaximum T (fun y ↦ g y - ε) n x) ↔
      ∃ n, ε < birkhoffAverage ℝ T g n x := by
  simp only [orbitMaximum_pos_iff]
  constructor
  · rintro ⟨n, k, hk, hpos⟩
    rw [birkhoffSum_sub_const] at hpos
    have hk0 : 0 < k := by
      cases k with
      | zero => simp at hpos
      | succ k => exact Nat.succ_pos _
    refine ⟨k, ?_⟩
    rw [birkhoffAverage, smul_eq_mul, ← div_eq_inv_mul]
    apply (lt_div_iff₀ (show 0 < (k : ℝ) by exact_mod_cast hk0)).2
    linarith
  · rintro ⟨n, hn⟩
    have hn0 : 0 < n := by
      cases n with
      | zero => simpa using lt_trans hε hn
      | succ n => exact Nat.succ_pos _
    refine ⟨n, n, le_rfl, ?_⟩
    rw [birkhoffSum_sub_const]
    rw [birkhoffAverage, smul_eq_mul, ← div_eq_inv_mul] at hn
    have h := (lt_div_iff₀ (show 0 < (n : ℝ) by exact_mod_cast hn0)).1 hn
    linarith

/-- Weak L1 control of the entire sequence of nonnegative orbit averages. -/
theorem measure_exists_birkhoffAverage_gt_le (hT : MeasurePreserving T μ μ)
    (hgm : Measurable g) (hg : Integrable g μ) (hg0 : 0 ≤ᵐ[μ] g)
    {ε : ℝ} (hε : 0 < ε) :
    μ {x | ∃ n, ε < birkhoffAverage ℝ T g n x} ≤
      ENNReal.ofReal ((∫ x, g x ∂μ) / ε) := by
  let E : ℕ → Set Ω := fun n ↦ {x | 0 < orbitMaximum T (fun y ↦ g y - ε) n x}
  have hE : Monotone E := by
    intro n m hnm x hx
    exact lt_of_lt_of_le hx (orbitMaximum_mono T (fun y ↦ g y - ε) x hnm)
  have heq : {x | ∃ n, ε < birkhoffAverage ℝ T g n x} = ⋃ n, E n := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, E]
    exact (exists_positive_orbitMaximum_iff T g hε x).symm
  rw [heq, hE.measure_iUnion]
  exact iSup_le fun n ↦ measure_positive_orbitMaximum_le hT hgm hg hg0 hε n

end ExactOverlaps.Ergodic
