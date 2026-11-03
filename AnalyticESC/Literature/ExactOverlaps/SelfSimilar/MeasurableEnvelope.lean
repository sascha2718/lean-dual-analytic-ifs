module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Analysis.SpecificLimits.Normed

set_option maxSynthPendingDepth 3

/-!
A measurable integrable envelope for a sequence of possibly nonmeasurable
exceptional sets with summable weighted outer measures. Measurable hulls
avoid imposing measurability on an uncountable supremum over ball radii.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.MeasurableEnvelope`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ExactOverlaps

theorem exists_integrable_envelope_of_weighted_measure_tsum
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (E : ℕ → Set Ω)
    (hE : (∑' n : ℕ, (n + 1 : ℝ≥0∞) * μ (E n)) ≠ ⊤) :
    ∃ G : Ω → ℝ, Measurable G ∧ Integrable G μ ∧ (∀ x, 0 ≤ G x) ∧
      ∀ᵐ x ∂μ, ∀ n : ℕ, x ∈ E n → (n : ℝ) + 1 ≤ G x := by
  classical
  let F : ℕ → Ω → ℝ≥0∞ := fun n ↦ (toMeasurable μ (E n)).indicator (fun _ ↦ (n : ℝ≥0∞) + 1)
  have hm : ∀ n, Measurable (F n) := fun n ↦
    measurable_const.indicator (measurableSet_toMeasurable μ (E n))
  let V : Ω → ℝ≥0∞ := fun x ↦ ∑' n, F n x
  have hV : Measurable V := Measurable.tsum hm
  have hi : (∫⁻ x, V x ∂μ) ≠ ⊤ := by
    have heq : (∫⁻ x, V x ∂μ) = ∑' n : ℕ, (n + 1 : ℝ≥0∞) * μ (E n) := by
      rw [show V = fun x ↦ ∑' n, F n x from rfl, lintegral_tsum (fun n ↦ (hm n).aemeasurable)]
      apply tsum_congr
      intro n
      simp only [F, lintegral_indicator (measurableSet_toMeasurable μ (E n)),
        lintegral_const, Measure.restrict_apply_univ, measure_toMeasurable]
    exact heq ▸ hE
  refine ⟨fun x ↦ (V x).toReal, hV.ennreal_toReal,
    integrable_toReal_of_lintegral_ne_top hV.aemeasurable hi,
    fun _ ↦ ENNReal.toReal_nonneg, ?_⟩
  filter_upwards [ae_lt_top' hV.aemeasurable hi] with x hx
  intro n hn
  have hmem := subset_toMeasurable μ (E n) hn
  have hle : (n : ℝ≥0∞) + 1 ≤ V x := by
    calc
      (n : ℝ≥0∞) + 1 = F n x :=
        (Set.indicator_of_mem hmem (fun _ ↦ (n : ℝ≥0∞) + 1)).symm
      _ ≤ V x := ENNReal.le_tsum (f := fun k ↦ F k x) n
  simpa only [ENNReal.toReal_add (by finiteness) ENNReal.one_ne_top,
    ENNReal.toReal_natCast, ENNReal.toReal_one] using ENNReal.toReal_mono hx.ne hle

theorem weighted_geometric_tsum_ne_top {q : ℝ≥0} (hq : q < 1) :
    (∑' n : ℕ, (n + 1 : ℝ≥0∞) * (q : ℝ≥0∞) ^ n) ≠ ⊤ := by
  have hs : Summable (fun n : ℕ ↦ ((n : ℝ) + 1) * (q : ℝ) ^ n) := by
    have hn := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (r := (q : ℝ)) 1
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg q.coe_nonneg] using
        (show (q : ℝ) < 1 from hq))
    have hg := summable_geometric_of_lt_one q.coe_nonneg (show (q : ℝ) < 1 from hq)
    simpa only [pow_one, one_mul, add_mul] using hn.add hg
  have hn : Summable (fun n : ℕ ↦ (n + 1 : ℝ≥0) * q ^ n) :=
    NNReal.summable_coe.mp (by simpa only [NNReal.coe_mul, NNReal.coe_add,
      NNReal.coe_natCast, NNReal.coe_one, NNReal.coe_pow] using hs)
  simpa only [ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_natCast,
    ENNReal.coe_one, ENNReal.coe_pow] using ENNReal.tsum_coe_ne_top_iff_summable.mpr hn

end ExactOverlaps
