module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.BallRatioMaximal
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.MeasurableEnvelope
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

set_option maxSynthPendingDepth 3

/-!
An integrable envelope for logarithmic ball likelihood ratios. This is a
uniform statement over every positive radius up to a fixed bound, rather
than integrability only of the limiting Radon--Nikodym information.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.BallInformationEnvelope`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal

namespace ExactOverlaps

theorem exists_integrable_ballInformation_envelope (κ ν : Measure ℝ)
    [IsFiniteMeasure κ] [IsFiniteMeasure ν] (hκν : κ ≤ ν) (R : ℝ) :
    ∃ G : ℝ → ℝ, Measurable G ∧ Integrable G κ ∧ (∀ x, 0 ≤ G x) ∧
      ∀ᵐ x ∂κ, ∀ r : ℝ, 0 < r → r ≤ R →
        |Real.log (κ (closedBall x r) / ν (closedBall x r)).toReal| ≤ G x := by
  let q : ℝ≥0 := ⟨Real.exp (-1), (Real.exp_pos _).le⟩
  have hq : q < 1 := by
    change Real.exp (-1) < 1
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  let E : ℕ → Set ℝ := fun n ↦ {x | ∃ r, 0 < r ∧ r ≤ R ∧
    κ (closedBall x r) ≤ (q : ℝ≥0∞) ^ n * ν (closedBall x r)}
  obtain ⟨N, hN⟩ := exists_ballRatio_maximal_constant
  have hE : (∑' n : ℕ, (n + 1 : ℝ≥0∞) * κ (E n)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := (N : ℝ≥0∞) * ν Set.univ *
      ∑' n : ℕ, (n + 1 : ℝ≥0∞) * (q : ℝ≥0∞) ^ n)
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by finiteness) (measure_ne_top _ _))
        (weighted_geometric_tsum_ne_top hq)
    · rw [← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro n
      calc
        (n + 1 : ℝ≥0∞) * κ (E n) ≤
            (n + 1 : ℝ≥0∞) * ((N : ℝ≥0∞) * ((q : ℝ≥0∞) ^ n * ν Set.univ)) := by
          exact mul_le_mul le_rfl (hN κ ν R ((q : ℝ≥0∞) ^ n)) bot_le bot_le
        _ = _ := by ring
  obtain ⟨G, hmG, hiG, hG0, hG⟩ :=
    exists_integrable_envelope_of_weighted_measure_tsum κ E hE
  refine ⟨G, hmG, hiG, hG0, ?_⟩
  filter_upwards [hG] with x hx
  intro r hr hrR
  let a := κ (closedBall x r)
  let b := ν (closedBall x r)
  have hab : a ≤ b := hκν _
  have ha : a ≠ ⊤ := measure_ne_top _ _
  have hb : b ≠ ⊤ := measure_ne_top _ _
  have hab1 : (a / b).toReal ≤ 1 := by
    have hh : a / b ≤ 1 := ENNReal.div_le_of_le_mul (by simpa using hab)
    exact (ENNReal.toReal_mono ENNReal.one_ne_top hh).trans_eq ENNReal.toReal_one
  have hl : Real.log (a / b).toReal ≤ 0 := Real.log_nonpos ENNReal.toReal_nonneg hab1
  change |Real.log (a / b).toReal| ≤ G x
  rw [abs_of_nonpos hl]
  by_cases hz : (a / b).toReal = 0
  · simpa only [hz, Real.log_zero, neg_zero] using hG0 x
  have hp : 0 < (a / b).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)
  let n : ℕ := ⌊-Real.log (a / b).toReal⌋₊
  have hn : (n : ℝ) ≤ -Real.log (a / b).toReal := Nat.floor_le (neg_nonneg.mpr hl)
  have hn' : -Real.log (a / b).toReal < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hbn : b ≠ 0 := by
    intro h
    have haz : a = 0 := le_antisymm (hab.trans_eq h) bot_le
    exact hz (by simp only [haz, h, ENNReal.zero_div, ENNReal.toReal_zero])
  have hpow : ((q : ℝ≥0∞) ^ n).toReal = Real.exp (-(n : ℝ)) := by
    rw [ENNReal.toReal_pow]
    change Real.exp (-1) ^ n = Real.exp (-(n : ℝ))
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hratio : a / b ≤ (q : ℝ≥0∞) ^ n := by
    apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top ha hbn) (by finiteness)).mp
    rw [hpow]
    calc
      (a / b).toReal = Real.exp (Real.log (a / b).toReal) := (Real.exp_log hp).symm
      _ ≤ Real.exp (-(n : ℝ)) := Real.exp_le_exp.mpr (by linarith)
  have hxE : x ∈ E n := ⟨r, hr, hrR, (ENNReal.div_le_iff hbn hb).mp hratio⟩
  exact hn'.le.trans (hx n hxE)

end ExactOverlaps
