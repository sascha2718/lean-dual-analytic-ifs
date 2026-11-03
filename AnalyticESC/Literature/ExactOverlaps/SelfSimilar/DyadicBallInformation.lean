module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.DyadicBallComparison
public import Mathlib.Analysis.SpecialFunctions.Exp

set_option maxSynthPendingDepth 3

/-!
Almost-sure comparison of dyadic cell information with logarithmic ball mass.
Exponential relative errors are summable, so their information cost is an
arbitrarily small multiple of the dyadic level.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.DyadicBallInformation`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Metric Filter
open scoped ENNReal

namespace ExactOverlaps.Entropy

noncomputable def dyadicBallInformation (μ : ProbabilityMeasure ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  -Real.log ((μ : Measure ℝ) (closedBall x ((2 : ℝ) ^ (-(n : ℤ))))).toReal

theorem summable_dyadic_information_threshold {ε : ℝ} (hε : 0 < ε) :
    (∑' n : ℕ, (3 : ℝ≥0∞) * ENNReal.ofReal
      (Real.exp (-(n : ℝ) * ε * Real.log 2))) ≠ ⊤ := by
  have ha : -ε * Real.log 2 < 0 :=
    mul_neg_of_neg_of_pos (neg_neg_of_pos hε) (Real.log_pos (by norm_num))
  have hs := (Real.summable_exp_nat_mul_iff.mpr ha).tsum_ofReal_ne_top
  have he (n : ℕ) : -(n : ℝ) * ε * Real.log 2 = (n : ℝ) * (-ε * Real.log 2) := by ring
  rw [ENNReal.tsum_mul_left]
  apply ENNReal.mul_ne_top (by norm_num)
  simpa only [he] using hs

theorem ae_eventually_information_ball_error_le (μ : ProbabilityMeasure ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(μ : Measure ℝ), ∀ᶠ n : ℕ in atTop,
      0 ≤ dyadicInformation μ n x - dyadicBallInformation μ n x ∧
        dyadicInformation μ n x - dyadicBallInformation μ n x ≤
          (n : ℝ) * ε * Real.log 2 := by
  let t : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (Real.exp (-(n : ℝ) * ε * Real.log 2))
  have ht : (∑' n, 3 * t n) ≠ ⊤ := summable_dyadic_information_threshold hε
  filter_upwards [ae_eventually_cell_ball_mass_bounds μ t ht] with x hx
  filter_upwards [hx] with n hn
  let b : ℝ≥0∞ := (μ : Measure ℝ) (closedBall x ((2 : ℝ) ^ (-(n : ℤ))))
  let c : ℝ≥0∞ := dyadicLaw μ n (dyadicQuantize n x)
  have hbfin : b ≠ ⊤ := measure_ne_top _ _
  have hcfin : c ≠ ⊤ := (dyadicLaw μ n).apply_ne_top _
  have hlow : Real.exp (-(n : ℝ) * ε * Real.log 2) * b.toReal < c.toReal := by
    have h := (ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbfin) hcfin).mpr hn.1
    simpa only [t, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using h
  have hhigh : c.toReal ≤ b.toReal := ENNReal.toReal_mono hbfin hn.2
  have hcpos : 0 < c.toReal := (mul_nonneg (Real.exp_nonneg _) ENNReal.toReal_nonneg).trans_lt hlow
  have hbpos : 0 < b.toReal := hcpos.trans_le hhigh
  have hloglo := Real.log_lt_log (mul_pos (Real.exp_pos _) hbpos) hlow
  rw [Real.log_mul (Real.exp_pos _).ne' hbpos.ne', Real.log_exp] at hloglo
  have hloghi := Real.log_le_log hcpos hhigh
  change 0 ≤ -Real.log c.toReal - -Real.log b.toReal ∧
    -Real.log c.toReal - -Real.log b.toReal ≤ (n : ℝ) * ε * Real.log 2
  constructor <;> linarith

end ExactOverlaps.Entropy
