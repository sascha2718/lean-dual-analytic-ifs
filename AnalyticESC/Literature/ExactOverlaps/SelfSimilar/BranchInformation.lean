module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.BranchDensity
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option maxSynthPendingDepth 3

/-!
Integrability of the conditional branch information. The bound is obtained
from the genuine Radon--Nikodym densities through the bounded entropy
function `-t log t`, rather than assuming logarithmic integrability.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.BranchInformation`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ExactOverlaps.SelfSimilar.System

variable {ι : Type*} [Fintype ι]

noncomputable def branchInformation (S : System ι) (ν : Measure ℝ) (i : ι) (x : ℝ) : ℝ :=
  -Real.log (S.branchDensity ν i x).toReal

theorem measurable_branchInformation (S : System ι) (ν : Measure ℝ) (i : ι) :
    Measurable (S.branchInformation ν i) :=
  ((S.measurable_branchDensity ν i).ennreal_toReal.log).neg

theorem branchDensity_toReal_le_one (S : System ι) {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : S.IsStationary ν) (i : ι) : ∀ᵐ x ∂ν, (S.branchDensity ν i x).toReal ≤ 1 := by
  filter_upwards [S.branchDensity_le_one hν i] with x hx
  exact (ENNReal.toReal_mono ENNReal.one_ne_top hx).trans_eq ENNReal.toReal_one

theorem integrable_branch_negMulLog (S : System ι) {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : S.IsStationary ν) (i : ι) :
    Integrable (fun x ↦ Real.negMulLog (S.branchDensity ν i x).toReal) ν := by
  have hm := Real.continuous_negMulLog.measurable.comp
    (S.measurable_branchDensity ν i).ennreal_toReal
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards [S.branchDensity_toReal_le_one hν i] with x hx
  change ‖Real.negMulLog (S.branchDensity ν i x).toReal‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.negMulLog_nonneg ENNReal.toReal_nonneg hx)]
  exact (Real.negMulLog_le_one_sub_self ENNReal.toReal_nonneg).trans
    (sub_le_self _ ENNReal.toReal_nonneg)

theorem branchDensity_lt_top (S : System ι) {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : S.IsStationary ν) (i : ι) : ∀ᵐ x ∂ν, S.branchDensity ν i x < ⊤ := by
  filter_upwards [S.branchDensity_le_one hν i] with x hx
  exact hx.trans_lt ENNReal.one_lt_top

theorem integrable_branchInformation (S : System ι) {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : S.IsStationary ν) (i : ι) :
    Integrable (S.branchInformation ν i) (S.branchMeasure ν i) := by
  rw [← S.withDensity_branchDensity hν i,
    integrable_withDensity_iff_integrable_smul' (S.measurable_branchDensity ν i)
      (S.branchDensity_lt_top hν i)]
  simpa only [branchInformation, smul_eq_mul, Real.negMulLog_def, mul_neg, neg_mul] using
    S.integrable_branch_negMulLog hν i

theorem integral_branchInformation (S : System ι) {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : S.IsStationary ν) (i : ι) :
    (∫ x, S.branchInformation ν i x ∂S.branchMeasure ν i) =
      ∫ x, Real.negMulLog (S.branchDensity ν i x).toReal ∂ν := by
  rw [← S.withDensity_branchDensity hν i,
    integral_withDensity_eq_integral_toReal_smul (S.measurable_branchDensity ν i)
      (S.branchDensity_lt_top hν i)]
  simp only [branchInformation, smul_eq_mul, Real.negMulLog_def, mul_neg, neg_mul]

theorem branchInformation_nonneg_ae (S : System ι) {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : S.IsStationary ν) (i : ι) :
    ∀ᵐ x ∂S.branchMeasure ν i, 0 ≤ S.branchInformation ν i x := by
  filter_upwards [(S.branchMeasure_absolutelyContinuous hν i).ae_le
    (S.branchDensity_toReal_le_one hν i)] with x hx
  exact neg_nonneg.mpr (Real.log_nonpos ENNReal.toReal_nonneg hx)

end ExactOverlaps.SelfSimilar.System
