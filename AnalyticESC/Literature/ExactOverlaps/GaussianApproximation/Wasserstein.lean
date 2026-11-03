module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic

set_option maxSynthPendingDepth 3

/-!
# The Kantorovich dual distance on real laws with finite first moments

The test functions are actual real functions with Lipschitz constant one.
Pinning them at zero removes irrelevant additive constants. Explicit first-
moment proofs ensure that every expectation in the definition is integrable.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.Wasserstein`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace ExactOverlaps.GaussianApproximation

/-- Unit Lipschitz test functions, normalized by their value at zero. -/
def unitTests : Set (ℝ → ℝ) := {f | LipschitzWith 1 f ∧ f 0 = 0}

lemma zero_mem_unitTests : (fun _ : ℝ ↦ (0 : ℝ)) ∈ unitTests := by
  refine ⟨?_, rfl⟩
  simpa using (LipschitzWith.const (0 : ℝ)).weaken (by norm_num : (0 : ℝ≥0) ≤ 1)

lemma abs_le_of_mem_unitTests {f : ℝ → ℝ} (hf : f ∈ unitTests) (x : ℝ) :
    |f x| ≤ |x| := by
  simpa only [Real.dist_eq, hf.2, sub_zero, NNReal.coe_one, one_mul] using
    hf.1.dist_le_mul x 0

lemma integrable_unitTest (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    {f : ℝ → ℝ} (hf : f ∈ unitTests) : Integrable f (μ : Measure ℝ) := by
  apply hμ.mono hf.1.continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x ↦ by
    simpa only [Real.norm_eq_abs] using abs_le_of_mem_unitTests hf x)

lemma abs_integral_unitTest_le (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    {f : ℝ → ℝ} (hf : f ∈ unitTests) :
    |∫ x, f x ∂(μ : Measure ℝ)| ≤ ∫ x, |x| ∂(μ : Measure ℝ) := by
  apply abs_integral_le_integral_abs.trans
  exact integral_mono (integrable_unitTest μ hμ hf).abs hμ.abs
    (abs_le_of_mem_unitTests hf)

lemma test_discrepancies_bddAbove (μ ν : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    (hν : Integrable (fun x : ℝ ↦ x) (ν : Measure ℝ)) :
    BddAbove ((fun f : ℝ → ℝ ↦
      |(∫ x, f x ∂(μ : Measure ℝ)) - ∫ x, f x ∂(ν : Measure ℝ)|) '' unitTests) := by
  refine ⟨(∫ x, |x| ∂(μ : Measure ℝ)) + ∫ x, |x| ∂(ν : Measure ℝ), ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  exact (abs_sub _ _).trans (add_le_add (abs_integral_unitTest_le μ hμ hf)
    (abs_integral_unitTest_le ν hν hf))

/-- The standard Kantorovich dual definition of the 1-Wasserstein distance. -/
def wasserstein1 (μ ν : ProbabilityMeasure ℝ)
    (_hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    (_hν : Integrable (fun x : ℝ ↦ x) (ν : Measure ℝ)) : ℝ :=
  sSup ((fun f : ℝ → ℝ ↦
    |(∫ x, f x ∂(μ : Measure ℝ)) - ∫ x, f x ∂(ν : Measure ℝ)|) '' unitTests)

lemma abs_integral_sub_le_wasserstein1 (μ ν : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    (hν : Integrable (fun x : ℝ ↦ x) (ν : Measure ℝ))
    {f : ℝ → ℝ} (hf : f ∈ unitTests) :
    |(∫ x, f x ∂(μ : Measure ℝ)) - ∫ x, f x ∂(ν : Measure ℝ)| ≤
      wasserstein1 μ ν hμ hν :=
  le_csSup (test_discrepancies_bddAbove μ ν hμ hν) ⟨f, hf, rfl⟩

lemma wasserstein1_le (μ ν : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    (hν : Integrable (fun x : ℝ ↦ x) (ν : Measure ℝ)) {d : ℝ}
    (hd : ∀ f ∈ unitTests,
      |(∫ x, f x ∂(μ : Measure ℝ)) - ∫ x, f x ∂(ν : Measure ℝ)| ≤ d) :
    wasserstein1 μ ν hμ hν ≤ d := by
  apply csSup_le ((show unitTests.Nonempty from ⟨_, zero_mem_unitTests⟩).image _)
  rintro _ ⟨f, hf, rfl⟩
  exact hd f hf

lemma wasserstein1_nonneg (μ ν : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    (hν : Integrable (fun x : ℝ ↦ x) (ν : Measure ℝ)) :
    0 ≤ wasserstein1 μ ν hμ hν := by
  simpa using abs_integral_sub_le_wasserstein1 μ ν hμ hν zero_mem_unitTests

lemma wasserstein1_self (μ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ)) :
    wasserstein1 μ μ hμ hμ = 0 := by
  apply le_antisymm _ (wasserstein1_nonneg μ μ hμ hμ)
  exact wasserstein1_le μ μ hμ hμ (fun _ _ ↦ by simp)

lemma wasserstein1_comm (μ ν : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    (hν : Integrable (fun x : ℝ ↦ x) (ν : Measure ℝ)) :
    wasserstein1 μ ν hμ hν = wasserstein1 ν μ hν hμ := by
  simp only [wasserstein1, abs_sub_comm]

lemma wasserstein1_triangle (μ ν ρ : ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ))
    (hν : Integrable (fun x : ℝ ↦ x) (ν : Measure ℝ))
    (hρ : Integrable (fun x : ℝ ↦ x) (ρ : Measure ℝ)) :
    wasserstein1 μ ρ hμ hρ ≤ wasserstein1 μ ν hμ hν + wasserstein1 ν ρ hν hρ := by
  apply wasserstein1_le
  intro f hf
  exact (abs_sub_le _ _ _).trans (add_le_add
    (abs_integral_sub_le_wasserstein1 μ ν hμ hν hf)
    (abs_integral_sub_le_wasserstein1 ν ρ hν hρ hf))

end ExactOverlaps.GaussianApproximation
