module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.FiniteProductLaw
public import AnalyticESC.Literature.ExactOverlaps.Entropy.RealConvolutionVariance
public import AnalyticESC.Literature.ExactOverlaps.Entropy.ConvolutionMixture
public import AnalyticESC.Literature.ExactOverlaps.Entropy.RepeatedRealConvolution

set_option maxSynthPendingDepth 3

/-!
# Actual convolutions of independently selected component laws

The convolution of a finite mixture is expanded over the genuine iid tuple
law. Variances add along each tuple, and the zero-fold convolution is the
point mass at zero.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.TupleConvolution`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace ExactOverlaps.Entropy

noncomputable def zeroRealLaw : ProbabilityMeasure ℝ := ⟨Measure.dirac 0, inferInstance⟩

lemma zeroRealLaw_hasBoundedSupport : HasBoundedSupport zeroRealLaw := by
  refine ⟨0, 0, ?_⟩
  change ∀ᵐ x ∂(Measure.dirac (0 : ℝ)), x ∈ Icc 0 0
  simp

lemma realConvolution_zero_right (μ : ProbabilityMeasure ℝ) :
    realConvolution μ zeroRealLaw = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [realConvolution_toMeasure]
  change (μ : Measure ℝ) ∗ Measure.dirac 0 = (μ : Measure ℝ)
  simp

noncomputable def tupleConvolution {α : Type*} (ν : α → ProbabilityMeasure ℝ) :
    (n : ℕ) → FiniteTuple α n → ProbabilityMeasure ℝ
  | 0, _ => zeroRealLaw
  | n + 1, w => realConvolution (ν w.1) (tupleConvolution ν n w.2)

lemma tupleConvolution_hasBoundedSupport {α : Type*} (ν : α → ProbabilityMeasure ℝ)
    (hν : ∀ a, HasBoundedSupport (ν a)) (n : ℕ) (w : FiniteTuple α n) :
    HasBoundedSupport (tupleConvolution ν n w) := by
  induction n with
  | zero => exact zeroRealLaw_hasBoundedSupport
  | succ n ih => exact realConvolution_hasBoundedSupport _ _ (hν w.1) (ih w.2)

lemma variance_tupleConvolution {α : Type*} (ν : α → ProbabilityMeasure ℝ)
    (hν : ∀ a, HasBoundedSupport (ν a)) (n : ℕ) (w : FiniteTuple α n) :
    variance (id : ℝ → ℝ) (tupleConvolution ν n w : Measure ℝ) =
      tupleSum (fun a ↦ variance (id : ℝ → ℝ) (ν a : Measure ℝ)) n w := by
  induction n with
  | zero => exact variance_dirac 0
  | succ n ih =>
    change variance (id : ℝ → ℝ)
      (realConvolution (ν w.1) (tupleConvolution ν n w.2) : Measure ℝ) = _
    rw [variance_realConvolution _ _ (hν w.1) (tupleConvolution_hasBoundedSupport ν hν n w.2),
      ih w.2]
    rfl

noncomputable def realConvolutionPower (μ : ProbabilityMeasure ℝ) : ℕ → ProbabilityMeasure ℝ
  | 0 => zeroRealLaw
  | n + 1 => realConvolution μ (realConvolutionPower μ n)

lemma realConvolutionPower_hasBoundedSupport (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n : ℕ) : HasBoundedSupport (realConvolutionPower μ n) := by
  induction n with
  | zero => exact zeroRealLaw_hasBoundedSupport
  | succ n ih => exact realConvolution_hasBoundedSupport _ _ hμ ih

lemma realConvolutionPower_succ_eq_iterated (μ : ProbabilityMeasure ℝ) (n : ℕ) :
    realConvolutionPower μ (n + 1) = iteratedRealConvolution μ μ n := by
  induction n with
  | zero => exact realConvolution_zero_right μ
  | succ n ih =>
    change realConvolution μ (realConvolutionPower μ (n + 1)) =
      realConvolution (iteratedRealConvolution μ μ n) μ
    rw [ih, realConvolution_comm]

theorem realConvolutionPower_eq_tuple_mixture {α : Type*} [Fintype α]
    (p : PMF α) (ν : α → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hmix : (μ : Measure ℝ) = ∑ a, p a • (ν a : Measure ℝ)) (n : ℕ) :
    (realConvolutionPower μ n : Measure ℝ) =
      ∑ w : FiniteTuple α n, (iidTupleLaw p n) w • (tupleConvolution ν n w : Measure ℝ) := by
  induction n with
  | zero =>
    change (zeroRealLaw : Measure ℝ) =
      ∑ w : PUnit, (PMF.pure PUnit.unit) w • (zeroRealLaw : Measure ℝ)
    simp
  | succ n ih =>
    exact realConvolution_eq_pair_mixture p (iidTupleLaw p n) ν (tupleConvolution ν n)
      μ (realConvolutionPower μ n) hmix ih

end ExactOverlaps.Entropy
