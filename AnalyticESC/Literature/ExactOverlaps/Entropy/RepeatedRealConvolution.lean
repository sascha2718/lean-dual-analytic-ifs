module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.CarryEntropy
public import AnalyticESC.Literature.ExactOverlaps.Entropy.RepeatedConvolution

set_option maxSynthPendingDepth 3

/-!
# Repeated real convolution and dyadic discretization

The real sum and the sum of the original dyadic labels are coupled at every
step. After k additional summands the carry has at most k+1 values, so its
entropy cost is at most log(k+1). The finite Kaimanovich–Vershik inequality
then bounds the real repeated-convolution entropy by its first increment.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.RepeatedRealConvolution`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory

namespace ExactOverlaps.Entropy

noncomputable def iteratedRealConvolution (μ ν : ProbabilityMeasure ℝ) : ℕ → ProbabilityMeasure ℝ
  | 0 => μ
  | k + 1 => realConvolution (iteratedRealConvolution μ ν k) ν

lemma iteratedRealConvolution_hasBoundedSupport (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν) (k : ℕ) :
    HasBoundedSupport (iteratedRealConvolution μ ν k) := by
  induction k with
  | zero => exact hμ
  | succ k ih => exact realConvolution_hasBoundedSupport _ _ ih hν

noncomputable def iteratedDyadicCoupling (μ ν : ProbabilityMeasure ℝ) (i : ℤ) :
    ℕ → ProbabilityMeasure (ℝ × ℤ)
  | 0 => dyadicLift μ i
  | k + 1 => mixedConvolution (iteratedDyadicCoupling μ ν i k) (dyadicLift ν i)

lemma iteratedDyadicCoupling_map_fst (μ ν : ProbabilityMeasure ℝ) (i : ℤ) (k : ℕ) :
    (iteratedDyadicCoupling μ ν i k).map Prod.fst = iteratedRealConvolution μ ν k := by
  induction k with
  | zero => exact dyadicLift_map_fst μ i
  | succ k ih =>
    simp only [iteratedDyadicCoupling, mixedConvolution_map_fst, ih,
      dyadicLift_map_fst, iteratedRealConvolution]

lemma iteratedDyadicCoupling_integerLaw (μ ν : ProbabilityMeasure ℝ) (i : ℤ) (k : ℕ) :
    ((iteratedDyadicCoupling μ ν i k).map Prod.snd).toMeasure.toPMF =
      iteratedConvolution (dyadicLaw μ i) (dyadicLaw ν i) k := by
  induction k with
  | zero => exact dyadicLift_integerLaw μ i
  | succ k ih =>
    simp only [iteratedDyadicCoupling, mixedConvolution_integerLaw, ih,
      dyadicLift_integerLaw, iteratedConvolution]

lemma iteratedDyadicCoupling_carryBound (μ ν : ProbabilityMeasure ℝ) (i : ℤ) (k : ℕ) :
    HasDyadicCarryBound (iteratedDyadicCoupling μ ν i k) i k := by
  induction k with
  | zero => exact dyadicLift_carryBound μ i
  | succ k ih =>
    simpa only [Nat.add_zero, iteratedDyadicCoupling] using
      mixedConvolution_carryBound _ _ i ih (dyadicLift_carryBound ν i)

/-- Many-factor discretization, with its explicit logarithmic carry error. -/
theorem abs_iteratedEntropy_sub_dyadicEntropy_le (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν) (i : ℤ) (k : ℕ) :
    |iteratedEntropy (dyadicLaw μ i) (dyadicLaw ν i)
        (dyadicLaw_support_finite μ hμ i) (dyadicLaw_support_finite ν hν i) k -
      dyadicEntropy (iteratedRealConvolution μ ν k)
        (iteratedRealConvolution_hasBoundedSupport μ ν hμ hν k) i| ≤
          Real.log ((k : ℝ) + 1) := by
  have hX : HasBoundedSupport ((iteratedDyadicCoupling μ ν i k).map Prod.fst) := by
    rw [iteratedDyadicCoupling_map_fst]
    exact iteratedRealConvolution_hasBoundedSupport μ ν hμ hν k
  have hY : ((iteratedDyadicCoupling μ ν i k).map Prod.snd).toMeasure.toPMF.support.Finite := by
    rw [iteratedDyadicCoupling_integerLaw]
    exact iteratedConvolution_support_finite _ _
      (dyadicLaw_support_finite μ hμ i) (dyadicLaw_support_finite ν hν i) k
  have h := abs_integerLaw_entropy_sub_dyadicEntropy_le (iteratedDyadicCoupling μ ν i k)
    hX hY i k (iteratedDyadicCoupling_carryBound μ ν i k)
  simpa only [iteratedDyadicCoupling_map_fst, iteratedDyadicCoupling_integerLaw,
    iteratedEntropy] using h

/-- A real repeated convolution is controlled by its first dyadic entropy increment. -/
theorem dyadicEntropy_iteratedRealConvolution_le (μ ν : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (hν : HasBoundedSupport ν) (i : ℤ) (k : ℕ) :
    dyadicEntropy (iteratedRealConvolution μ ν k)
      (iteratedRealConvolution_hasBoundedSupport μ ν hμ hν k) i ≤
    dyadicEntropy μ hμ i + (k : ℝ) *
      (dyadicEntropy (realConvolution μ ν) (realConvolution_hasBoundedSupport μ ν hμ hν) i -
        dyadicEntropy μ hμ i + Real.log 2) + Real.log ((k : ℝ) + 1) := by
  have hcarry := (abs_le.mp (abs_iteratedEntropy_sub_dyadicEntropy_le μ ν hμ hν i k)).1
  have hseq := iteratedEntropy_le_first_increment (dyadicLaw μ i) (dyadicLaw ν i)
    (dyadicLaw_support_finite μ hμ i) (dyadicLaw_support_finite ν hν i) k
  have hfirst := (abs_le.mp
    (abs_discreteConvolution_entropy_sub_dyadicEntropy_le_log_two μ ν hμ hν i)).2
  have hmul := mul_le_mul_of_nonneg_left hfirst (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  change _ ≤ dyadicEntropy μ hμ i + (k : ℝ) * (_ - dyadicEntropy μ hμ i) at hseq
  nlinarith

end ExactOverlaps.Entropy
