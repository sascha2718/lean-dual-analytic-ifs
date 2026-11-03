module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.ChainRule
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Data.Int.Interval

set_option maxSynthPendingDepth 3

/-!
# Dyadic quantization of bounded probability laws

The entropy is the finite Shannon entropy of the actual push-forward law.
Bounded support supplies a finite-support proof at every integer level,
including the negative levels used for sums at their square-root scale.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.Dyadic`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ExactOverlaps.Entropy

/-- The integer label of the half-open dyadic cell at level `i`. -/
noncomputable def dyadicQuantize (i : ℤ) (x : ℝ) : ℤ := ⌊(2 : ℝ) ^ i * x⌋

/-- The half-open dyadic cell labelled `k` at the integer level `i`. -/
def dyadicCell (i k : ℤ) : Set ℝ := {x | dyadicQuantize i x = k}

lemma dyadic_scale_pos (i : ℤ) : 0 < (2 : ℝ) ^ i := zpow_pos (by norm_num) _

@[fun_prop] lemma measurable_dyadicQuantize (i : ℤ) : Measurable (dyadicQuantize i) := by
  unfold dyadicQuantize
  fun_prop

lemma measurableSet_dyadicCell (i k : ℤ) : MeasurableSet (dyadicCell i k) :=
  (measurable_dyadicQuantize i) (measurableSet_singleton k)

lemma mem_dyadicCell_iff (i k : ℤ) (x : ℝ) :
    x ∈ dyadicCell i k ↔ (k : ℝ) ≤ (2 : ℝ) ^ i * x ∧
      (2 : ℝ) ^ i * x < (k : ℝ) + 1 := by
  exact Int.floor_eq_iff

lemma dyadicCell_eq_Ico (i k : ℤ) :
    dyadicCell i k = Ico ((k : ℝ) / (2 : ℝ) ^ i) (((k : ℝ) + 1) / (2 : ℝ) ^ i) := by
  ext x
  rw [mem_dyadicCell_iff, mem_Ico, div_le_iff₀ (dyadic_scale_pos i),
    lt_div_iff₀ (dyadic_scale_pos i)]
  simp only [mul_comm]

/-- A coarser cell label is obtained by integer division of a finer cell label. -/
lemma dyadicQuantize_add_nat (i : ℤ) (m : ℕ) (x : ℝ) :
    dyadicQuantize i x = dyadicQuantize (i + m) x / (2 ^ m : ℕ) := by
  unfold dyadicQuantize
  rw [← Int.floor_div_natCast]
  congr 1
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
  push_cast
  field_simp

/-- The probability mass function of the dyadic cell label. -/
noncomputable def dyadicLaw (μ : ProbabilityMeasure ℝ) (i : ℤ) : PMF ℤ :=
  (μ.map (dyadicQuantize i)).toMeasure.toPMF

lemma dyadicLaw_apply (μ : ProbabilityMeasure ℝ) (i k : ℤ) :
    dyadicLaw μ i k = (μ : Measure ℝ) (dyadicCell i k) := by
  rw [dyadicLaw, Measure.toPMF_apply,
    ProbabilityMeasure.map_apply' μ (measurable_dyadicQuantize i).aemeasurable
      (measurableSet_singleton k)]
  rfl

lemma dyadicLaw_eq_map_of_toMeasure_eq (μ : ProbabilityMeasure ℝ) (p : PMF ℝ)
    (hμ : (μ : Measure ℝ) = p.toMeasure) (i : ℤ) :
    dyadicLaw μ i = p.map (dyadicQuantize i) := by
  unfold dyadicLaw
  rw [PMF.toPMF_eq_iff_toMeasure_eq, ProbabilityMeasure.toMeasure_map,
    hμ, PMF.toMeasure_map (dyadicQuantize i) p (measurable_dyadicQuantize i)]

lemma dyadicLaw_toMeasure (μ : ProbabilityMeasure ℝ) (i : ℤ) :
    (dyadicLaw μ i).toMeasure = (μ : Measure ℝ).map (dyadicQuantize i) := by
  simp [dyadicLaw]

/-- The probability law at a coarser scale is a deterministic statistic of the finer law. -/
lemma dyadicLaw_map_div (μ : ProbabilityMeasure ℝ) (i : ℤ) (m : ℕ) :
    (dyadicLaw μ (i + m)).map (fun k : ℤ ↦ k / (2 ^ m : ℕ)) = dyadicLaw μ i := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _), dyadicLaw_toMeasure,
    dyadicLaw_toMeasure, Measure.map_map (measurable_of_countable _)
      (measurable_dyadicQuantize _)]
  congr 1
  funext x
  exact (dyadicQuantize_add_nat i m x).symm

/-- Bounded support up to a null set; suitable for arbitrary compact real laws. -/
def HasBoundedSupport (μ : ProbabilityMeasure ℝ) : Prop :=
  ∃ a b : ℝ, ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a b

lemma dyadicLaw_support_subset (μ : ProbabilityMeasure ℝ) (i : ℤ)
    {a b : ℝ} (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a b) :
    (dyadicLaw μ i).support ⊆
      Icc (dyadicQuantize i a) (dyadicQuantize i b) := by
  intro k hk
  by_contra hnot
  have hzero : (μ : Measure ℝ) (dyadicCell i k) = 0 := by
    apply measure_mono_null (t := {x | x ∉ Icc a b})
    · intro x hx hxab
      apply hnot
      have hkx : dyadicQuantize i x = k := hx
      rw [← hkx]
      exact ⟨Int.floor_mono (mul_le_mul_of_nonneg_left hxab.1 (dyadic_scale_pos i).le),
        Int.floor_mono (mul_le_mul_of_nonneg_left hxab.2 (dyadic_scale_pos i).le)⟩
    · exact ae_iff.mp hμ
  exact hk (by rw [dyadicLaw_apply, hzero])

lemma dyadicLaw_support_finite (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (i : ℤ) : (dyadicLaw μ i).support.Finite := by
  obtain ⟨a, b, hab⟩ := hμ
  exact (Set.finite_Icc (dyadicQuantize i a) (dyadicQuantize i b)).subset
    (dyadicLaw_support_subset μ i hab)

/-- Dyadic entropy with natural logarithms, with finiteness justified by bounded support. -/
noncomputable def dyadicEntropy (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (i : ℤ) : ℝ :=
  finiteEntropy (dyadicLaw μ i) (dyadicLaw_support_finite μ hμ i)

/-- Hochman's normalized base-two entropy at a natural-number level. -/
noncomputable def normalizedDyadicEntropy (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n : ℕ) : ℝ :=
  dyadicEntropy μ hμ n / ((n : ℝ) * Real.log 2)

lemma dyadicEntropy_nonneg (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (i : ℤ) :
    0 ≤ dyadicEntropy μ hμ i := finiteEntropy_nonneg _ _

/-- Refining a dyadic partition cannot decrease its entropy. -/
lemma dyadicEntropy_le_add_nat (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ)
    (i : ℤ) (m : ℕ) : dyadicEntropy μ hμ i ≤ dyadicEntropy μ hμ (i + m) := by
  have h := finiteEntropy_map_le (dyadicLaw μ (i + m))
    (dyadicLaw_support_finite μ hμ (i + m)) (fun k : ℤ ↦ k / (2 ^ m : ℕ))
  simpa only [dyadicLaw_map_div, dyadicEntropy] using h

lemma dyadicEntropy_mono (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) :
    Monotone (dyadicEntropy μ hμ) := by
  intro i j hij
  obtain ⟨m, hm⟩ := Int.le.dest hij
  simpa only [hm] using dyadicEntropy_le_add_nat μ hμ i m

lemma normalizedDyadicEntropy_nonneg (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n : ℕ) :
    0 ≤ normalizedDyadicEntropy μ hμ n := by
  exact div_nonneg (dyadicEntropy_nonneg μ hμ n)
    (mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg (by norm_num)))

end ExactOverlaps.Entropy
