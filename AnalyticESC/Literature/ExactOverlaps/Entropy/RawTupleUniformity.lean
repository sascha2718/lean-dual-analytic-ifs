module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.ConvolutionUniformity
public import AnalyticESC.Literature.ExactOverlaps.Entropy.RawTupleConvolution

set_option maxSynthPendingDepth 3

/-!
# Uniform components of sufficiently variable raw component tuples

The coarse dilation puts each raw component into its own unit interval.
The genuine long-convolution uniformity theorem applies uniformly to those
interval locations, and exact entropy increments transfer it back to the
original signed dyadic scale.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.RawTupleUniformity`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace ExactOverlaps.Entropy

lemma ae_dilated_rawComponent_mem_Icc (μ : ProbabilityMeasure ℝ) (i : ℤ)
    (k : (dyadicLaw μ i).support) :
    ∀ᵐ x ∂((rawComponent μ i k).map (fun x ↦ (2 : ℝ) ^ i * x) : Measure ℝ),
      x ∈ Icc (k : ℝ) ((k : ℝ) + 1) := by
  have hc : (2 : ℝ) ^ i ≠ 0 := by positivity
  have hab : ∀ᵐ x ∂(rawComponent μ i k : Measure ℝ),
      x ∈ Icc ((k : ℝ) / (2 : ℝ) ^ i) (((k : ℝ) + 1) / (2 : ℝ) ^ i) := by
    filter_upwards [ae_rawComponent_mem μ i k] with x hx
    rw [dyadicCell_eq_Ico] at hx
    exact ⟨hx.1, hx.2.le⟩
  have h := ae_map_mul_mem_Icc (rawComponent μ i k) (show 0 ≤ (2 : ℝ) ^ i by positivity) hab
  have h₁ : (2 : ℝ) ^ i * ((k : ℝ) / (2 : ℝ) ^ i) = (k : ℝ) := by field_simp
  have h₂ : (2 : ℝ) ^ i * (((k : ℝ) + 1) / (2 : ℝ) ^ i) = (k : ℝ) + 1 := by field_simp
  rw [h₁, h₂] at h
  exact h

lemma dilated_rawTuple_eq_continuousSumLaw (μ : ProbabilityMeasure ℝ) (i : ℤ)
    (n : ℕ) (w : FiniteTuple (dyadicLaw μ i).support n) :
    (tupleConvolution (rawComponent μ i) n w).map (componentRescale i 0) =
      continuousSumLaw (fun j ↦ (rawComponent μ i (tupleCoordinate n w j)).map
        (fun x ↦ (2 : ℝ) ^ i * x)) := by
  rw [map_componentRescale_zero, tupleConvolution_eq_continuousSumLaw,
    continuousSumLaw_map_mul]

theorem exists_rawTuple_component_uniformity {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) {m : ℕ} (hm : 0 < m) :
    ∃ p K : ℕ, 0 < K ∧ ∀ n : ℕ, K ≤ n →
      ∀ (μ : ProbabilityMeasure ℝ) (i : ℤ) (w : FiniteTuple (dyadicLaw μ i).support n),
      σ * n ≤ variance (id : ℝ → ℝ)
        ((tupleConvolution (rawComponent μ i) n w).map (componentRescale i 0) : Measure ℝ) →
      componentEntropyLowerTailMass (tupleConvolution (rawComponent μ i) n w)
        (tupleConvolution_hasBoundedSupport _ (rawComponent_hasBoundedSupport μ i) n w)
        (i - dyadicSqrtScale n + p) m δ < δ := by
  have hd : 0 < δ ^ 2 / 4 := by positivity
  obtain ⟨p, K, hK, hp⟩ := exists_convolution_component_uniformity hσ hd hm
  refine ⟨p, K, hK, ?_⟩
  intro n hn μ i w hvar
  let ν : Fin n → ProbabilityMeasure ℝ := fun j ↦
    (rawComponent μ i (tupleCoordinate n w j)).map (fun x ↦ (2 : ℝ) ^ i * x)
  let a : Fin n → ℝ := fun j ↦ ((tupleCoordinate n w j).val : ℝ)
  have hab (j : Fin n) : ∀ᵐ x ∂(ν j : Measure ℝ), x ∈ Icc (a j) (a j + 1) :=
    ae_dilated_rawComponent_mem_Icc μ i (tupleCoordinate n w j)
  have he : (tupleConvolution (rawComponent μ i) n w).map (componentRescale i 0) =
      continuousSumLaw ν := dilated_rawTuple_eq_continuousSumLaw μ i n w
  rw [he] at hvar
  have hu := hp n hn ν a hab hvar
  have hdilate := component_lowerTail_dilation_le (tupleConvolution (rawComponent μ i) n w)
    (tupleConvolution_hasBoundedSupport _ (rawComponent_hasBoundedSupport μ i) n w)
    i ((p : ℤ) - dyadicSqrtScale n) hm hd.le δ
  simp only [he] at hdilate
  have hprod : δ * componentEntropyLowerTailMass (tupleConvolution (rawComponent μ i) n w)
      (tupleConvolution_hasBoundedSupport _ (rawComponent_hasBoundedSupport μ i) n w)
      (i + ((p : ℤ) - dyadicSqrtScale n)) m δ < δ * δ := by
    nlinarith [sq_pos_of_pos hδ]
  have h := (mul_lt_mul_iff_right₀ hδ).1 hprod
  convert h using 1
  congr 1
  omega

end ExactOverlaps.Entropy
