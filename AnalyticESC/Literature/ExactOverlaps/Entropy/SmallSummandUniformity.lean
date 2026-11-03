module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.DilatedSumGaussian
public import AnalyticESC.Literature.ExactOverlaps.Entropy.DilationUniformity

set_option maxSynthPendingDepth 3

/-!
# Component uniformity from small independent summands

A fixed positive variance range and sufficiently short summand intervals
after dilation force uniform components at one common shifted dyadic level.
The interval locations and the Gaussian comparison mean are unrestricted.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.SmallSummandUniformity`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace ExactOverlaps.Entropy

open GaussianApproximation

theorem exists_small_summand_component_uniformity {σ V δ : ℝ}
    (hσ : 0 < σ) (hV : 0 < V) (hδ : 0 < δ) {m : ℕ} (hm : 0 < m) :
    ∃ p : ℕ, ∃ ε > 0, ∀ {ι : Type} [Fintype ι]
      (ν : ι → ProbabilityMeasure ℝ) (a b : ι → ℝ)
      (hab : ∀ i, ∀ᵐ x ∂(ν i : Measure ℝ), x ∈ Icc (a i) (b i))
      (s : ℤ) (R : ℝ), (∀ i, b i - a i ≤ R) →
      (2 : ℝ) ^ s * R ≤ ε → ∀ (v : ℝ≥0), σ ≤ (v : ℝ) → (v : ℝ) ≤ V →
      ((2 : ℝ) ^ s) ^ 2 * variance (id : ℝ → ℝ) (continuousSumLaw ν : Measure ℝ) = (v : ℝ) →
      componentEntropyLowerTailMass (continuousSumLaw ν)
        (continuousSumLaw_hasBoundedSupport ν (fun i ↦ ⟨a i, b i, hab i⟩))
        (s + p) m δ < δ := by
  obtain ⟨p, η, hη, hp⟩ := exists_wasserstein_uniformity_after_dilation hσ hV hδ hm
  refine ⟨p, η / gaussianApproximationConstant, div_pos hη gaussianApproximationConstant_pos, ?_⟩
  intro ι _ ν a b hab s R hR hsize v hvσ hvV hvar
  obtain ⟨mean, hi, hW⟩ := wasserstein1_dilated_continuousSumLaw_le ν a b hab
    (show 0 ≤ (2 : ℝ) ^ s by positivity) hR v (hσ.trans_le hvσ) hvar
  have hsmall : gaussianApproximationConstant * ((2 : ℝ) ^ s * R) ≤ η := by
    have h := mul_le_mul_of_nonneg_left hsize gaussianApproximationConstant_pos.le
    calc
      _ ≤ gaussianApproximationConstant * (η / gaussianApproximationConstant) := h
      _ = η := by field_simp [gaussianApproximationConstant_pos.ne']
  apply hp (continuousSumLaw ν) (continuousSumLaw_hasBoundedSupport ν
    (fun i ↦ ⟨a i, b i, hab i⟩)) s mean v hvσ hvV
  simpa only [wasserstein1, map_componentRescale_zero] using hW.trans hsmall

end ExactOverlaps.Entropy
