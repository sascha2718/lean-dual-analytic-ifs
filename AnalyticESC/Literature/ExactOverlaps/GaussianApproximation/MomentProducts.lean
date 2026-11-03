module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.GaussianApproximation.Moments

set_option maxSynthPendingDepth 3

/-!
# The first-times-second moment bound

Integrating an elementary cubic inequality twice proves the moment product
estimate needed in the independent-summand Stein argument. Every moment is
finite by the explicit third-moment hypothesis.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.GaussianApproximation.MomentProducts`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory

namespace ExactOverlaps.GaussianApproximation

lemma three_mul_abs_mul_sq_le (x y : ℝ) :
    3 * |x| * y ^ 2 ≤ |x| ^ 3 + 2 * |y| ^ 3 := by
  have h := mul_nonneg (sq_nonneg (|x| - |y|))
    (add_nonneg (abs_nonneg x) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg y)))
  rw [← sq_abs y]
  nlinarith

lemma firstMoment_mul_secondMoment_le_thirdMoment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 3 μ) :
    (∫ ω, |X ω| ∂μ) * (∫ ω, (X ω) ^ 2 ∂μ) ≤ ∫ ω, |X ω| ^ 3 ∂μ := by
  have h1 := (integrable_of_memLp_three hX).abs
  have h2 := integrable_sq_of_memLp_three hX
  have h3 := integrable_abs_cube_of_memLp_three hX
  have hi (ω : Ω) : 3 * |X ω| * (∫ η, (X η) ^ 2 ∂μ) ≤
      |X ω| ^ 3 + 2 * ∫ η, |X η| ^ 3 ∂μ := by
    have h := integral_mono (h2.const_mul (3 * |X ω|))
      ((integrable_const (|X ω| ^ 3)).add (h3.const_mul 2))
      (fun η ↦ three_mul_abs_mul_sq_le (X ω) (X η))
    change (∫ η, 3 * |X ω| * (X η) ^ 2 ∂μ) ≤ ∫ η, |X ω| ^ 3 + 2 * |X η| ^ 3 ∂μ at h
    rw [integral_add (integrable_const _) (h3.const_mul 2)] at h
    simpa only [integral_const_mul, integral_const, probReal_univ, one_smul] using h
  have h := integral_mono ((h1.const_mul 3).mul_const (∫ η, (X η) ^ 2 ∂μ))
    (h3.add (integrable_const (2 * ∫ η, |X η| ^ 3 ∂μ))) hi
  change (∫ ω, 3 * |X ω| * (∫ η, (X η) ^ 2 ∂μ) ∂μ) ≤
    ∫ ω, |X ω| ^ 3 + 2 * (∫ η, |X η| ^ 3 ∂μ) ∂μ at h
  rw [integral_mul_const, integral_const_mul,
    integral_add h3 (integrable_const _), integral_const, probReal_univ, one_smul] at h
  linarith

end ExactOverlaps.GaussianApproximation
