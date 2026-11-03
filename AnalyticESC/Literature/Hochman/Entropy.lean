module

public import AnalyticESC.Literature.Hochman.Bridge

@[expose] public section

/-!
# Dyadic entropy on the line: the toolbox

Properties of the dyadic entropy `H(θ, 𝒟_n)` (bits) of the shared vocabulary
`FractalGeometry.SelfConformal`, for the proof of Hochman's entropy growth theorem (Hochman,
*On self-similar sets with overlaps and inverse theorems for entropy*, Ann. of Math. 180 (2014),
Section 3.1, Lemma 3.1, and the identity `𝔼_{i=n}(H(θ_{x,i}, 𝒟_{n+m})) = H(θ, 𝒟_{n+m} | 𝒟_n)` of
Section 3.2). The finite-entropy statements are transferred from the Kittle–Kogler library
`ExactOverlaps` through `FractalGeometry/Hochman/Bridge.lean`.

## Main declarations

* `dyadicEntropy_nonneg`, `dyadicEntropy_zero`: nonnegativity, the zero measure.
* `dyadicEntropy_le_add`, `dyadicEntropy_add_sub_le`: monotonicity in the level and the bound
  `H(θ, 𝒟_{n+p}) - H(θ, 𝒟_n) ≤ p`, for probability measures of bounded support.
* `dyadicEntropy_eq_zero_of_cell`: a probability measure carried by a level-`n` cell has zero
  entropy at level `n`.
* `dyadicEntropy_componentAt_le`, `dyadicEntropy_componentAt_nonneg`: `0 ≤ H(θ_D, 𝒟_{n+p}) ≤ p`
  for a level-`n` component.
* `dyadicEntropy_add_sub_eq_integral`: the chain rule
  `H(θ, 𝒟_{n+p}) - H(θ, 𝒟_n) = ∫ H(θ_{y,n}, 𝒟_{n+p}) dθ(y)`.
* `normalizedDyadicEntropy_rescaledComponent`, `componentEntropyLowerTailMass_eq`: the
  Kittle–Kogler mass of components of low entropy, in our vocabulary.

Copied from the library `FractalGeometry` (module `FractalGeometry.Hochman.Entropy`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Hochman

open MeasureTheory Set FractalGeometry.SelfConformal
open ExactOverlaps.Entropy (dyadicLaw HasBoundedSupport rawComponent rescaledComponent
  dyadicLaw_support_finite)
open scoped ENNReal

/-- `log 2 > 0`. -/
theorem log_two_pos' : 0 < Real.log 2 := Real.log_pos one_lt_two

/-! ### Elementary bounds -/

/-- The dyadic entropy of a measure of total mass at most one is nonnegative. -/
theorem dyadicEntropy_nonneg (θ : Measure ℝ) [IsFiniteMeasure θ] (hθ : θ univ ≤ 1) (n : ℕ) :
    0 ≤ dyadicEntropy θ n := by
  refine div_nonneg (tsum_nonneg fun k => Real.negMulLog_nonneg measureReal_nonneg ?_)
    log_two_pos'.le
  rw [Measure.real, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top ((measure_mono (subset_univ _)).trans hθ)

/-- The zero measure has zero entropy. -/
theorem dyadicEntropy_zero (n : ℕ) : dyadicEntropy (0 : Measure ℝ) n = 0 := by
  simp [dyadicEntropy]

/-- Refining the partition does not decrease entropy: `H(θ, 𝒟_n) ≤ H(θ, 𝒟_{n+p})`. -/
theorem dyadicEntropy_le_add (θ : Measure ℝ) [IsProbabilityMeasure θ] {a b : ℝ}
    (hab : θ (Icc a b)ᶜ = 0) (n p : ℕ) : dyadicEntropy θ n ≤ dyadicEntropy θ (n + p) := by
  have h := ExactOverlaps.Entropy.dyadicEntropy_le_add_nat (toPM θ) (hasBoundedSupport_toPM θ hab)
    n p
  rw [show ((n : ℤ) + (p : ℤ)) = ((n + p : ℕ) : ℤ) by push_cast; rfl, kDyadicEntropy_eq,
    kDyadicEntropy_eq] at h
  exact le_of_mul_le_mul_right h log_two_pos'

/-- Refining `p` times adds at most `p` bits: `H(θ, 𝒟_{n+p}) - H(θ, 𝒟_n) ≤ p`. -/
theorem dyadicEntropy_add_sub_le (θ : Measure ℝ) [IsProbabilityMeasure θ] {a b : ℝ}
    (hab : θ (Icc a b)ᶜ = 0) (n p : ℕ) : dyadicEntropy θ (n + p) - dyadicEntropy θ n ≤ p := by
  have h := ExactOverlaps.Entropy.dyadicEntropy_increment_le (toPM θ)
    (hasBoundedSupport_toPM θ hab) n p
  rw [show ((n : ℤ) + (p : ℤ)) = ((n + p : ℕ) : ℤ) by push_cast; rfl, kDyadicEntropy_eq,
    kDyadicEntropy_eq, ← sub_mul] at h
  exact le_of_mul_le_mul_right h log_two_pos'

/-- A probability measure carried by a level-`n` cell has zero entropy at level `n`. -/
theorem dyadicEntropy_eq_zero_of_cell (θ : Measure ℝ) [IsProbabilityMeasure θ] {n : ℕ} {k : ℤ}
    (h : θ (cell n k)ᶜ = 0) : dyadicEntropy θ n = 0 := by
  have hk : θ (cell n k) = 1 := (prob_compl_eq_zero_iff (measurableSet_cell n k)).1 h
  have hterm : ∀ l : ℤ, Real.negMulLog (θ.real (cell n l)) = 0 := by
    intro l
    by_cases hl : l = k
    · rw [hl, Measure.real, hk, ENNReal.toReal_one, Real.negMulLog_one]
    · have h0 : θ (cell n l) = 0 :=
        measure_mono_null (Disjoint.subset_compl_right
          (pairwise_disjoint_cell n hl)) h
      rw [Measure.real, h0, ENNReal.toReal_zero, Real.negMulLog_zero]
  simp [dyadicEntropy, hterm]

/-- The level-`n` component on a cell, viewed through a bounding interval. -/
theorem componentAt_compl_Icc (θ : Measure ℝ) (n : ℕ) (k : ℤ) :
    componentAt θ n k (Icc ((k : ℝ) / 2 ^ n) (((k : ℝ) + 1) / 2 ^ n))ᶜ = 0 :=
  measure_mono_null (compl_subset_compl.2 Ico_subset_Icc_self) (componentAt_compl θ n k)

/-- A level-`n` component has nonnegative entropy. -/
theorem dyadicEntropy_componentAt_nonneg (θ : Measure ℝ) [IsFiniteMeasure θ] (n : ℕ) (k : ℤ)
    (N : ℕ) : 0 ≤ dyadicEntropy (componentAt θ n k) N :=
  dyadicEntropy_nonneg _ (componentAt_univ_le θ n k) N

/-- A level-`n` component has entropy at most `p` at level `n + p`. -/
theorem dyadicEntropy_componentAt_le (θ : Measure ℝ) [IsFiniteMeasure θ] (n : ℕ) (k : ℤ)
    (p : ℕ) : dyadicEntropy (componentAt θ n k) (n + p) ≤ p := by
  by_cases h0 : θ (cell n k) = 0
  · rw [componentAt_eq_zero θ h0, dyadicEntropy_zero]
    exact Nat.cast_nonneg p
  · have := isProbabilityMeasure_componentAt θ h0
    have h := dyadicEntropy_add_sub_le (componentAt θ n k) (componentAt_compl_Icc θ n k) n p
    rwa [dyadicEntropy_eq_zero_of_cell (componentAt θ n k) (componentAt_compl θ n k),
      sub_zero] at h

/-! ### The chain rule -/

/-- The chain rule `H(θ, 𝒟_{n+p}) - H(θ, 𝒟_n) = ∫ H(θ_{y,n}, 𝒟_{n+p}) dθ(y)` for a probability
measure of bounded support: the conditional entropy given `𝒟_n` is the average entropy of the
level-`n` components (Hochman 2014, Section 3.2). -/
theorem dyadicEntropy_add_sub_eq_integral (θ : Measure ℝ) [IsProbabilityMeasure θ] {a b : ℝ}
    (hab : θ (Icc a b)ᶜ = 0) (n p : ℕ) :
    dyadicEntropy θ (n + p) - dyadicEntropy θ n =
      ∫ y, dyadicEntropy (component θ n y) (n + p) ∂θ := by
  have hμ := hasBoundedSupport_toPM θ hab
  have hK := ExactOverlaps.Entropy.averageRawComponentEntropy_eq_sub (toPM θ) hμ n p
  let _ : Fintype (dyadicLaw (toPM θ) n).support := (dyadicLaw_support_finite _ hμ n).fintype
  unfold ExactOverlaps.Entropy.averageRawComponentEntropy at hK
  have hlev : ((n : ℤ) + (p : ℤ)) = ((n + p : ℕ) : ℤ) := by push_cast; rfl
  simp only [hlev, kDyadicEntropy_eq, rawComponent_eq_componentAt, toPM_coe] at hK
  have hsum := sum_support_eq_sum_Icc (toPM θ) hab n
    (fun k => dyadicEntropy (componentAt θ n k) (n + p) * Real.log 2)
  simp only [toPM_coe] at hsum
  rw [hsum] at hK
  have hint := integral_comp_cellIdx θ hab n (fun k => dyadicEntropy (componentAt θ n k) (n + p))
  rw [show ∫ y, dyadicEntropy (component θ n y) (n + p) ∂θ = _ from hint]
  simp_rw [← mul_assoc] at hK
  rw [← Finset.sum_mul, ← sub_mul] at hK
  exact (mul_right_cancel₀ log_two_pos'.ne' hK).symm

/-! ### Components of low entropy in the Kittle–Kogler library -/

/-- The normalised entropy of a rescaled Kittle–Kogler component at level `M` is
`H(θ_D, 𝒟_{q+M}) / M` for the corresponding raw component. -/
theorem normalizedDyadicEntropy_rescaledComponent (μ : ProbabilityMeasure ℝ) (q M : ℕ)
    (k : (dyadicLaw μ q).support) :
    ExactOverlaps.Entropy.normalizedDyadicEntropy (rescaledComponent μ q k)
        (ExactOverlaps.Entropy.rescaledComponent_hasBoundedSupport μ q k) M =
      dyadicEntropy (componentAt (μ : Measure ℝ) q k) (q + M) / M := by
  rw [ExactOverlaps.Entropy.normalizedDyadicEntropy,
    ExactOverlaps.Entropy.dyadicEntropy_rescaledComponent,
    show ((q : ℤ) + (M : ℤ)) = ((q + M : ℕ) : ℤ) by push_cast; rfl, kDyadicEntropy_eq,
    rawComponent_eq_componentAt, mul_div_mul_right _ _ log_two_pos'.ne']

/-- The Kittle–Kogler mass of level-`q` components with `H_M ≤ 1 - c` is
`θ({x : H(θ_{x,q}, 𝒟_{q+M}) / M ≤ 1 - c})`. -/
theorem componentEntropyLowerTailMass_eq (θ : Measure ℝ) [IsProbabilityMeasure θ] {a b : ℝ}
    (hab : θ (Icc a b)ᶜ = 0) (hμ : HasBoundedSupport (toPM θ)) (q M : ℕ) (c : ℝ) :
    ExactOverlaps.Entropy.componentEntropyLowerTailMass (toPM θ) hμ q M c =
      θ.real {x | dyadicEntropy (component θ q x) (q + M) / M ≤ 1 - c} := by
  classical
  set Q : ℤ → Prop := fun k => dyadicEntropy (componentAt θ q k) (q + M) / M ≤ 1 - c
  unfold ExactOverlaps.Entropy.componentEntropyLowerTailMass
  let _ : Fintype (dyadicLaw (toPM θ) q).support := (dyadicLaw_support_finite _ hμ q).fintype
  have hterm : ∀ k : (dyadicLaw (toPM θ) q).support,
      (if ExactOverlaps.Entropy.normalizedDyadicEntropy (rescaledComponent (toPM θ) q k)
          (ExactOverlaps.Entropy.rescaledComponent_hasBoundedSupport (toPM θ) q k) M ≤ 1 - c
        then (dyadicLaw (toPM θ) q k).toReal else 0) =
        (dyadicLaw (toPM θ) q k).toReal * (if Q k then 1 else 0) := by
    intro k
    rw [normalizedDyadicEntropy_rescaledComponent]
    split_ifs with h1 h2 h2
    · rw [mul_one]
    · exact absurd h1 h2
    · exact absurd h2 h1
    · rw [mul_zero]
  rw [Fintype.sum_congr _ _ hterm]
  have hsum := sum_support_eq_sum_Icc (toPM θ) hab q (fun k => if Q k then (1 : ℝ) else 0)
  simp only [toPM_coe] at hsum
  rw [hsum, ← integral_comp_cellIdx θ hab q (fun k => if Q k then (1 : ℝ) else 0)]
  have hset : {x | dyadicEntropy (component θ q x) (q + M) / M ≤ 1 - c} =
      cellIdx q ⁻¹' {k | Q k} := rfl
  rw [hset, ← integral_indicator_one ((measurable_cellIdx q) MeasurableSet.of_discrete)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
  rfl

end FractalGeometry.Hochman
