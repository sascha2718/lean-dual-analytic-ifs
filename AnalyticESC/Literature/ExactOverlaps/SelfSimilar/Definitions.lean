module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.Similarity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Data.Fintype.Order

set_option maxSynthPendingDepth 3

/-!
Finite weighted systems of contracting real similarities. Stationarity is
the usual measure identity. Existence, uniqueness and dimension theorems are
not included as assumptions in these definitions.

The elementary stationarity and finite-bound arguments are adapted from
Constantin Kogler's 0BSD LpSelfSimilar formalization (2026), specialized to
signed affine similarities of the real line.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.Definitions`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ExactOverlaps.SelfSimilar

/-- Finite contracting similarities with nonnegative weights summing to one.
Zero weights are allowed; support restriction is a subsequent theorem. -/
structure System (ι : Type*) [Fintype ι] where
  map : ι → RealSimilarity
  contracting : ∀ i, |(map i).ratio| < 1
  weight : ι → ℝ≥0
  weight_sum : ∑ i, weight i = 1

namespace System

variable {ι : Type*} [Fintype ι]

/-- The fixed point identity for the finite weighted pushforward operator. -/
def IsStationary (S : System ι) (ν : Measure ℝ) : Prop :=
  ν = ∑ i, (S.weight i : ℝ≥0∞) • ν.map (S.map i)

theorem weight_sum_ennreal (S : System ι) :
    ∑ i, (S.weight i : ℝ≥0∞) = 1 := by
  exact_mod_cast S.weight_sum

theorem weight_sum_real (S : System ι) :
    ∑ i, (S.weight i : ℝ) = 1 := by
  exact_mod_cast S.weight_sum

theorem nonempty_index (S : System ι) : Nonempty ι := by
  by_contra h
  have : IsEmpty ι := not_nonempty_iff.mp h
  have := S.weight_sum
  simp at this

theorem stationary_apply (S : System ι) {ν : Measure ℝ}
    (hν : S.IsStationary ν) {E : Set ℝ} (hE : MeasurableSet E) :
    ν E = ∑ i, (S.weight i : ℝ≥0∞) * ν ((S.map i) ⁻¹' E) := by
  conv_lhs => rw [hν]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  congr 1
  ext i
  rw [Measure.map_apply (S.map i).measurable hE]

theorem measure_le_of_preimages_subset (S : System ι) {ν : Measure ℝ}
    (hν : S.IsStationary ν) {E F : Set ℝ} (hE : MeasurableSet E)
    (hsub : ∀ i, (S.map i) ⁻¹' E ⊆ F) : ν E ≤ ν F := by
  rw [S.stationary_apply hν hE]
  calc
    ∑ i, (S.weight i : ℝ≥0∞) * ν ((S.map i) ⁻¹' E) ≤
        ∑ i, (S.weight i : ℝ≥0∞) * ν F := by
      exact Finset.sum_le_sum fun i _ ↦ mul_le_mul' le_rfl (measure_mono (hsub i))
    _ = ν F := by rw [← Finset.sum_mul, S.weight_sum_ennreal, one_mul]

/-- Uniform contraction and displacement bounds follow from finiteness. -/
theorem exists_uniform_bounds (S : System ι) :
    ∃ c M : ℝ, 0 < c ∧ c < 1 ∧ 0 ≤ M ∧
      (∀ i, |(S.map i).ratio| ≤ c) ∧ (∀ i, |(S.map i).shift| ≤ M) := by
  classical
  have := S.nonempty_index
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i ↦ |(S.map i).ratio|) Finset.univ_nonempty
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ
    (fun j ↦ |(S.map j).shift|) Finset.univ_nonempty
  exact ⟨|(S.map i).ratio|, |(S.map j).shift|, (S.map i).abs_ratio_pos,
    S.contracting i, abs_nonneg _, fun k ↦ hi k (Finset.mem_univ k),
    fun k ↦ hj k (Finset.mem_univ k)⟩

theorem exists_min_ratio (S : System ι) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ ∀ i, a ≤ |(S.map i).ratio| := by
  classical
  have := S.nonempty_index
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
    (fun i ↦ |(S.map i).ratio|) Finset.univ_nonempty
  exact ⟨|(S.map i).ratio|, (S.map i).abs_ratio_pos, S.contracting i,
    fun k ↦ hi k (Finset.mem_univ k)⟩

/-- The paper's (negative) Lyapunov exponent, using natural logarithms. -/
noncomputable def lyapunov (S : System ι) : ℝ :=
  ∑ i, (S.weight i : ℝ) * Real.log |(S.map i).ratio|

theorem exists_weight_pos (S : System ι) : ∃ i, 0 < (S.weight i : ℝ) := by
  have hs : 0 < ∑ i, (S.weight i : ℝ) := by rw [S.weight_sum_real]; norm_num
  obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff_of_nonneg
    (fun i _ ↦ (S.weight i).coe_nonneg) |>.mp hs
  exact ⟨i, hi⟩

/-- Strict contraction and total probability one force a negative exponent,
even when some listed similarities have weight zero. -/
theorem lyapunov_neg (S : System ι) : S.lyapunov < 0 := by
  obtain ⟨i, hi⟩ := S.exists_weight_pos
  have hlog (j : ι) : Real.log |(S.map j).ratio| < 0 :=
    Real.log_neg (S.map j).abs_ratio_pos (S.contracting j)
  have hsum : (∑ j, (S.weight j : ℝ) * Real.log |(S.map j).ratio|) <
      ∑ _j : ι, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro j _
      exact mul_nonpos_of_nonneg_of_nonpos (S.weight j).coe_nonneg (hlog j).le
    · exact ⟨i, Finset.mem_univ i, mul_neg_of_pos_of_neg hi (hlog i)⟩
  simpa only [Finset.sum_const_zero, lyapunov] using hsum

theorem abs_lyapunov_pos (S : System ι) : 0 < |S.lyapunov| :=
  abs_pos.mpr S.lyapunov_neg.ne

theorem abs_lyapunov_eq_neg (S : System ι) : |S.lyapunov| = -S.lyapunov :=
  abs_of_neg S.lyapunov_neg

end System
end ExactOverlaps.SelfSimilar
