module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.TailOscillation
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.BernoulliPointwise
public import Mathlib.Algebra.BigOperators.Field

set_option maxSynthPendingDepth 3

/-!
Deterministic error estimates for triangular orbit averages. A fixed
tail oscillation controls the bulk; only a fixed terminal block of the
integrable dominating observable remains.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.TriangularAverages`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps.Ergodic

noncomputable def triangularAverage {Ω : Type*} (T : Ω → Ω) (F : ℕ → Ω → ℝ)
    (n : ℕ) (x : Ω) : ℝ := (∑ j ∈ Finset.range n, F (n - j) (T^[j] x)) / n

theorem triangularAverage_error_le {Ω : Type*} (T : Ω → Ω)
    {F : ℕ → Ω → ℝ} {f G : Ω → ℝ} {x : Ω}
    (hF : ∀ j n, |F n (T^[j] x)| ≤ G (T^[j] x))
    (hf : ∀ j, |f (T^[j] x)| ≤ G (T^[j] x))
    {m n : ℕ} (hmn : m ≤ n) :
    |triangularAverage T F n x - birkhoffAverage ℝ T f n x| ≤
      birkhoffAverage ℝ T (tailOscillation F f m) n x +
        2 * ((birkhoffSum T G n x - birkhoffSum T G (n - m) x) / n) := by
  let d : ℕ → ℝ := fun j ↦ |F (n - j) (T^[j] x) - f (T^[j] x)|
  have hsplit : (∑ j ∈ Finset.range n, d j) =
      (∑ j ∈ Finset.range (n - m), d j) +
        ∑ k ∈ Finset.range m, d (n - m + k) := by
    simpa only [Nat.sub_add_cancel hmn] using Finset.sum_range_add d (n - m) m
  have hbulk : (∑ j ∈ Finset.range (n - m), d j) ≤
      ∑ j ∈ Finset.range n, tailOscillation F f m (T^[j] x) := by
    apply le_trans (Finset.sum_le_sum (fun j hj ↦
      le_tailOscillation (hF j) (hf j) (m := m) (n := n - j)
        (by have := Finset.mem_range.mp hj; omega)))
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le _ _))
      (fun j _ _ ↦ (tailOscillation_bounds (hF j) (hf j) m).1)
  have htail : (∑ k ∈ Finset.range m, d (n - m + k)) ≤
      2 * ∑ k ∈ Finset.range m, G (T^[n - m + k] x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    dsimp [d]
    have hh := abs_sub_le (F (n - (n - m + k)) (T^[n - m + k] x)) 0
      (f (T^[n - m + k] x))
    simp only [sub_zero, zero_sub, abs_neg] at hh
    exact hh.trans (by linarith [hF (n - m + k) (n - (n - m + k)), hf (n - m + k)])
  have hGsplit : birkhoffSum T G n x - birkhoffSum T G (n - m) x =
      ∑ k ∈ Finset.range m, G (T^[n - m + k] x) := by
    have hh := Finset.sum_range_add (fun j ↦ G (T^[j] x)) (n - m) m
    rw [Nat.sub_add_cancel hmn] at hh
    change (∑ j ∈ Finset.range n, G (T^[j] x)) -
      (∑ j ∈ Finset.range (n - m), G (T^[j] x)) = _
    linarith only [hh]
  have hsum : (∑ j ∈ Finset.range n, d j) ≤
      (∑ j ∈ Finset.range n, tailOscillation F f m (T^[j] x)) +
        2 * (birkhoffSum T G n x - birkhoffSum T G (n - m) x) := by
    rw [hsplit, hGsplit]
    exact add_le_add hbulk htail
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  calc
    |triangularAverage T F n x - birkhoffAverage ℝ T f n x| =
        |∑ j ∈ Finset.range n, (F (n - j) (T^[j] x) - f (T^[j] x))| / n := by
      simp only [triangularAverage, birkhoffAverage, birkhoffSum, smul_eq_mul,
        ← div_eq_inv_mul, ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_nonneg hn]
    _ ≤ (∑ j ∈ Finset.range n, d j) / n :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hn
    _ ≤ _ := by
      have hh := div_le_div_of_nonneg_right hsum hn
      simpa only [add_div, mul_div_assoc, birkhoffAverage, birkhoffSum, smul_eq_mul,
        ← div_eq_inv_mul] using hh

end ExactOverlaps.Ergodic
