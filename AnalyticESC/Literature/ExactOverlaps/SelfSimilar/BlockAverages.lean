module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Algebra.BigOperators.Field

set_option maxSynthPendingDepth 3

/-!
Elementary passage from averages along arithmetic blocks to all partial
averages for a bounded real sequence. This is used after applying the
independent strong law separately to the residue classes of a block.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.BlockAverages`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open Filter Finset
open scoped Topology

namespace ExactOverlaps.Ergodic

theorem sum_range_mul_blocks (a : ℕ → ℝ) (q m : ℕ) :
    ∑ i ∈ range (q * m), a i = ∑ j ∈ range q, ∑ r ∈ range m, a (j * m + r) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

theorem abs_sum_range_le (a : ℕ → ℝ) {C : ℝ} (ha : ∀ i, |a i| ≤ C)
    (b r : ℕ) : |∑ i ∈ range r, a (b + i)| ≤ (r : ℝ) * C := by
  calc
    |∑ i ∈ range r, a (b + i)| ≤ ∑ i ∈ range r, |a (b + i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range r, C := sum_le_sum (fun i _ ↦ ha (b + i))
    _ = (r : ℝ) * C := by simp

theorem tendsto_nat_quotient {m : ℕ} (hm : 0 < m) :
    Tendsto (fun n : ℕ ↦ n / m) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b * m)] with n hn
  exact (Nat.le_div_iff_mul_le hm).2 hn

theorem tendsto_remainder_div {m : ℕ} (hm : 0 < m) :
    Tendsto (fun n : ℕ ↦ (n % m : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n ↦ by positivity)
    (fun n ↦ div_le_div_of_nonneg_right
      (show ((n % m : ℕ) : ℝ) ≤ m by exact_mod_cast (Nat.mod_lt n hm).le)
      (Nat.cast_nonneg n))
  exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

theorem tendsto_completed_block_fraction {m : ℕ} (hm : 0 < m) :
    Tendsto (fun n : ℕ ↦ ((n / m * m : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_remainder_div hm)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have he : ((n / m * m : ℕ) : ℝ) + ((n % m : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast (show n / m * m + n % m = n by
      simpa only [Nat.mul_comm] using Nat.div_add_mod n m)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  apply (eq_div_iff hn0).2
  field_simp
  linarith

theorem tendsto_cesaro_of_completed_blocks (a : ℕ → ℝ) {m : ℕ} (hm : 0 < m)
    {C L : ℝ} (ha : ∀ i, |a i| ≤ C)
    (hblocks : Tendsto (fun q : ℕ ↦ (∑ i ∈ range (q * m), a i) / ((q * m : ℕ) : ℝ))
      atTop (𝓝 L)) :
    Tendsto (fun n : ℕ ↦ (∑ i ∈ range n, a i) / (n : ℝ)) atTop (𝓝 L) := by
  have hC : 0 ≤ C := (abs_nonneg (a 0)).trans (ha 0)
  let R : ℕ → ℝ := fun n ↦ ∑ i ∈ range (n % m), a (n / m * m + i)
  have hR : ∀ n, |R n| ≤ (m : ℝ) * C := by
    intro n
    apply (abs_sum_range_le a ha _ _).trans
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.mod_lt n hm).le) hC
  have hr : Tendsto (fun n : ℕ ↦ R n / (n : ℝ)) atTop (𝓝 0) := by
    have hb : Tendsto (fun n : ℕ ↦ (m : ℝ) * C / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    apply squeeze_zero_norm (fun n ↦ ?_) hb
    have habs : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (by positivity)
    rw [Real.norm_eq_abs, abs_div, habs]
    exact div_le_div_of_nonneg_right (hR n) (Nat.cast_nonneg n)
  have hp := (hblocks.comp (tendsto_nat_quotient hm)).mul (tendsto_completed_block_fraction hm)
  have h := hp.add hr
  simp only [mul_one, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop m] with n hn
  have hq : 0 < n / m := Nat.div_pos hn hm
  have hb : ((n / m * m : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos hq hm).ne'
  have he : n = n / m * m + n % m := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod n m).symm
  have hsum : (∑ i ∈ range n, a i) = (∑ i ∈ range (n / m * m), a i) + R n := by
    conv_lhs => rw [he, sum_range_add]
  rw [hsum]
  change (∑ i ∈ range (n / m * m), a i) / ((n / m * m : ℕ) : ℝ) *
      (((n / m * m : ℕ) : ℝ) / (n : ℝ)) + R n / (n : ℝ) =
    ((∑ i ∈ range (n / m * m), a i) + R n) / (n : ℝ)
  rw [div_mul_div_cancel₀ hb, add_div]

/-- Residue-class strong laws imply the full Cesàro law for a bounded sequence. -/
theorem tendsto_cesaro_of_residue_classes (a : ℕ → ℝ) {m : ℕ} (hm : 0 < m)
    {C L : ℝ} (ha : ∀ i, |a i| ≤ C)
    (hres : ∀ r < m, Tendsto
      (fun q : ℕ ↦ (∑ j ∈ range q, a (j * m + r)) / (q : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ ↦ (∑ i ∈ range n, a i) / (n : ℝ)) atTop (𝓝 L) := by
  apply tendsto_cesaro_of_completed_blocks a hm ha
  have hs := tendsto_finsetSum (range m) (fun r hr ↦ hres r (mem_range.mp hr))
  have h := hs.div_const (m : ℝ)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [sum_const, card_range, nsmul_eq_mul, mul_div_cancel_left₀ L hm0] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with q hq
  rw [sum_range_mul_blocks, sum_comm, ← sum_div, Nat.cast_mul, div_div]

end ExactOverlaps.Ergodic
