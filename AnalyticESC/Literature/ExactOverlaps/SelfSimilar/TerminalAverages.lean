module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.BernoulliPointwise

set_option maxSynthPendingDepth 3

/-!
A fixed terminal block of an orbit sum is negligible after normalization
whenever the full orbit averages converge. This handles the boundary
terms in triangular averaging without any uniform boundedness assumption.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.TerminalAverages`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open Filter
open scoped Topology

namespace ExactOverlaps.Ergodic

theorem tendsto_nat_sub_fraction (m : ℕ) :
    Tendsto (fun n : ℕ ↦ ((n - m : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
    ((tendsto_const_nhds (x := (m : ℝ))).div_atTop tendsto_natCast_atTop_atTop)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop m, eventually_gt_atTop 0] with n hmn hn
  rw [Nat.cast_sub hmn]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

theorem terminal_orbit_sum_div_tendsto_zero {Ω : Type*} (T : Ω → Ω) (G : Ω → ℝ)
    (x : Ω) {L : ℝ}
    (hG : Tendsto (fun n ↦ birkhoffAverage ℝ T G n x) atTop (𝓝 L)) (m : ℕ) :
    Tendsto (fun n : ℕ ↦ (birkhoffSum T G n x - birkhoffSum T G (n - m) x) / n)
      atTop (𝓝 0) := by
  have h := hG.sub ((tendsto_nat_sub_fraction m).mul (hG.comp (tendsto_sub_atTop_nat m)))
  simp only [one_mul, sub_self] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop m] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le m) hn).ne'
  have hnm0 : ((n - m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt hn).ne'
  simp only [birkhoffAverage, smul_eq_mul, Function.comp_def]
  field_simp

end ExactOverlaps.Ergodic
