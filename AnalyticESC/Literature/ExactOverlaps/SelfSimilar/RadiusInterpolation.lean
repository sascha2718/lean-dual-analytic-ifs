module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.RadiusIndex
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

set_option maxSynthPendingDepth 3

/-!
Interpolation from contraction scales to all positive radii. A monotone
nonnegative information function is squeezed between adjacent sampled
values, using their genuine linear asymptotic logarithmic radius rate.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.RadiusInterpolation`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open Filter
open scoped Topology

namespace ExactOverlaps

theorem tendsto_succ_div_of_div {a : ℕ → ℝ} {L : ℝ}
    (ha : Tendsto (fun n : ℕ ↦ a n / n) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ ↦ a (n + 1) / n) atTop (𝓝 L) := by
  have hf : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_natCast_atTop_atTop)
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  have h := (ha.comp (tendsto_add_atTop_nat 1)).mul hf
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs0 : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [Function.comp_def, Nat.cast_add, Nat.cast_one]
  field_simp

theorem information_radius_limit_of_sampled_rates {r : ℕ → ℝ} {I : ℝ → ℝ}
    (hr : ∀ n, 0 < r n) (hanti : Antitone r) (hzero : Tendsto r atTop (𝓝 0))
    (hI0 : ∀ t : ℝ, 0 < t → 0 ≤ I t) (hI : AntitoneOn I (Set.Ioi 0))
    {h L : ℝ} (hL : 0 < L)
    (hinfo : Tendsto (fun n : ℕ ↦ I (r n) / n) atTop (𝓝 h))
    (hrate : Tendsto (fun n : ℕ ↦ -Real.log (r n) / n) atTop (𝓝 L)) :
    Tendsto (fun t : ℝ ↦ I t / -Real.log t) (𝓝[>] 0) (𝓝 (h / L)) := by
  have hlo : Tendsto (fun n : ℕ ↦ I (r n) / -Real.log (r (n + 1)))
      atTop (𝓝 (h / L)) := by
    apply (hinfo.div (tendsto_succ_div_of_div hrate) hL.ne').congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact div_div_div_cancel_right₀ (by exact_mod_cast hn.ne') _ _
  have hhi : Tendsto (fun n : ℕ ↦ I (r (n + 1)) / -Real.log (r n))
      atTop (𝓝 (h / L)) := by
    apply ((tendsto_succ_div_of_div hinfo).div hrate hL.ne').congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact div_div_div_cancel_right₀ (by exact_mod_cast hn.ne') _ _
  obtain ⟨k, hk, hbetween⟩ := exists_radius_index hr hanti hzero
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), r (k t) < 1 :=
    (hzero.comp hk).eventually (gt_mem_nhds zero_lt_one)
  apply (hlo.comp hk).squeeze' (hhi.comp hk)
  · filter_upwards [hbetween, hsmall, self_mem_nhdsWithin] with t ht hsmall htp
    have hpos : 0 < t := htp
    have hlog : 0 < -Real.log t := neg_pos.mpr (Real.log_neg hpos (ht.2.trans_lt hsmall))
    apply div_le_div₀ (hI0 t hpos) (hI htp (hr (k t)) ht.2) hlog
    exact neg_le_neg (Real.log_le_log (hr (k t + 1)) ht.1.le)
  · filter_upwards [hbetween, hsmall, self_mem_nhdsWithin] with t ht hsmall htp
    have hpos : 0 < t := htp
    have hlog : 0 < -Real.log (r (k t)) := neg_pos.mpr (Real.log_neg (hr (k t)) hsmall)
    apply div_le_div₀ (hI0 _ (hr (k t + 1))) (hI (hr (k t + 1)) htp ht.1.le) hlog
    exact neg_le_neg (Real.log_le_log hpos ht.2)

end ExactOverlaps
