module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Order.Filter.AtTopBot.Basic

set_option maxSynthPendingDepth 3

/-!
Selection of adjacent scales in a decreasing positive radius sequence.
The selected index tends to infinity as the radius tends to zero from
above, enabling transfer of sampled local-dimension limits.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.RadiusIndex`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open Filter
open scoped Topology

namespace ExactOverlaps

theorem exists_radius_index {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hanti : Antitone r)
    (hzero : Tendsto r atTop (𝓝 0)) :
    ∃ k : ℝ → ℕ, Tendsto k (𝓝[>] (0 : ℝ)) atTop ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ), r (k t + 1) < t ∧ t ≤ r (k t) := by
  classical
  have hex : ∀ t : ℝ, 0 < t → ∃ n : ℕ, r (n + 1) < t := by
    intro t ht
    exact ((hzero.comp (tendsto_add_atTop_nat 1)).eventually (gt_mem_nhds ht)).exists
  let k : ℝ → ℕ := fun t ↦ if ht : 0 < t then Nat.find (hex t ht) else 0
  have hlow : ∀ t : ℝ, 0 < t → r (k t + 1) < t := by
    intro t ht
    simp only [k, dite_eq_left ht]
    exact Nat.find_spec (hex t ht)
  have hupp : ∀ t : ℝ, 0 < t → t ≤ r 0 → t ≤ r (k t) := by
    intro t ht ht0
    by_cases hk : k t = 0
    · simpa only [hk] using ht0
    have hkpos : 0 < k t := Nat.pos_of_ne_zero hk
    by_contra h
    have hh : r ((k t - 1) + 1) < t := by
      rw [Nat.sub_add_cancel hkpos]
      exact lt_of_not_ge h
    have hmin : Nat.find (hex t ht) ≤ k t - 1 := Nat.find_min' (hex t ht) hh
    have heq : Nat.find (hex t ht) = k t := by simp only [k, dite_eq_left ht]
    rw [heq] at hmin
    omega
  refine ⟨k, ?_, ?_⟩
  · apply tendsto_atTop.mpr
    intro M
    have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < r (M + 1) :=
      (gt_mem_nhds (hr (M + 1))).filter_mono nhdsWithin_le_nhds
    filter_upwards [he, self_mem_nhdsWithin] with t ht htp
    have hpos : 0 < t := htp
    by_contra h
    have hkM : k t + 1 ≤ M + 1 := by omega
    have hh := hanti hkM
    linarith [hlow t hpos]
  · have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < r 0 :=
      (gt_mem_nhds (hr 0)).filter_mono nhdsWithin_le_nhds
    filter_upwards [he, self_mem_nhdsWithin] with t ht htp
    exact ⟨hlow t htp, hupp t htp ht.le⟩

end ExactOverlaps
