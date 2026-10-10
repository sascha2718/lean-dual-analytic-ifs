module

public import AnalyticESC.Dimension.Rapaport
public import AnalyticESC.Generic.OpenDense

@[expose] public section

/-!
# Corollary 1.7

The systems of `𝔖_N` with equality in (1.6) contain a `d₂`-open and `d₂`-dense subset of `𝔖_N`, for
`N ≥ 2`. The open set is the open set of Theorem 1.4 intersected with the systems whose attractor
is not a singleton, which is open and dense for `N ≥ 2`; Theorem 1.6 applies to its systems.
-/

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory

namespace OpenDense

/-- The `𝒞²` distance on `I` from a map to itself vanishes. -/
theorem d2Map_self (f : ℂ → ℂ) : d2Map f f = 0 := by
  simp [d2Map]

/-- The `𝒞²` distance from a family of maps to itself vanishes. -/
theorem d2Sys_self {N : ℕ} (f : Fin N → ℂ → ℂ) : d2Sys f f = 0 := by
  simp [d2Sys, d2Map_self]

/-- The triangle inequality for `d₂` on `𝔖_N`. -/
theorem d2Sys_le_add {N : ℕ} {f g h : Fin N → ℂ → ℂ} (hf : InUnionClass f)
    (hg : InUnionClass g) (hh : InUnionClass h) : d2Sys f h ≤ d2Sys f g + d2Sys g h := by
  obtain ⟨ε, hε, hf⟩ := hf
  obtain ⟨ε', hε', hg⟩ := hg
  obtain ⟨ε'', hε'', hh⟩ := hh
  exact d2_le_add (⟨f, hε, hf⟩ : IFS N ε) (⟨g, hε', hg⟩ : IFS N ε') (⟨h, hε'', hh⟩ : IFS N ε'')

/-- A map of `S^ω_ε(I)` has at most one fixed point in `I`. -/
theorem eq_of_re_eq_self {ε : ℝ} (hε : 0 < ε) {h : ℂ → ℂ} (hh : InClass ε h) {x y : ℝ}
    (hx : x ∈ I) (hy : y ∈ I) (hhx : (h x).re = x) (hhy : (h y).re = y) : x = y := by
  -- `F(x) = h(x) - x` is strictly decreasing on `I`, since `|h'| < 1`
  set F : ℝ → ℝ := fun x => (h x).re - x with hF
  have hderiv : ∀ x ∈ I, HasDerivAt F ((deriv h x).re - 1) x := fun x hx =>
    (hasDerivAt_re_ofReal (hh.differentiableOn.differentiableAt
      ((isOpen_nbhd _).mem_nhds (ofReal_mem_nbhd (by linarith) hx)))).sub (hasDerivAt_id x)
  have hcont : ContinuousOn F I := fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn F I := by
    refine strictAntiOn_of_deriv_neg (convex_Icc 0 1) hcont fun x hx => ?_
    have hxI : x ∈ I := interior_subset hx
    rw [(hderiv x hxI).deriv, sub_neg]
    exact (Complex.re_le_norm _).trans_lt
      (hh.norm_deriv_lt_one x (subset_closure (ofReal_mem_nbhd hε hxI)))
  refine hanti.injOn hx hy ?_
  simp only [hF, hhx, hhy, sub_self]

/-- Having no common fixed point in `I` is a `d₂`-open condition in `𝔖_N`: the continuous
function `∑_i |f_i(x) - x|` has a positive minimum `m` on `I`, and `d₂(f, g) < m/(N+1)` keeps
some `|g_i(x) - x|` positive at every `x ∈ I`. -/
theorem exists_forall_d2Sys_lt_not_fixed {N : ℕ} {f : Fin N → ℂ → ℂ} (hf : InUnionClass f)
    (hfix : ¬ ∃ x ∈ I, ∀ i, (f i x).re = x) :
    ∃ r > 0, ∀ g, InUnionClass g → d2Sys f g < r → ¬ ∃ x ∈ I, ∀ i, (g i x).re = x := by
  obtain ⟨ε, hε, hfε⟩ := hf
  push Not at hfix
  set F : ℝ → ℝ := fun x => ∑ i, |(f i x).re - x| with hF
  have hcont : ContinuousOn F I := by
    refine continuousOn_finsetSum _ fun i _ => ?_
    have h1 : ContinuousOn (fun x : ℝ => f i x) I :=
      (hfε i).differentiableOn.continuousOn.comp Complex.continuous_ofReal.continuousOn
        fun x hx => ofReal_mem_nbhd (by linarith) hx
    exact ((Complex.continuous_re.comp_continuousOn h1).sub continuousOn_id).abs
  have hpos : ∀ x ∈ I, 0 < F x := by
    intro x hx
    obtain ⟨i, hi⟩ := hfix x hx
    exact Finset.sum_pos' (fun j _ => abs_nonneg _)
      ⟨i, Finset.mem_univ i, abs_pos.2 (sub_ne_zero.2 hi)⟩
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) hcont
  set m := F x₀
  have hm : 0 < m := hpos x₀ hx₀
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine ⟨m / (N + 1), div_pos hm (by positivity), ?_⟩
  rintro g ⟨ε', hε', hgε⟩ hd ⟨x, hx, hgx⟩
  let Φ : IFS N ε := ⟨f, hε, hfε⟩
  let Ψ : IFS N ε' := ⟨g, hε', hgε⟩
  have hle : ∀ i, |(f i x).re - x| ≤ d2Sys f g := by
    intro i
    calc |(f i x).re - x| = |(f i x - g i x).re| := by rw [Complex.sub_re, hgx i]
      _ ≤ ‖f i x - g i x‖ := Complex.abs_re_le_norm _
      _ ≤ d2Sys f g := (IFS.Continuity.norm_sub_le_d2 Φ Ψ i hx).1
  have hsum : F x ≤ N * d2Sys f g := by
    calc F x ≤ ∑ _i : Fin N, d2Sys f g := Finset.sum_le_sum fun i _ => hle i
      _ = N * d2Sys f g := by simp
  have hmx : m ≤ F x := isMinOn_iff.1 hmin x hx
  have h1 : (N : ℝ) * d2Sys f g ≤ N * (m / (N + 1)) := mul_le_mul_of_nonneg_left hd.le hN
  have h2 : (N : ℝ) * (m / (N + 1)) < m := by
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
    linarith
  linarith

/-- Having no common fixed point in `I` is a `d₂`-dense condition in `𝔖_N` for `N ≥ 2`. If the maps
`f_i` fix a common point `p`, replace one map `f_j` by the perturbation
`f_j^t = (1 - t) f_j + t h_j` of the interpolation `IFS.exists_noCoincidence_near`, with `h_j(p) ≠ p` and small
`t > 0`. A common fixed point of the new system is fixed by some `f_k`, `k ≠ j`, so it is `p`, which
`f_j^t` moves. -/
theorem exists_not_fixed_d2Sys_lt {N : ℕ} (hN : 2 ≤ N) {f : Fin N → ℂ → ℂ}
    (hf : InUnionClass f) {r : ℝ} (hr : 0 < r) :
    ∃ g, InUnionClass g ∧ (¬ ∃ x ∈ I, ∀ i, (g i x).re = x) ∧ d2Sys f g < r := by
  by_cases hfix : ∃ x ∈ I, ∀ i, (f i x).re = x
  swap
  · exact ⟨f, hf, hfix, by rw [d2Sys_self]; exact hr⟩
  obtain ⟨p, hp, hfp⟩ := hfix
  obtain ⟨ε, hε, hfε⟩ := hf
  let Φ : IFS N ε := ⟨f, hε, hfε⟩
  -- a map `f_j` with `h_j(p) ≠ p`, and a second map `f_k`
  obtain ⟨j, hj⟩ : ∃ j : Fin N, IFS.Coincidences.slope N * p + IFS.Coincidences.offset j ≠ p := by
    by_contra! h
    have h01 : (⟨0, by omega⟩ : Fin N) < ⟨1, by omega⟩ := Fin.mk_lt_mk.2 one_pos
    linarith [IFS.Coincidences.offset_add_slope_lt_offset h01, h ⟨0, by omega⟩,
      h ⟨1, by omega⟩, IFS.Coincidences.slope_pos (N := N)]
  have : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.2 hN
  obtain ⟨k, hk⟩ := exists_ne j
  -- the parameter `t`
  set c := Φ.cmin
  have hc : 0 < c := Φ.cmin_pos (by omega)
  obtain ⟨K, hK, hK'⟩ := IFS.Coincidences.exists_deriv_deriv_bound Φ
  set t := min (c / (c + 1)) (r / (4 + K)) / 2
  have ht0 : 0 < t := half_pos (lt_min (by positivity) (by positivity))
  have htt : t < min (c / (c + 1)) (r / (4 + K)) := half_lt_self (lt_min (by positivity)
    (by positivity))
  have ht1 : t * (c + 1) < c := (lt_div_iff₀ (by positivity)).1 (htt.trans_le (min_le_left _ _))
  have ht2 : t * (4 + K) < r := (lt_div_iff₀ (by positivity)).1 (htt.trans_le (min_le_right _ _))
  have htI : t ∈ I := ⟨ht0.le, by nlinarith⟩
  set g := Function.update f j (IFS.Coincidences.homotopy Φ t j) with hg
  refine ⟨g, ⟨ε, hε, fun i => ?_⟩, ?_, ?_⟩
  · by_cases hi : i = j
    · rw [hi, hg, Function.update_self]
      exact IFS.Coincidences.inClass_homotopy Φ ht0 ht1 j
    · rw [hg, Function.update_of_ne hi]
      exact hfε i
  · rintro ⟨x, hx, hgx⟩
    have hxk : (f k x).re = x := by simpa [g, Function.update_of_ne hk] using hgx k
    obtain rfl := eq_of_re_eq_self hε (hfε k) hx hp hxk (hfp k)
    have h := hgx j
    rw [hg, Function.update_self] at h
    rw [IFS.Coincidences.re_homotopy_ofReal, show (Φ.f j x).re = x from hfp j] at h
    have h' : t * (IFS.Coincidences.slope N * x + IFS.Coincidences.offset j - x) = 0 := by
      linarith
    exact hj (by linarith [(mul_eq_zero.1 h').resolve_left ht0.ne'])
  · have h : ∀ i, d2Map (f i) (g i) ≤ t * (4 + K) := by
      intro i
      by_cases hi : i = j
      · rw [hi, hg, Function.update_self]
        exact IFS.Coincidences.d2Map_homotopy_le Φ j hK (hK' j) htI
      · rw [hg, Function.update_of_ne hi, d2Map_self]
        positivity
    exact (Real.iSup_le h (by positivity)).trans_lt ht2

end OpenDense

/-- Corollary 1.7. For `N ≥ 2`, the systems of `𝔖_N` with equality in (1.6) contain a subset `U` of
`𝔖_N` that is open and dense in the `𝒞²` metric. -/
theorem corollary_1_7 (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) {N : ℕ}
    (hN : 2 ≤ N) :
    ∃ U : Set (Fin N → ℂ → ℂ),
      (∀ f ∈ U, ∃ ε : ℝ, ∃ Φ : IFS N ε, Φ.f = f ∧ Φ.DimEquality) ∧
      (∀ f ∈ U, ∃ r > 0, ∀ g, InUnionClass g → d2Sys f g < r → g ∈ U) ∧
      (∀ f, InUnionClass f → ∀ r > 0, ∃ g ∈ U, d2Sys f g < r) := by
  have hN0 : 0 < N := by omega
  obtain ⟨U₁, hU₁, hU₁o, hU₁d⟩ := theorem_1_4 N
  -- the open set of Theorem 1.4, intersected with the systems without common fixed point
  refine ⟨U₁ ∩ {f | InUnionClass f ∧ ¬ ∃ x ∈ I, ∀ i, (f i x).re = x}, ?_, ?_, ?_⟩
  · -- Theorem 1.6, with the remark after it
    rintro f ⟨hf₁, -, hfix⟩
    obtain ⟨ε, Φ, rfl, hΦ⟩ := hU₁ f hf₁
    refine ⟨ε, Φ, rfl, Φ.theorem_1_6 hM hS hN0 (fun h => hfix ?_) (Φ.esc_of_sesc hΦ)⟩
    exact (Φ.exists_attractor_eq_singleton_iff hN0).1 h
  · -- openness
    rintro f ⟨hf₁, hf, hfix⟩
    obtain ⟨r₁, hr₁, h₁⟩ := hU₁o f hf₁
    obtain ⟨r₂, hr₂, h₂⟩ := OpenDense.exists_forall_d2Sys_lt_not_fixed hf hfix
    exact ⟨min r₁ r₂, lt_min hr₁ hr₂, fun g hg hfg =>
      ⟨h₁ g hg (hfg.trans_le (min_le_left _ _)), hg, h₂ g hg (hfg.trans_le (min_le_right _ _))⟩⟩
  · -- density: perturb to remove a common fixed point, then apply Theorem 1.4
    intro f hf r hr
    obtain ⟨g, hg, hgfix, hfg⟩ := OpenDense.exists_not_fixed_d2Sys_lt hN hf (half_pos hr)
    obtain ⟨ρ, hρ, hgρ⟩ := OpenDense.exists_forall_d2Sys_lt_not_fixed hg hgfix
    obtain ⟨h, hh₁, hgh⟩ := hU₁d g hg (min ρ (r / 2)) (lt_min hρ (half_pos hr))
    obtain ⟨ε, Ψ, rfl, -⟩ := hU₁ h hh₁
    have hh : InUnionClass Ψ.f := ⟨ε, Ψ.ε_pos, Ψ.inClass⟩
    refine ⟨Ψ.f, ⟨hh₁, hh, hgρ Ψ.f hh (hgh.trans_le (min_le_left _ _))⟩, ?_⟩
    have h := OpenDense.d2Sys_le_add hf hg hh
    linarith [hgh.trans_le (min_le_right _ _)]

end AnalyticESC
