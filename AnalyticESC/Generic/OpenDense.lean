module

public import AnalyticESC.Generic.Density
public import AnalyticESC.Generic.Coincidences
public import AnalyticESC.Generic.Continuity
public import AnalyticESC.Main.Dichotomy

@[expose] public section

/-!
# Theorem 1.4

The IFSs of `𝔖_N` that satisfy the SESC contain a `d₂`-open and `d₂`-dense subset of `𝔖_N`, the
union class of decision D1. The open set consists of the systems whose dual IFS satisfies the
SSC: it is open by Lemma 2.6, its systems satisfy the SESC by Theorem 2.2, and it is dense by
Lemma 4.2 and the density step. The density step combines two perturbations, so it uses the
triangle inequality for `d₂` between systems of `𝔖_N(ε)` for different `ε`. For `N = 0` the
dual IFS has no attractor, and the open set consists of all systems.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace OpenDense

/-- The triangle inequality for `sup_{x ∈ I} |F(x) - H(x)|`, for maps continuous on a set
containing `I`. -/
theorem iSup_norm_sub_le_add {F G H : ℂ → ℂ} {U : Set ℂ} (hIU : ((↑) : ℝ → ℂ) '' I ⊆ U)
    (hF : ContinuousOn F U) (hG : ContinuousOn G U) (hH : ContinuousOn H U) :
    (⨆ x : I, ‖F ((x : ℝ) : ℂ) - H ((x : ℝ) : ℂ)‖) ≤
      (⨆ x : I, ‖F ((x : ℝ) : ℂ) - G ((x : ℝ) : ℂ)‖) +
        ⨆ x : I, ‖G ((x : ℝ) : ℂ) - H ((x : ℝ) : ℂ)‖ := by
  have hFG := IFS.Continuity.bddAbove_range_norm_sub hIU hF hG
  have hGH := IFS.Continuity.bddAbove_range_norm_sub hIU hG hH
  refine Real.iSup_le (fun x => ?_) (add_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _)
    (Real.iSup_nonneg fun _ => norm_nonneg _))
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add (le_ciSup hFG x) (le_ciSup hGH x))

/-- The triangle inequality for the `𝒞²` distance on `I` between maps holomorphic on an open set
containing `I`. -/
theorem d2Map_le_add {f g h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hIU : ((↑) : ℝ → ℂ) '' I ⊆ U) (hf : DifferentiableOn ℂ f U)
    (hg : DifferentiableOn ℂ g U) (hh : DifferentiableOn ℂ h U) :
    d2Map f h ≤ d2Map f g + d2Map g h := by
  have e0 := iSup_norm_sub_le_add hIU hf.continuousOn hg.continuousOn hh.continuousOn
  have e1 := iSup_norm_sub_le_add hIU (hf.deriv hU).continuousOn (hg.deriv hU).continuousOn
    (hh.deriv hU).continuousOn
  have e2 := iSup_norm_sub_le_add hIU ((hf.deriv hU).deriv hU).continuousOn
    ((hg.deriv hU).deriv hU).continuousOn ((hh.deriv hU).deriv hU).continuousOn
  unfold d2Map
  linarith

/-- The `𝒞²` distance on `I` is nonnegative. -/
theorem d2Map_nonneg (f g : ℂ → ℂ) : 0 ≤ d2Map f g :=
  add_nonneg (add_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _)
    (Real.iSup_nonneg fun _ => norm_nonneg _)) (Real.iSup_nonneg fun _ => norm_nonneg _)

/-- The triangle inequality for `d₂` on `𝔖_N`, for systems in `𝔖_N(ε)` for different `ε`. -/
theorem d2_le_add {N : ℕ} {ε ε' ε'' : ℝ} (Φ : IFS N ε) (Φ' : IFS N ε') (Ψ : IFS N ε'') :
    d2 Φ Ψ ≤ d2 Φ Φ' + d2 Φ' Ψ := by
  set U := nbhd (2 * ε) ∩ nbhd (2 * ε') ∩ nbhd (2 * ε'')
  have hU : IsOpen U := ((isOpen_nbhd _).inter (isOpen_nbhd _)).inter (isOpen_nbhd _)
  have hIU : ((↑) : ℝ → ℂ) '' I ⊆ U :=
    subset_inter (subset_inter (IFS.Continuity.image_I_subset_nbhd (by linarith [Φ.ε_pos]))
      (IFS.Continuity.image_I_subset_nbhd (by linarith [Φ'.ε_pos])))
      (IFS.Continuity.image_I_subset_nbhd (by linarith [Ψ.ε_pos]))
  have hUΦ : U ⊆ nbhd (2 * ε) := inter_subset_left.trans inter_subset_left
  have hUΦ' : U ⊆ nbhd (2 * ε') := inter_subset_left.trans inter_subset_right
  have hUΨ : U ⊆ nbhd (2 * ε'') := inter_subset_right
  have h1 : 0 ≤ d2 Φ Φ' := Real.iSup_nonneg fun _ => d2Map_nonneg _ _
  have h2 : 0 ≤ d2 Φ' Ψ := Real.iSup_nonneg fun _ => d2Map_nonneg _ _
  refine Real.iSup_le (fun i => ?_) (add_nonneg h1 h2)
  refine (d2Map_le_add hU hIU ((Φ.inClass i).differentiableOn.mono hUΦ)
    ((Φ'.inClass i).differentiableOn.mono hUΦ') ((Ψ.inClass i).differentiableOn.mono hUΨ)).trans
    (add_le_add ?_ ?_)
  · exact le_ciSup (f := fun i => d2Map (Φ.f i) (Φ'.f i)) (Set.finite_range _).bddAbove i
  · exact le_ciSup (f := fun i => d2Map (Φ'.f i) (Ψ.f i)) (Set.finite_range _).bddAbove i

/-- Without letters, every IFS satisfies the SESC: distinct words of equal length do not
exist. -/
theorem sesc_of_eq_zero {ε : ℝ} (Φ : IFS 0 ε) : Φ.SESC :=
  ⟨1, one_pos, fun _ i _ hij => absurd (funext fun k => (i k).elim0) hij⟩

end OpenDense

/-- Theorem 1.4. The systems of `𝔖_N` satisfying the SESC contain a subset `U` of `𝔖_N` that is
open and dense in the `𝒞²` metric. -/
theorem theorem_1_4 (N : ℕ) :
    ∃ U : Set (Fin N → ℂ → ℂ),
      (∀ f ∈ U, ∃ ε : ℝ, ∃ Φ : IFS N ε, Φ.f = f ∧ Φ.SESC) ∧
      (∀ f ∈ U, ∃ r > 0, ∀ g, InUnionClass g → d2Sys f g < r → g ∈ U) ∧
      (∀ f, InUnionClass f → ∀ r > 0, ∃ g ∈ U, d2Sys f g < r) := by
  -- The systems whose dual IFS satisfies the SSC; all systems if `N = 0`.
  refine ⟨{f | ∃ ε : ℝ, ∃ Φ : IFS N ε, Φ.f = f ∧ (0 < N → Φ.DualSSC)}, ?_, ?_, ?_⟩
  · -- The SESC, by Theorem 2.2.
    rintro _ ⟨ε, Φ, rfl, hΦ⟩
    refine ⟨ε, Φ, rfl, ?_⟩
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact OpenDense.sesc_of_eq_zero Φ
    · exact Φ.theorem_2_2 (hΦ hN)
  · -- Openness, by Lemma 2.6.
    rintro _ ⟨ε, Φ, rfl, hΦ⟩
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · refine ⟨1, one_pos, fun g ⟨ε', hε', hg⟩ _ => ⟨ε', ⟨g, hε', hg⟩, rfl, fun h => ?_⟩⟩
      exact absurd h (lt_irrefl 0)
    obtain ⟨δ, hδ, hΨ⟩ := Φ.lemma_2_6_union (hΦ hN)
    exact ⟨δ, hδ, fun g ⟨ε', hε', hg⟩ hfg =>
      ⟨ε', ⟨g, hε', hg⟩, rfl, fun _ => hΨ (⟨g, hε', hg⟩ : IFS N ε') hfg⟩⟩
  · -- Density, by Lemma 4.2 and the density step.
    rintro f ⟨ε, hε, hf⟩ r hr
    let Φ : IFS N ε := ⟨f, hε, hf⟩
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · refine ⟨f, ⟨ε, Φ, rfl, fun h => absurd h (lt_irrefl 0)⟩, ?_⟩
      rw [d2Sys, Real.iSup_of_isEmpty]
      exact hr
    obtain ⟨Φ₁, hΦ₁, hI, hnc⟩ := Φ.lemma_4_2 (half_pos hr)
    obtain ⟨ε', Ψ, hΨ, hssc⟩ := IFS.exists_dualSSC_near hN Φ₁ hI hnc (half_pos hr)
    refine ⟨Ψ.f, ⟨ε', Ψ, rfl, fun _ => hssc⟩, ?_⟩
    have h := OpenDense.d2_le_add Φ Φ₁ Ψ
    change d2 Φ Ψ < r
    linarith

end AnalyticESC
