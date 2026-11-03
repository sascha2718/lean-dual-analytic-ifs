module

public import AnalyticESC.Literature.Rapaport.Analytic.Setup
public import AnalyticESC.Literature.SelfConformal.CutSet

@[expose] public section

/-!
# The self-conformal measure has the structure used in Section 3

For `φ` satisfying `AnalyticESC.RapaportHyp` and a positive probability vector `p`, the
self-conformal measure `μ = selfConformal φ p hp` is a probability measure on `I` without atoms
(Section 2.3 of A. Rapaport, *Dimension of self-conformal measures associated to an exponentially
separated analytic IFS on ℝ*, arXiv:2412.16753v2, using that the maps have no common fixed
point), and for each `n` it satisfies (2.7), `μ = ∑_{u ∈ Ψ_n} p_u φ_u μ`, with the bounds (2.8),
`C⁻¹ 2^{-n} ≤ |φ_u'| ≤ C 2^{-n}` on `I`, from the bounded distortion property (Lemma 2.1). All
these facts are taken from the shared toolkit `FractalGeometry.SelfConformal`.

## Main declarations

* `biLipOn_realComp_of_isCutWord`: the maps `φ_u`, `u ∈ Ψ_n`, are bi-Lipschitz on `I` with
  constants `C^{-1} 2^{-n}` and `C 2^{-n}`.
* `scStructure_selfConformal`: `SCStructure (selfConformal φ p hp)`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.SelfConformalStructure`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic

open MeasureTheory ProbabilityTheory Set Filter Topology FractalGeometry.SelfConformal
open scoped ENNReal

variable {N : ℕ} {φ : Fin N → ℝ → ℝ}

/-- For `u ∈ Ψ_n`, `φ_u` is bi-Lipschitz on `I` with constants `C⁻¹ 2^{-n}` and `C 2^{-n}`,
where `C` is the product of the distortion constant and the constant of (2.8). -/
theorem biLipOn_realComp_of_isCutWord (hφ : AnalyticESC.RapaportHyp φ) (hN : 0 < N) {n : ℕ}
    {u : List (Fin N)} (hu : IsCutWord φ n u) :
    BiLipOn (AnalyticESC.realComp φ u) ((distConst φ * cutConst φ)⁻¹ / 2 ^ n)
      (distConst φ * cutConst φ / 2 ^ n) := by
  intro x hx y hy
  have hD := one_lt_distConst hφ
  have hC := one_lt_cutConst hφ hN
  have h0 : (0 : ℝ) ∈ AnalyticESC.I := ⟨le_rfl, zero_le_one⟩
  have hup := abs_realComp_sub_le_distConst hφ u hx hy h0
  have hlo := distConst_inv_mul_le_abs_realComp_sub hφ u hx hy h0
  have hd1 := abs_deriv_le_of_isCutWord hφ hN hu h0
  have hd2 := le_abs_deriv_of_isCutWord hφ hN hu h0
  have e : (2 : ℝ)⁻¹ ^ n = 1 / 2 ^ n := by rw [inv_pow, one_div]
  rw [e] at hd1 hd2
  have hxy := abs_nonneg (x - y)
  constructor
  · calc (distConst φ * cutConst φ)⁻¹ / 2 ^ n * |x - y| =
          (distConst φ)⁻¹ * ((cutConst φ)⁻¹ * (1 / 2 ^ n)) * |x - y| := by
          rw [mul_inv]
          ring
      _ ≤ (distConst φ)⁻¹ * |deriv (AnalyticESC.realComp φ u) 0| * |x - y| := by gcongr
      _ ≤ _ := hlo
  · calc |AnalyticESC.realComp φ u x - AnalyticESC.realComp φ u y|
        ≤ distConst φ * |deriv (AnalyticESC.realComp φ u) 0| * |x - y| := hup
      _ ≤ distConst φ * (cutConst φ * (1 / 2 ^ n)) * |x - y| := by
          gcongr
      _ = distConst φ * cutConst φ / 2 ^ n * |x - y| := by ring

/-- The self-conformal measure of a system satisfying Rapaport's hypotheses has the structure
`SCStructure`. -/
theorem scStructure_selfConformal [NeZero N] (hφ : AnalyticESC.RapaportHyp φ) {p : Fin N → ℝ}
    (hp : AnalyticESC.IsProbVec p) : SCStructure (selfConformal φ p hp) := by
  classical
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hμI := selfConformal_compl_I hφ hp
  refine ⟨inferInstance, hμI, selfConformal_singleton hφ hp, ?_⟩
  have hD := one_lt_distConst hφ
  have hC := one_lt_cutConst hφ hN
  refine ⟨distConst φ * cutConst φ, by nlinarith, fun n => ?_⟩
  set e := (cutSet φ n).equivFin
  refine ⟨(cutSet φ n).card, fun j => weight p (e.symm j),
    fun j => clampToI (AnalyticESC.realComp φ (e.symm j)), fun j => weight_nonneg hp _, ?_, ?_,
    fun j => ?_⟩
  · rw [← sum_weight_cutSet hφ hp n, ← Finset.sum_coe_sort (cutSet φ n)]
    exact Equiv.sum_comp e.symm (fun u => weight p u)
  · conv_lhs => rw [selfConformal_eq_sum_cutSet hφ hp n, ← Finset.sum_coe_sort (cutSet φ n)]
    rw [← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_clampToI hμI]
  · have hu : IsCutWord φ n (e.symm j : List (Fin N)) := (mem_cutSet hφ).1 (e.symm j).2
    have hL := biLipOn_realComp_of_isCutWord hφ hN hu
    refine ⟨continuous_clampToI hL.continuousOn,
      mapsTo_clampToI (mapsTo_realComp hφ _), ?_⟩
    have := hL.clampToI
    convert this using 2

end FractalGeometry.Rapaport.Analytic
