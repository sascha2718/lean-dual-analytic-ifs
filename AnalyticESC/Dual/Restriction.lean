module

public import AnalyticESC.Conjugation.DualConj
public import AnalyticESC.Generic.Class

@[expose] public section

/-!
# Independence of the admissible radius

Restriction to a smaller neighbourhood is continuous and injective on the analytic function
space. It intertwines the dual operators, maps the dual attractor onto the smaller-radius
attractor, and preserves SSC, singleton attractors and common fixed points of specified words.
This formalises the paragraph following Lemma 2.1 in Section 2.1.
-/

namespace AnalyticESC

open Set Metric Filter Topology
open scoped UniformConvergence

variable {ε ρ : ℝ}

/-- Restriction from `B_ε` to `B_ρ`. -/
def restrictNbhd (hle : ρ ≤ ε) (u : nbhd ε →ᵤ ℂ) : nbhd ρ →ᵤ ℂ :=
  UniformFun.ofFun fun z => UniformFun.toFun u ⟨z, nbhd_mono hle z.2⟩

@[simp] theorem restrictNbhd_toNbhd (hle : ρ ≤ ε) (g : ℂ → ℂ) :
    restrictNbhd hle (toNbhd ε g) = toNbhd ρ g := rfl

theorem continuous_restrictNbhd (hle : ρ ≤ ε) : Continuous (restrictNbhd hle) :=
  UniformFun.precomp_uniformContinuous.continuous

theorem restrictNbhd_mem (hle : ρ ≤ ε) {u : nbhd ε →ᵤ ℂ}
    (hu : u ∈ analyticSpace ε) : restrictNbhd hle u ∈ analyticSpace ρ := by
  obtain ⟨g, hd, hc, hr, rfl⟩ := hu
  exact ⟨g, hd.mono (nbhd_mono hle), hc.mono (closure_mono (nbhd_mono hle)), hr, rfl⟩

/-- Injectivity follows from agreement on the real unit interval. -/
theorem restrictNbhd_injOn (hρ : 0 < ρ) (hle : ρ ≤ ε) :
    InjOn (restrictNbhd hle) (analyticSpace ε) := by
  rintro u ⟨g, hg, -, -, rfl⟩ v ⟨h, hh, -, -, rfl⟩ he
  have hI : ∀ x ∈ I, g x = h x := fun x hx =>
    congrArg (fun u : nbhd ρ →ᵤ ℂ => UniformFun.toFun u ⟨(x : ℂ), ofReal_mem_nbhd hρ hx⟩) he
  have heq := eqOn_nbhd_of_eqOn_Icc (hρ.trans_le hle) hg hh zero_lt_one subset_rfl hI
  apply UniformFun.toFun.injective
  funext z
  exact heq z.2

namespace IFS

variable {N : ℕ} (Φ : IFS N ε) (hρ : 0 < ρ) (hle : ρ ≤ ε)

/-- Restriction intertwines each dual operator. -/
theorem restrictNbhd_dualOpU (i : Fin N) (u : nbhd ε →ᵤ ℂ) :
    restrictNbhd hle (Φ.dualOpU i u) =
      (Φ.restrict hρ hle).dualOpU i (restrictNbhd hle u) := rfl

/-- Restriction intertwines every finite dual composition. -/
theorem restrictNbhd_dualCompOn (a : List (Fin N)) (u : nbhd ε →ᵤ ℂ) :
    restrictNbhd hle (Φ.dualCompOn a u) =
      (Φ.restrict hρ hle).dualCompOn a (restrictNbhd hle u) := by
  induction a with
  | nil => rfl
  | cons i a ih =>
    change restrictNbhd hle (Φ.dualOpU i (Φ.dualCompOn a u)) = _
    rw [restrictNbhd_dualOpU, ih]
    rfl

/-- The global formula for the dual projection does not depend on the radius. -/
@[simp] theorem restrict_dualProj (w : Word N) :
    (Φ.restrict hρ hle).dualProj w = Φ.dualProj w := rfl

/-- Restriction maps the dual attractor onto the attractor at the smaller radius. -/
theorem isDualAttractor_restrict_image (hN : 0 < N) {Λ : Set (nbhd ε →ᵤ ℂ)}
    (hΛ : Φ.IsDualAttractor Λ) :
    (Φ.restrict hρ hle).IsDualAttractor (restrictNbhd hle '' Λ) := by
  have he := (Φ.existsUnique_isDualAttractor hN).unique hΛ (Φ.isDualAttractor_range hN)
  rw [he, ← range_comp]
  exact (Φ.restrict hρ hle).isDualAttractor_range hN

/-- SSC is independent of the admissible radius. -/
theorem restrict_dualSSC_iff (hN : 0 < N) :
    (Φ.restrict hρ hle).DualSSC ↔ Φ.DualSSC :=
  ((Φ.restrict hρ hle).dualSSC_iff_ne hN).trans (Φ.dualSSC_iff_ne hN).symm

/-- Having a singleton dual attractor is independent of the admissible radius. -/
theorem restrict_singleton_iff (hN : 0 < N) :
    (∃ Λ, (Φ.restrict hρ hle).IsDualAttractor Λ ∧ ∃ h, Λ = {h}) ↔
      ∃ Λ, Φ.IsDualAttractor Λ ∧ ∃ h, Λ = {h} :=
  ((Φ.restrict hρ hle).theorem_2_3_conj hN).symm.trans (Φ.theorem_2_3_conj hN)

/-- Equality of the fixed points of any two specified nonempty dual compositions is
independent of the admissible radius; the words need not have the same length. -/
theorem restrict_common_fixedPoint_iff {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (i : Fin m → Fin N) (j : Fin n → Fin N) :
    (∃ u ∈ analyticSpace ρ,
      (Φ.restrict hρ hle).dualCompOn (List.ofFn i) u = u ∧
      (Φ.restrict hρ hle).dualCompOn (List.ofFn j) u = u) ↔
    ∃ u ∈ analyticSpace ε,
      Φ.dualCompOn (List.ofFn i) u = u ∧ Φ.dualCompOn (List.ofFn j) u = u := by
  constructor
  · rintro ⟨u, hu, hi, hj⟩
    have he := (((Φ.restrict hρ hle).dualCompOn_fixed_iff hm i hu).mp hi).symm.trans
      (((Φ.restrict hρ hle).dualCompOn_fixed_iff hn j hu).mp hj)
    have he' : toNbhd ε (Φ.dualProj (.inf (periodic hm i))) =
        toNbhd ε (Φ.dualProj (.inf (periodic hn j))) :=
      restrictNbhd_injOn hρ hle (Φ.dualProj_mem_analyticSpace _)
        (Φ.dualProj_mem_analyticSpace _) he
    refine ⟨_, Φ.dualProj_mem_analyticSpace _, Φ.dualCompOn_periodic hm i, ?_⟩
    rw [he']
    exact Φ.dualCompOn_periodic hn j
  · rintro ⟨u, hu, hi, hj⟩
    refine ⟨restrictNbhd hle u, restrictNbhd_mem hle hu, ?_, ?_⟩
    · rw [← Φ.restrictNbhd_dualCompOn hρ hle, hi]
    · rw [← Φ.restrictNbhd_dualCompOn hρ hle, hj]

end IFS

end AnalyticESC
