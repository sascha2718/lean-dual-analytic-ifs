module

public import Mathlib
public import AnalyticESC.Literature.Bowen.Basic

@[expose] public section

/-!
# Bowen's theorem on the one-sided full shift: the weak-* limit

The final step of the proof of

R. Bowen, *Equilibrium states and the ergodic theory of Anosov diffeomorphisms*, Lecture Notes in
Mathematics 470, Springer, 1975, Theorem 1.4,

on the one-sided full shift `ℕ → Fin N`: if for every `M` some probability measure satisfies the
Gibbs bounds (with fixed constants) on all cylinders of length `m ≤ M`, then some probability
measure satisfies them on all cylinders. The space `ℕ → Fin N` is compact and metrisable, so the
space of Borel probability measures is compact for the weak-* topology (Prokhorov); cylinders are
clopen, so their masses depend continuously on the measure, and the Gibbs bounds up to level `M`
define a decreasing sequence of nonempty closed sets.

Adapted from `FractalGeometry.Pressure.ParityShift.Limits`.

## Main declarations

* `FractalGeometry.Bowen.continuous_measureReal_of_isClopen`: the mass of a clopen set is weak-*
  continuous.
* `FractalGeometry.Bowen.isClopen_cyl`: cylinders are clopen.
* `FractalGeometry.Bowen.GibbsUpTo φ ν c₁ c₂ P M`: the Gibbs bounds for cylinders of length
  `m ≤ M`.
* `FractalGeometry.Bowen.exists_gibbs_of_forall_gibbsUpTo`: the limit argument.

Copied from the library `FractalGeometry` (module `FractalGeometry.Bowen.Limit`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Bowen

open MeasureTheory Set

section Clopen

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- On a compact space, the mass of a clopen set is a weak-* continuous function of a probability
measure (the indicator of a clopen set is continuous). -/
theorem continuous_measureReal_of_isClopen {U : Set X} (hU : IsClopen U) :
    Continuous fun ν : ProbabilityMeasure X => (ν : Measure X).real U := by
  refine (ProbabilityMeasure.continuous_integral_continuousMap
    (⟨U.indicator 1, hU.continuous_indicator continuous_const⟩ : C(X, ℝ))).congr fun ν => ?_
  exact integral_indicator_one hU.isOpen.measurableSet

end Clopen

variable {N : ℕ}

/-- Cylinders are clopen: they are preimages under the continuous restriction to `Fin m`, whose
target is discrete. -/
theorem isClopen_cyl (x : ℕ → Fin N) (m : ℕ) : IsClopen (cyl x m) := by
  have e : cyl x m = (fun y : ℕ → Fin N => fun i : Fin m => y i) ⁻¹' {fun i : Fin m => x i} := by
    ext y
    simp only [mem_cyl, mem_preimage, mem_singleton_iff, funext_iff]
    exact ⟨fun h i => h i i.2, fun h i hi => h ⟨i, hi⟩⟩
  rw [e]
  exact (isClopen_discrete _).preimage (continuous_pi fun i => continuous_apply _)

/-- Cylinders are measurable. -/
theorem measurableSet_cyl (x : ℕ → Fin N) (m : ℕ) : MeasurableSet (cyl x m) :=
  (isClopen_cyl x m).isOpen.measurableSet

/-- The Gibbs bounds `c₁ ≤ ν[x₀ ⋯ x_{m-1}] / exp(-P m + S_m φ(x)) ≤ c₂` for all cylinders of
length `m ≤ M`. -/
def GibbsUpTo (φ : (ℕ → Fin N) → ℝ) (ν : Measure (ℕ → Fin N)) (c₁ c₂ P : ℝ) (M : ℕ) : Prop :=
  ∀ x : ℕ → Fin N, ∀ m ≤ M,
    c₁ * Real.exp (-P * m + birkhoff φ m x) ≤ ν.real (cyl x m) ∧
      ν.real (cyl x m) ≤ c₂ * Real.exp (-P * m + birkhoff φ m x)

variable {φ : (ℕ → Fin N) → ℝ} {c₁ c₂ P : ℝ}

/-- The Gibbs bounds up to level `M` define a weak-* closed set of probability measures. -/
theorem isClosed_setOf_gibbsUpTo (M : ℕ) :
    IsClosed {ν : ProbabilityMeasure (ℕ → Fin N) | GibbsUpTo φ ν c₁ c₂ P M} := by
  have e : {ν : ProbabilityMeasure (ℕ → Fin N) | GibbsUpTo φ ν c₁ c₂ P M} =
      ⋂ x : ℕ → Fin N, ⋂ m : ℕ, ⋂ _ : m ≤ M,
        ({ν : ProbabilityMeasure (ℕ → Fin N) |
            c₁ * Real.exp (-P * m + birkhoff φ m x) ≤ (ν : Measure (ℕ → Fin N)).real (cyl x m)} ∩
          {ν : ProbabilityMeasure (ℕ → Fin N) |
            (ν : Measure (ℕ → Fin N)).real (cyl x m) ≤
              c₂ * Real.exp (-P * m + birkhoff φ m x)}) := by
    ext ν
    simp only [mem_ofPred_eq, mem_iInter, mem_inter_iff, GibbsUpTo]
  rw [e]
  refine isClosed_iInter fun x => isClosed_iInter fun m => isClosed_iInter fun _ => ?_
  have hc := continuous_measureReal_of_isClopen (isClopen_cyl x m)
  exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)

/-- The limit argument: if for every level `M` some probability measure satisfies the Gibbs
bounds with the constants `c₁, c₂, P` on all cylinders of length `m ≤ M`, then some probability
measure satisfies them on all cylinders. -/
theorem exists_gibbs_of_forall_gibbsUpTo
    (h : ∀ M : ℕ, ∃ ν : Measure (ℕ → Fin N), IsProbabilityMeasure ν ∧ GibbsUpTo φ ν c₁ c₂ P M) :
    ∃ ν : Measure (ℕ → Fin N), IsProbabilityMeasure ν ∧ ∀ (x : ℕ → Fin N) (m : ℕ),
      c₁ * Real.exp (-P * m + birkhoff φ m x) ≤ ν.real (cyl x m) ∧
        ν.real (cyl x m) ≤ c₂ * Real.exp (-P * m + birkhoff φ m x) := by
  set K : ℕ → Set (ProbabilityMeasure (ℕ → Fin N)) := fun M => {ν | GibbsUpTo φ ν c₁ c₂ P M}
  have hclosed : ∀ M, IsClosed (K M) := isClosed_setOf_gibbsUpTo
  have hmono : ∀ M, K (M + 1) ⊆ K M := fun M ν hν x m hm => hν x m (hm.trans M.le_succ)
  have hne : ∀ M, (K M).Nonempty := fun M => by
    obtain ⟨ν, hp, hg⟩ := h M
    exact ⟨⟨ν, hp⟩, hg⟩
  obtain ⟨ν, hν⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hmono hne
    (hclosed 0).isCompact hclosed
  rw [mem_iInter] at hν
  exact ⟨ν, inferInstance, fun x m => hν m x m le_rfl⟩

end FractalGeometry.Bowen
