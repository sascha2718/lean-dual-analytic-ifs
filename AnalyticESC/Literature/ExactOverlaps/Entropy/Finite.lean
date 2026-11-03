module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
Adapted from the LpSelfSimilar entropy library.
-/

public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Tactic

set_option maxSynthPendingDepth 3

@[expose] public section

/-!
Shannon entropy, in nats, for finitely supported probability mass functions.
The finite-support proof is an explicit argument, so the definition cannot
silently assign a finite value to a divergent entropy series. The convention
`0 log 0 = 0` is Mathlib's continuous function `Real.negMulLog`.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.Finite`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

open scoped BigOperators ENNReal

namespace ExactOverlaps.Entropy

/-- Shannon entropy of a finitely supported law, with the natural logarithm. -/
noncomputable def finiteEntropy {α : Type*} (p : PMF α) (hp : p.support.Finite) : ℝ :=
  ∑ a ∈ hp.toFinset, Real.negMulLog (p a).toReal

lemma map_apply_of_injective {α β : Type*} (p : PMF α) {f : α → β}
    (hf : Function.Injective f) (a : α) : p.map f (f a) = p a := by
  classical
  rw [PMF.map_apply, tsum_eq_single a]
  · simp
  · intro b hba
    simp [hf.ne (Ne.symm hba)]

/-- An injective recoding preserves finite Shannon entropy. -/
lemma finiteEntropy_map_of_injective {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    {f : α → β} (hf : Function.Injective f) :
    finiteEntropy (p.map f) (by simpa using hp.image f) = finiteEntropy p hp := by
  classical
  unfold finiteEntropy
  have hfin : (show (p.map f).support.Finite from by simpa using hp.image f).toFinset =
      hp.toFinset.image f := by ext x; simp
  rw [hfin, Finset.sum_image (fun a _ b _ h ↦ hf h)]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_apply_of_injective p hf]

lemma finiteEntropy_uniform {α : Type*} [Fintype α] [Nonempty α] :
    finiteEntropy (PMF.uniformOfFintype α) (Set.toFinite _) = Real.log (Fintype.card α) := by
  classical
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by positivity
  simp [finiteEntropy, PMF.support_uniformOfFintype, PMF.uniformOfFintype_apply,
    Real.negMulLog, Real.log_inv, hcard]

end ExactOverlaps.Entropy
