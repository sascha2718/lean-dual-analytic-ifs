module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.IndependentPair
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.EntropySupport

set_option maxSynthPendingDepth 3

/-!
# Convolution of finitely supported laws

The convolution is the actual law of the sum of an independent pair. Its
entropy lies between each summand entropy and their sum.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.Convolution`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace ExactOverlaps.Entropy

noncomputable def discreteConvolution {G : Type*} [Add G] (p q : PMF G) : PMF G :=
  (independentPair p q).map (fun x ↦ x.1 + x.2)

lemma discreteConvolution_eq_bind {G : Type*} [Add G] (p q : PMF G) :
    discreteConvolution p q = p.bind (fun a ↦ q.map (fun b ↦ a + b)) := by
  simp only [discreteConvolution, independentPair, PMF.map_bind, PMF.map_comp,
    Function.comp_def]

lemma discreteConvolution_support_finite {G : Type*} [Add G]
    (p q : PMF G) (hp : p.support.Finite) (hq : q.support.Finite) :
    (discreteConvolution p q).support.Finite := by
  simpa [discreteConvolution] using
    (independentPair_support_finite p q hp hq).image (fun x ↦ x.1 + x.2)

lemma discreteConvolution_assoc {G : Type*} [AddSemigroup G] (p q r : PMF G) :
    discreteConvolution (discreteConvolution p q) r =
      discreteConvolution p (discreteConvolution q r) := by
  simp only [discreteConvolution_eq_bind, PMF.bind_bind, PMF.bind_map,
    PMF.map_bind, PMF.map_comp, Function.comp_def, add_assoc]

lemma discreteConvolution_comm {G : Type*} [AddCommMagma G] (p q : PMF G) :
    discreteConvolution p q = discreteConvolution q p := by
  simp only [discreteConvolution_eq_bind, PMF.map]
  rw [PMF.bind_comm]
  simp only [Function.comp_def, add_comm]

theorem finiteEntropy_discreteConvolution_le_add {G : Type*} [Add G]
    (p q : PMF G) (hp : p.support.Finite) (hq : q.support.Finite) :
    finiteEntropy (discreteConvolution p q) (discreteConvolution_support_finite p q hp hq) ≤
      finiteEntropy p hp + finiteEntropy q hq := by
  have h := finiteEntropy_map_le (independentPair p q)
    (independentPair_support_finite p q hp hq) (fun x ↦ x.1 + x.2)
  rwa [finiteEntropy_independentPair] at h

theorem finiteEntropy_right_le_discreteConvolution {G : Type*} [AddLeftCancelSemigroup G]
    (p q : PMF G) (hp : p.support.Finite) (hq : q.support.Finite) :
    finiteEntropy q hq ≤
      finiteEntropy (discreteConvolution p q) (discreteConvolution_support_finite p q hp hq) := by
  classical
  let : Fintype p.support := hp.fintype
  have he : (supportLaw p).bind (fun a ↦ q.map (fun b ↦ (a : G) + b)) =
      discreteConvolution p q := by
    rw [discreteConvolution_eq_bind]
    conv_rhs => rw [← supportLaw_map_val p, PMF.bind_map]
    rfl
  have h := average_finiteEntropy_le_bind (supportLaw p)
    (fun a ↦ q.map (fun b ↦ (a : G) + b))
    (fun a ↦ by simpa using hq.image (fun b ↦ (a : G) + b))
  simp only [finiteEntropy_map_of_injective q hq (fun _ _ h ↦ add_left_cancel h),
    ← Finset.sum_mul, sum_pmf_toReal, one_mul, he] at h
  exact h

theorem finiteEntropy_left_le_discreteConvolution {G : Type*} [AddCommGroup G]
    (p q : PMF G) (hp : p.support.Finite) (hq : q.support.Finite) :
    finiteEntropy p hp ≤
      finiteEntropy (discreteConvolution p q) (discreteConvolution_support_finite p q hp hq) := by
  have h := finiteEntropy_right_le_discreteConvolution q p hq hp
  simpa only [discreteConvolution_comm q p] using h

end ExactOverlaps.Entropy
