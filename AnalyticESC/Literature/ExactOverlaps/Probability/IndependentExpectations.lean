module

public import AnalyticESC.Literature.ExactOverlaps.Entropy.IndependentPair
public import AnalyticESC.Literature.ExactOverlaps.Probability.FiniteMoments

set_option maxSynthPendingDepth 3

/-!
# Actual expectations under an independent finite pair

The product PMF has the product support and product atom masses. Finite
expectations consequently equal iterated expectations and factor for
products of coordinate functions.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Probability.IndependentExpectations`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open scoped BigOperators ENNReal Classical

namespace ExactOverlaps.FiniteProbability

lemma expectation_mul_const {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → ℝ) (c : ℝ) :
    expectation p hp (fun a ↦ f a * c) = expectation p hp f * c := by
  simp only [expectation, ← mul_assoc, ← Finset.sum_mul]

lemma expectation_independentPair {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (f : α × β → ℝ) :
    expectation (Entropy.independentPair p q) (Entropy.independentPair_support_finite p q hp hq) f =
      expectation p hp (fun a ↦ expectation q hq (fun b ↦ f (a, b))) := by
  have hs : (Entropy.independentPair_support_finite p q hp hq).toFinset =
      hp.toFinset ×ˢ hq.toFinset := by
    ext z
    simp [Entropy.independentPair_support]
  unfold expectation
  rw [hs, Finset.sum_product]
  simp only [Entropy.independentPair_apply, ENNReal.toReal_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma expectation_independentPair_mul {α β : Type*} (p : PMF α) (q : PMF β)
    (hp : p.support.Finite) (hq : q.support.Finite) (f : α → ℝ) (g : β → ℝ) :
    expectation (Entropy.independentPair p q) (Entropy.independentPair_support_finite p q hp hq)
      (fun z ↦ f z.1 * g z.2) = expectation p hp f * expectation q hq g := by
  rw [expectation_independentPair]
  change expectation p hp (fun a ↦ expectation q hq (fun b ↦ f a * g b)) = _
  simp_rw [expectation_const_mul q hq]
  exact expectation_mul_const p hp f _

lemma independentPair_map_pair {α β γ δ : Type*} (p : PMF α) (q : PMF β)
    (f : α → γ) (g : β → δ) :
    (Entropy.independentPair p q).map (fun z ↦ (f z.1, g z.2)) =
      Entropy.independentPair (p.map f) (q.map g) := by
  have he : (Entropy.independentPair p q).map (fun z ↦ (f z.1, g z.2)) =
      ((Entropy.independentPair p q).map (fun z ↦ (f z.1, z.2))).map (fun z ↦ (z.1, g z.2)) := by
    rw [PMF.map_comp]
    rfl
  rw [he, Entropy.independentPair_map_left, Entropy.independentPair_map_right]

end ExactOverlaps.FiniteProbability
