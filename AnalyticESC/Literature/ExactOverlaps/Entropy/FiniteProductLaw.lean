module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.IndependentPair

set_option maxSynthPendingDepth 3

/-!
# Genuine finite product laws

Finite tuples are represented by nested products. Their probability law is
constructed recursively from the actual independent-pair PMF. Marginals
may differ, and finiteness is required only of their supports when used.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.FiniteProductLaw`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

namespace ExactOverlaps.Entropy

universe u

def FiniteTuple (α : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => α × FiniteTuple α n

instance finiteTupleFintype (α : Type*) [Fintype α] : (n : ℕ) → Fintype (FiniteTuple α n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by
      letI := finiteTupleFintype α n
      exact inferInstanceAs (Fintype (α × FiniteTuple α n))

def tupleCoordinate {α : Type*} : (n : ℕ) → FiniteTuple α n → Fin n → α
  | 0, _, i => Fin.elim0 i
  | n + 1, w, i => Fin.cases w.1 (fun j ↦ tupleCoordinate n w.2 j) i

noncomputable def tupleLaw {α : Type*} : (n : ℕ) → (Fin n → PMF α) → PMF (FiniteTuple α n)
  | 0, _ => PMF.pure PUnit.unit
  | n + 1, p => independentPair (p 0) (tupleLaw n (fun i ↦ p i.succ))

lemma tupleLaw_support_finite {α : Type*} (n : ℕ) (p : Fin n → PMF α)
    (hp : ∀ i, (p i).support.Finite) : (tupleLaw n p).support.Finite := by
  induction n with
  | zero =>
    change (PMF.pure (PUnit.unit : PUnit)).support.Finite
    rw [PMF.support_pure]
    exact Set.finite_singleton _
  | succ n ih =>
    exact independentPair_support_finite (p 0) (tupleLaw n (fun i ↦ p i.succ))
      (hp 0) (ih (fun i ↦ p i.succ) (fun i ↦ hp i.succ))

lemma tupleLaw_coordinate {α : Type*} (n : ℕ) (p : Fin n → PMF α) (i : Fin n) :
    (tupleLaw n p).map (fun w ↦ tupleCoordinate n w i) = p i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change (independentPair (p 0) (tupleLaw n (fun j ↦ p j.succ))).map Prod.fst = p 0
      exact independentPair_map_fst (p 0) (tupleLaw n (fun j ↦ p j.succ))
    · change (independentPair (p 0) (tupleLaw n (fun j ↦ p j.succ))).map
        (fun w ↦ tupleCoordinate n w.2 j) = p j.succ
      rw [show (fun w : α × FiniteTuple α n ↦ tupleCoordinate n w.2 j) =
        (fun w ↦ tupleCoordinate n w j) ∘ Prod.snd from rfl,
        ← PMF.map_comp, independentPair_map_snd]
      exact ih (fun j ↦ p j.succ) j

noncomputable def iidTupleLaw {α : Type*} (p : PMF α) (n : ℕ) : PMF (FiniteTuple α n) :=
  tupleLaw n (fun _ ↦ p)

lemma iidTupleLaw_support_finite {α : Type*} (p : PMF α) (hp : p.support.Finite) (n : ℕ) :
    (iidTupleLaw p n).support.Finite := tupleLaw_support_finite n (fun _ ↦ p) (fun _ ↦ hp)

lemma iidTupleLaw_coordinate {α : Type*} (p : PMF α) (n : ℕ) (i : Fin n) :
    (iidTupleLaw p n).map (fun w ↦ tupleCoordinate n w i) = p :=
  tupleLaw_coordinate n (fun _ ↦ p) i

def tupleSum {α : Type*} (f : α → ℝ) : (n : ℕ) → FiniteTuple α n → ℝ
  | 0, _ => 0
  | n + 1, w => f w.1 + tupleSum f n w.2

end ExactOverlaps.Entropy
