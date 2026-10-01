module

public import AnalyticESC.Dual.Attractor

@[expose] public section

/-!
# Conjugacy to self-similar systems

The vocabulary of Definition 1.9 and Theorems 1.12 and 2.3: analytic invertible changes of
coordinates on `[0,1]`, conjugacy and sub-conjugacy to self-similar systems, periodic words and
the iterates of the dual operators on `C^ω_ε([0,1])`.
-/

namespace AnalyticESC

open Set
open scoped UniformConvergence

/-- `g` is an analytic, invertible map on `[0,1]` (Definition 1.9): analytic on a neighbourhood
of each point of `[0,1]` and injective on `[0,1]`. -/
def IsAnalyticCoord (g : ℝ → ℝ) : Prop := AnalyticOnNhd ℝ g I ∧ InjOn g I

/-- The maps `F_j` of `[0,1]` are conjugated to a self-similar IFS (Definition 1.9): for an
analytic invertible `g`, `g ∘ F_j ∘ g⁻¹` is the similarity `y ↦ λ_j y + t_j` with
`λ_j ∈ (-1,1) \ {0}`, that is, `g(F_j(x)) = λ_j g(x) + t_j` on `[0,1]`. -/
def ConjSelfSimilar {M : ℕ} (F : Fin M → ℝ → ℝ) : Prop :=
  ∃ g, IsAnalyticCoord g ∧ ∃ lam t : Fin M → ℝ, ∀ j,
    lam j ≠ 0 ∧ |lam j| < 1 ∧ ∀ x ∈ I, g (F j x) = lam j * g x + t j

/-- The infinite word `w w w ⋯` for a nonempty finite word `w`. -/
def periodic {N m : ℕ} (hm : 0 < m) (w : Fin m → Fin N) : ℕ → Fin N :=
  fun n => w ⟨n % m, Nat.mod_lt n hm⟩

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- The maps `x ↦ f_i(x)` of `Φ` on the real line. -/
noncomputable def realMaps : Fin N → ℝ → ℝ := fun i x => (Φ.f i x).re

/-- `Φ` is sub-conjugated to a self-similar IFS: for distinct words `i, j` of the same length,
the pair `(f_i, f_j)` is conjugated to a self-similar IFS. -/
def SubConjSelfSimilar : Prop :=
  ∃ (m : ℕ) (i j : Fin m → Fin N), i ≠ j ∧
    ConjSelfSimilar ![fun x : ℝ => (Φ.comp (List.ofFn i) x).re,
      fun x : ℝ => (Φ.comp (List.ofFn j) x).re]

/-- `F_w = F_{w₁} ∘ ⋯ ∘ F_{w_k}` acting on functions on `B_ε`. -/
noncomputable def dualCompOn (w : List (Fin N)) : (nbhd ε →ᵤ ℂ) → nbhd ε →ᵤ ℂ :=
  w.foldr (fun i G => Φ.dualOpU i ∘ G) id

end IFS

end AnalyticESC
