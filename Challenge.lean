module

public import Mathlib

@[expose] public section

/-!
# Exponential separation of analytic self-conformal sets on the real line

Headline statements from B. Bárány, I. Kolossváry and S. Troscheit, *On exponential separation
of analytic self-conformal sets on the real line*. Theorem and equation numbers refer to the
manuscript.

A map of the IFS is given by its holomorphic extension `f : ℂ → ℂ`; on `[0,1]` it is real, and its
complex derivatives at real points are the derivatives of its real restriction. Finite words are
lists, read from the left: `f_{i₁ ⋯ iₙ} = f_{i₁} ∘ ⋯ ∘ f_{iₙ}`.
-/

namespace Challenge

open Set Metric

/-- The unit interval `I = [0,1]`. -/
abbrev I : Set ℝ := Icc 0 1

/-- The open `δ`-neighbourhood `B_δ = {z ∈ ℂ : ∃ x ∈ I, |z - x| < δ}` of `I` in `ℂ`. -/
def nbhd (δ : ℝ) : Set ℂ := thickening δ (((↑) : ℝ → ℂ) '' I)

/-- The class `S^ω_ε(I)` of Section 1.1, for a map given by its holomorphic extension:
(A) `f` is complex analytic on `B_{2ε}` and real at the real points of `B_{2ε}`;
(B) `f(I) ⊆ I` and `f(cl B_ε) ⊆ B_ε`; (C) `0 < |f'(z)| < 1` for `z ∈ cl B_ε`. -/
structure InClass (ε : ℝ) (f : ℂ → ℂ) : Prop where
  differentiableOn : DifferentiableOn ℂ f (nbhd (2 * ε))
  im_eq_zero : ∀ x : ℝ, (x : ℂ) ∈ nbhd (2 * ε) → (f x).im = 0
  re_mem_I : ∀ x ∈ I, (f x).re ∈ I
  mapsTo : MapsTo f (closure (nbhd ε)) (nbhd ε)
  deriv_ne_zero : ∀ z ∈ closure (nbhd ε), deriv f z ≠ 0
  norm_deriv_lt_one : ∀ z ∈ closure (nbhd ε), ‖deriv f z‖ < 1

variable {N : ℕ}

/-- `f_w = f_{w₁} ∘ ⋯ ∘ f_{w_k}` for a finite word `w`, with `f_∅ = id`. -/
def comp (f : Fin N → ℂ → ℂ) (w : List (Fin N)) : ℂ → ℂ := w.foldr (fun i g => f i ∘ g) id

/-- `sup_{x ∈ [0,1]} |f_i(x) - f_j(x)|` for finite words `i` and `j`. -/
noncomputable def supDist (f : Fin N → ℂ → ℂ) (i j : List (Fin N)) : ℝ :=
  ⨆ x : I, ‖comp f i ((x : ℝ) : ℂ) - comp f j ((x : ℝ) : ℂ)‖

/-- The strong exponential separation condition (Definition 1.2): there is `c > 0` with
`sup_{x ∈ [0,1]} |f_i(x) - f_j(x)| ≥ c^n` for all distinct `i, j ∈ Σ_n` and all `n`. -/
def SESC (f : Fin N → ℂ → ℂ) : Prop :=
  ∃ c > 0, ∀ n, ∀ i j : Fin n → Fin N, i ≠ j → c ^ n ≤ supDist f (List.ofFn i) (List.ofFn j)

/-- The distortion `f''/f'`. -/
noncomputable def nonlin (g : ℂ → ℂ) (z : ℂ) : ℂ := deriv (deriv g) z / deriv g z

/-- The dual natural projection `H_w` of (1.4) for a finite word `w`. The term with index `n`
(from `0`) is `(f_i''/f_i')(f_{v^←}(z)) · f_{v^←}'(z)`, where `v` is the prefix of the first `n`
letters, `i` the next letter and `f_{v^←} = f_{v_n} ∘ ⋯ ∘ f_{v_1}`. -/
noncomputable def dualProjFin (f : Fin N → ℂ → ℂ) (w : List (Fin N)) (z : ℂ) : ℂ :=
  ∑' n, match w[n]? with
    | none => 0
    | some i => nonlin (f i) (comp f (w.take n).reverse z) * deriv (comp f (w.take n).reverse) z

/-- The dual natural projection `H_w` of (1.4) for an infinite word `w`. -/
noncomputable def dualProjInf (f : Fin N → ℂ → ℂ) (w : ℕ → Fin N) (z : ℂ) : ℂ :=
  ∑' n, nonlin (f (w n)) (comp f (List.ofFn fun k : Fin n => w k).reverse z) *
    deriv (comp f (List.ofFn fun k : Fin n => w k).reverse) z

/-- The constant `c_max` of (1.7): the supremum of `|f_i'|` over `cl B_ε` and `i`. -/
noncomputable def cmax (ε : ℝ) (f : Fin N → ℂ → ℂ) : ℝ :=
  ⨆ (i : Fin N) (z : closure (nbhd ε)), ‖deriv (f i) z‖

/-- `β = sup_{x ∈ [0,1], i} |f_i''/f_i'(x)|` (Proposition 1.8). -/
noncomputable def beta (f : Fin N → ℂ → ℂ) : ℝ := ⨆ (x : I) (i : Fin N), ‖nonlin (f i) ((x : ℝ) : ℂ)‖

/-- The maps `f₁(x) = x/8`, `f₂(x) = x/8 + x²/32`, `f₃(x) = x/16 + x²/32 + 29/32` of the example in
Section 1.2.2. -/
noncomputable def exampleMaps : Fin 3 → ℂ → ℂ :=
  ![fun z => z / 8, fun z => z / 8 + z ^ 2 / 32, fun z => z / 16 + z ^ 2 / 32 + 29 / 32]

/-- The natural projection `π(w) = lim_{n → ∞} f_{w₁ ⋯ wₙ}(0)` of (1.3). -/
noncomputable def natProj (f : Fin N → ℂ → ℂ) (w : ℕ → Fin N) : ℝ :=
  Filter.limUnder Filter.atTop fun n => (comp f (List.ofFn fun k : Fin n => w k) 0).re

/-- The attractor `Λ = π(Σ)`. -/
def attractor (f : Fin N → ℂ → ℂ) : Set ℝ := range (natProj f)

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
def periodic {m : ℕ} (hm : 0 < m) (w : Fin m → Fin N) : ℕ → Fin N :=
  fun n => w ⟨n % m, Nat.mod_lt n hm⟩

/-- Theorem 1.5. Let `Φ = (f_i)_{i ∈ Fin N}` be an analytic IFS in `𝔖_N`. If
`sup_{x ∈ [0,1]} |H_i(x) - H_j(x)| > 0` for all distinct `i, j ∈ Σ ∪ Σ_*` with `|i| = |j|`, then `Φ`
satisfies the strong exponential separation condition. Words of equal length are either both
finite of the same length or both infinite. -/
theorem audit_sesc_of_dualProj {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ)
    (hf : ∀ i, InClass ε (f i))
    (hfin : ∀ n, ∀ i j : Fin n → Fin N, i ≠ j →
      0 < ⨆ x : I, ‖dualProjFin f (List.ofFn i) ((x : ℝ) : ℂ) -
        dualProjFin f (List.ofFn j) ((x : ℝ) : ℂ)‖)
    (hinf : ∀ i j : ℕ → Fin N, i ≠ j →
      0 < ⨆ x : I, ‖dualProjInf f i ((x : ℝ) : ℂ) - dualProjInf f j ((x : ℝ) : ℂ)‖) :
    SESC f := by
  sorry

/-- Proposition 1.8. Let `Φ = (f_i)_{i ∈ Fin N}` be an analytic IFS in `𝔖_N` with `N ≥ 2` maps.
Suppose that there is `α > 0` such that for all `i ≠ j` there is `x ∈ [0,1]` with
`|f_i''/f_i'(x) - f_j''/f_j'(x)| ≥ α`. Then `β > 0`, and if `α > 2β c_max/(1 - c_max)`, then
`sup_{x ∈ [0,1]} |H_i(x) - H_j(x)| > 0` for all distinct `i, j ∈ Σ ∪ Σ_*` with `|i| = |j|`, and `Φ`
satisfies the strong exponential separation condition. -/
theorem audit_example_criterion {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ)
    (hf : ∀ i, InClass ε (f i)) (hN : 2 ≤ N) {α : ℝ} (hα : 0 < α)
    (hsep : ∀ i j : Fin N, i ≠ j → ∃ x ∈ I, α ≤ ‖nonlin (f i) x - nonlin (f j) x‖) :
    0 < beta f ∧ (2 * beta f * cmax ε f / (1 - cmax ε f) < α →
      (∀ n, ∀ i j : Fin n → Fin N, i ≠ j →
        0 < ⨆ x : I, ‖dualProjFin f (List.ofFn i) ((x : ℝ) : ℂ) -
          dualProjFin f (List.ofFn j) ((x : ℝ) : ℂ)‖) ∧
      (∀ i j : ℕ → Fin N, i ≠ j →
        0 < ⨆ x : I, ‖dualProjInf f i ((x : ℝ) : ℂ) - dualProjInf f j ((x : ℝ) : ℂ)‖) ∧
      SESC f) := by
  sorry

/-- The example of Section 1.2.2: the system `x/8`, `x/8 + x²/32`, `x/16 + x²/32 + 29/32` lies in
`𝔖_3` for some `ε > 0` and satisfies the strong exponential separation condition. -/
theorem audit_example_sesc : ∃ ε > 0, (∀ i, InClass ε (exampleMaps i)) ∧ SESC exampleMaps := by
  sorry

/-- Theorem 1.12, first claim: an analytic IFS is conjugated, by an analytic map with nonvanishing
derivative, to an analytic IFS in which the map corresponding to `f_i` is a similarity. -/
theorem audit_conj_similarity {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ)
    (hf : ∀ i, InClass ε (f i)) (i : Fin N) :
    ∃ g, IsAnalyticCoord g ∧ (∀ x ∈ I, deriv g x ≠ 0) ∧
      ∃ lam t : ℝ, lam ≠ 0 ∧ |lam| < 1 ∧ ∀ x ∈ I, g (f i x).re = lam * g x + t := by
  sorry

/-- Theorem 1.12 (a). If the attractor of `Φ` is not a singleton, then `Φ` is conjugated to a
self-similar IFS if and only if `H_i ≡ H_j` on `[0,1]` for all `i, j ∈ Σ`. -/
theorem audit_conj_iff {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i))
    (hnd : ¬ ∃ x, attractor f = {x}) :
    ConjSelfSimilar (fun i (x : ℝ) => (f i x).re) ↔
      ∀ i j : ℕ → Fin N, ∀ x ∈ I, dualProjInf f i x = dualProjInf f j x := by
  sorry

/-- Theorem 1.12 (b). If the attractor of `Φ` is not a singleton, then `Φ` is sub-conjugated to a
self-similar IFS, that is, `(f_i, f_j)` is conjugated to a self-similar IFS for some distinct
`i, j ∈ Σ_*` of the same length, if and only if `H_{(i)^∞} ≡ H_{(j)^∞}` on `[0,1]` for some distinct
`i, j ∈ Σ_*` of the same length. -/
theorem audit_subconj_iff {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i))
    (hnd : ¬ ∃ x, attractor f = {x}) :
    (∃ (m : ℕ) (i j : Fin m → Fin N), i ≠ j ∧
      ConjSelfSimilar ![fun x : ℝ => (comp f (List.ofFn i) x).re,
        fun x : ℝ => (comp f (List.ofFn j) x).re]) ↔
      ∃ (m : ℕ) (hm : 0 < m) (i j : Fin m → Fin N), i ≠ j ∧
        ∀ x ∈ I, dualProjInf f (periodic hm i) x = dualProjInf f (periodic hm j) x := by
  sorry

end Challenge
