module

public import Mathlib

@[expose] public section

/-!
# Definitions

The vocabulary of B. Bárány, I. Kolossváry and S. Troscheit, *On exponential separation of
analytic self-conformal sets on the real line*.

Maps are given by their holomorphic extension `f : ℂ → ℂ`. Statements about `[0,1]` evaluate at
real points `(x : ℂ)`, `x ∈ I`; there `f`, `f'` and `f''` are real, and the complex derivatives
agree with the derivatives of the real restriction. Finite words are lists, read from the left:
`f_{i₁ ⋯ iₙ} = f_{i₁} ∘ ⋯ ∘ f_{iₙ}`.
-/

namespace AnalyticESC

open Set Metric Filter Topology
open scoped UniformConvergence

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

/-- An analytic IFS `Φ = (f_i)_{i ∈ Fin N}` in `𝔖_N`, for a fixed `ε > 0`. -/
structure IFS (N : ℕ) (ε : ℝ) where
  /-- The maps of the system. -/
  f : Fin N → ℂ → ℂ
  ε_pos : 0 < ε
  inClass : ∀ i, InClass ε (f i)

/-- A finite or infinite word over the alphabet `Fin N`, an element of `Σ_* ∪ Σ`. -/
inductive Word (N : ℕ) where
  | fin (w : List (Fin N))
  | inf (w : ℕ → Fin N)

namespace Word

variable {N : ℕ}

/-- The length `|w| ∈ ℕ ∪ {∞}`. -/
def length : Word N → ℕ∞
  | fin w => w.length
  | inf _ => ⊤

/-- The letter in position `n` (counted from `0`), if `n < |w|`. -/
def get? : Word N → ℕ → Option (Fin N)
  | fin w, n => w[n]?
  | inf w, n => some (w n)

/-- The prefix of the first `n` letters (the whole word if `|w| ≤ n`). -/
def take : Word N → ℕ → List (Fin N)
  | fin w, n => w.take n
  | inf w, n => List.ofFn fun k : Fin n => w k

/-- The word `a w` obtained by placing the finite word `a` in front of `w`. -/
def prepend (a : List (Fin N)) : Word N → Word N
  | fin w => fin (a ++ w)
  | inf w => inf fun n => if h : n < a.length then a[n] else w (n - a.length)

/-- `|i ∧ j|`: the length of the longest common prefix of `i` and `j` (`⊤` if `i = j` is
infinite). -/
noncomputable def commonPrefixLength (i j : Word N) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : ∀ k < n, (i.get? k).isSome ∧ i.get? k = j.get? k), (n : ℕ∞)

end Word

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- `f_w = f_{w₁} ∘ ⋯ ∘ f_{w_k}` for a finite word `w`, with `f_∅ = id`. -/
def comp (w : List (Fin N)) : ℂ → ℂ := w.foldr (fun i g => Φ.f i ∘ g) id

/-- `sup_{x ∈ [0,1]} |f_i(x) - f_j(x)|` for finite words `i` and `j`. -/
noncomputable def supDist (i j : List (Fin N)) : ℝ :=
  ⨆ x : I, ‖Φ.comp i ((x : ℝ) : ℂ) - Φ.comp j ((x : ℝ) : ℂ)‖

/-- The exponential separation condition (ESC): there is `c > 0` with
`sup_{x ∈ [0,1]} |f_i(x) - f_j(x)| ≥ c^n` for all distinct `i, j ∈ Σ_n`, for infinitely many
`n`. -/
def ESC : Prop :=
  ∃ c > 0, ∃ᶠ n in atTop, ∀ i j : Fin n → Fin N, i ≠ j →
    c ^ n ≤ Φ.supDist (List.ofFn i) (List.ofFn j)

/-- The strong exponential separation condition (SESC, Definition 1.2). -/
def SESC : Prop :=
  ∃ c > 0, ∀ n, ∀ i j : Fin n → Fin N, i ≠ j → c ^ n ≤ Φ.supDist (List.ofFn i) (List.ofFn j)

/-- Weak super-exponential condensation (Definition 1.2): a positive sequence `η` with
`log(η_n)/n → -∞`, a subsequence `n_ℓ` and distinct `i, j ∈ Σ_{n_ℓ}` with
`sup_{x ∈ [0,1]} |f_i(x) - f_j(x)| ≤ η_{n_ℓ}`. -/
def WeakSuperExpCondensation : Prop :=
  ∃ η : ℕ → ℝ, (∀ n, 0 < η n) ∧ Tendsto (fun n => Real.log (η n) / n) atTop atBot ∧
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ ℓ, ∃ i j : Fin (φ ℓ) → Fin N, i ≠ j ∧
      Φ.supDist (List.ofFn i) (List.ofFn j) ≤ η (φ ℓ)

/-- The natural projection `π(w) = lim_{n → ∞} f_{w₁ ⋯ wₙ}(0)` of (1.3). -/
noncomputable def natProj (w : ℕ → Fin N) : ℝ :=
  limUnder atTop fun n => (Φ.comp (List.ofFn fun k : Fin n => w k) 0).re

/-- The attractor `Λ = π(Σ)`. -/
def attractor : Set ℝ := range Φ.natProj

/-- `Φ` has exact overlaps: `f_i = f_j` on `Λ` for distinct finite words `i` and `j`. -/
def HasExactOverlaps : Prop :=
  ∃ i j : List (Fin N), i ≠ j ∧ ∀ x ∈ Φ.attractor, Φ.comp i (x : ℂ) = Φ.comp j (x : ℂ)

/-- Compositions along distinct finite words differ somewhere on `[0,1]`: `f_i ≢ f_j` on `[0,1]`
for all distinct `i, j ∈ Σ_*` (the hypothesis of Lemma 4.1). -/
def NoCoincidence : Prop :=
  ∀ i j : List (Fin N), i ≠ j → ∃ x ∈ I, Φ.comp i (x : ℂ) ≠ Φ.comp j (x : ℂ)

/-- The constant `c_max` of (1.7): the supremum of `|f_i'|` over `cl B_ε` and `i`. -/
noncomputable def cmax : ℝ := ⨆ (i : Fin N) (z : closure (nbhd ε)), ‖deriv (Φ.f i) z‖

/-- The constant `c_min` of (1.7): the infimum of `|f_i'|` over `cl B_ε` and `i`. -/
noncomputable def cmin : ℝ := ⨅ (i : Fin N) (z : closure (nbhd ε)), ‖deriv (Φ.f i) z‖

/-- The distortion `f_i''/f_i'`. -/
noncomputable def nonlin (i : Fin N) (z : ℂ) : ℂ := deriv (deriv (Φ.f i)) z / deriv (Φ.f i) z

/-- The term with index `n` (from `0`) of the series (1.4) for `H_w`: with `v` the first `n`
letters of `w` and `i` the next one, `(f_i''/f_i')(f_{v^←}(z)) · f_{v^←}'(z)`, where
`f_{v^←} = f_{v_n} ∘ ⋯ ∘ f_{v_1}` is the composition in reverse order. Zero if `|w| ≤ n`. -/
noncomputable def dualTerm (w : Word N) (n : ℕ) (z : ℂ) : ℂ :=
  match w.get? n with
  | none => 0
  | some i => Φ.nonlin i (Φ.comp (w.take n).reverse z) * deriv (Φ.comp (w.take n).reverse) z

/-- The dual natural projection `H_w` of (1.4), for finite and infinite words. -/
noncomputable def dualProj (w : Word N) (z : ℂ) : ℂ := ∑' n, Φ.dualTerm w n z

/-- The dual operator `(F_i h)(z) = f_i'(z) · h(f_i(z)) + (f_i''/f_i')(z)` of (2.1). -/
noncomputable def dualOp (i : Fin N) (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv (Φ.f i) z * h (Φ.f i z) + Φ.nonlin i z

/-- `F_w = F_{w₁} ∘ ⋯ ∘ F_{w_k}` for a finite word `w`. -/
noncomputable def dualComp (w : List (Fin N)) : (ℂ → ℂ) → ℂ → ℂ :=
  w.foldr (fun i G => Φ.dualOp i ∘ G) id

end IFS

/-- The restriction of `h` to `B_ε`, in the space of functions on `B_ε` with the topology of
uniform convergence, that is, of the supremum norm over `B_ε`. -/
def toNbhd (ε : ℝ) (h : ℂ → ℂ) : nbhd ε →ᵤ ℂ := UniformFun.ofFun fun z => h z

/-- The space `C^ω_ε([0,1])` of Section 2.1: maps complex analytic on `B_ε` and real on `I`,
as functions on `B_ε`. -/
def analyticSpace (ε : ℝ) : Set (nbhd ε →ᵤ ℂ) :=
  {h | ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (nbhd ε) ∧ (∀ x ∈ I, (g x).im = 0) ∧ h = toNbhd ε g}

/-- The pairs `ℬ_n = {(i, j) ∈ Σ_n × Σ_n : i₁ < j₁}` of Section 4.1. -/
def pairs (N n : ℕ) : Set ((Fin n → Fin N) × (Fin n → Fin N)) :=
  {p | ∃ h : 0 < n, p.1 ⟨0, h⟩ < p.2 ⟨0, h⟩}

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- The dual operator `F_i` acting on functions on `B_ε`; `f_i` maps `B_ε` into itself. -/
noncomputable def dualOpU (i : Fin N) (h : nbhd ε →ᵤ ℂ) : nbhd ε →ᵤ ℂ :=
  UniformFun.ofFun fun z =>
    deriv (Φ.f i) z * UniformFun.toFun h ⟨Φ.f i z, (Φ.inClass i).mapsTo (subset_closure z.2)⟩ +
      Φ.nonlin i z

/-- `Λ` is an attractor of the dual IFS `Φ*` (Lemma 2.1): a nonempty compact subset of
`C^ω_ε([0,1])` with `Λ = ⋃_i F_i Λ`. -/
def IsDualAttractor (Λ : Set (nbhd ε →ᵤ ℂ)) : Prop :=
  Λ ⊆ analyticSpace ε ∧ Λ.Nonempty ∧ IsCompact Λ ∧ Λ = ⋃ i, Φ.dualOpU i '' Λ

/-- The dual IFS `Φ*` satisfies the strong separation condition: `F_i Λ* ∩ F_j Λ* = ∅` for
`i ≠ j`. -/
def DualSSC : Prop :=
  ∃ Λ, Φ.IsDualAttractor Λ ∧ ∀ i j, i ≠ j → Disjoint (Φ.dualOpU i '' Λ) (Φ.dualOpU j '' Λ)

/-- `conv((F_i k)(x), (F_i K)(x))` for a finite word `i` and constants `k`, `K`. -/
noncomputable def dualCylAt (k K : ℝ) (i : List (Fin N)) (x : ℝ) : Set ℝ :=
  uIcc (Φ.dualComp i (fun _ => (k : ℂ)) x).re (Φ.dualComp i (fun _ => (K : ℂ)) x).re

/-- The cylinders `F_i(k,K)` and `F_j(k,K)` are disjoint in the sense of (2.2). -/
def DualCylDisjoint (k K : ℝ) (i j : List (Fin N)) : Prop :=
  ∃ x ∈ I, Disjoint (Φ.dualCylAt k K i x) (Φ.dualCylAt k K j x)

/-- The orbit `𝒪_i(x) = (x, f_{i₁}(x), f_{i₂ i₁}(x), …, f_{i_{|i|} ⋯ i₁}(x))` of Section 4.1, as
a list of real points. -/
noncomputable def orbit (i : List (Fin N)) (x : ℝ) : List ℝ :=
  (List.range (i.length + 1)).map fun l => (Φ.comp (i.take l).reverse x).re

end IFS

/-- The `𝒞²` distance on `I` between two maps (Section 1.1), with derivatives at real points. -/
noncomputable def d2Map (f g : ℂ → ℂ) : ℝ :=
  (⨆ x : I, ‖f ((x : ℝ) : ℂ) - g ((x : ℝ) : ℂ)‖) +
    (⨆ x : I, ‖deriv f ((x : ℝ) : ℂ) - deriv g ((x : ℝ) : ℂ)‖) +
    (⨆ x : I, ‖deriv (deriv f) ((x : ℝ) : ℂ) - deriv (deriv g) ((x : ℝ) : ℂ)‖)

/-- The `𝒞²` distance `d₂(Φ, Ψ) = max_i d₂(f_i, g_i)` between two families of maps. -/
noncomputable def d2Sys {N : ℕ} (f g : Fin N → ℂ → ℂ) : ℝ := ⨆ i, d2Map (f i) (g i)

/-- The `𝒞²` distance `d₂(Φ, Ψ) = max_i d₂(f_i, g_i)` on `𝔖_N`. The two systems may lie in
`𝔖_N(ε)` for different `ε`. -/
noncomputable def d2 {N : ℕ} {ε ε' : ℝ} (Φ : IFS N ε) (Ψ : IFS N ε') : ℝ :=
  ⨆ i, d2Map (Φ.f i) (Ψ.f i)

/-- The space `𝔖_N` of Section 1.1: families of maps that all lie in `S^ω_ε(I)` for some
`ε > 0`, that is, in `S^ω(I) = ⋃_{ε > 0} S^ω_ε(I)`. -/
def InUnionClass {N : ℕ} (f : Fin N → ℂ → ℂ) : Prop := ∃ ε > 0, ∀ i, InClass ε (f i)

end AnalyticESC
