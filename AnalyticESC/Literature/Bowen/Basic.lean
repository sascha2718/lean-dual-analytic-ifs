module

public import Mathlib

@[expose] public section

/-!
# Bowen's theorem on the one-sided full shift: basic vocabulary

This file sets up the symbolic vocabulary for a proof of

R. Bowen, *Equilibrium states and the ergodic theory of Anosov diffeomorphisms*, Lecture Notes in
Mathematics 470, Springer, 1975, Theorem 1.4,

on the one-sided full shift `ℕ → Fin N`. The proof is an adaptation of the two-sided proof in
`FractalGeometry.Pressure.ParityShift` to the full shift, where every word is admissible.

## Main declarations

* `FractalGeometry.Bowen.cyl x m`: the cylinder `{y | ∀ i < m, y i = x i}`.
* `FractalGeometry.Bowen.birkhoff φ n x`: the Birkhoff sum `∑_{k < n} φ(σ^k x)` for the left
  shift `σ`, in the form `∑ k ∈ range n, φ (fun i => x (i + k))`.
* `FractalGeometry.Bowen.HasExpVariation φ b α`: the variation of `φ` on cylinders of length `k`
  is at most `b α^k`.
* `FractalGeometry.Bowen.HasBoundedDistortion φ D`: Birkhoff sums of length `n` at two points
  that agree on the first `n` coordinates differ by at most `D`.
* `FractalGeometry.Bowen.HasExpVariation.hasBoundedDistortion`: exponential variation gives
  bounded distortion with constant `b (1 - α)⁻¹`.
* `FractalGeometry.Bowen.ext0 u`: the extension `u 0 0 0 ⋯` of a finite word `u`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Bowen.Basic`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Bowen

open Finset

variable {N : ℕ}

/-- The cylinder `[x₀ ⋯ x_{m-1}] = {y | ∀ i < m, y i = x i}` of length `m` around `x`. -/
def cyl (x : ℕ → Fin N) (m : ℕ) : Set (ℕ → Fin N) := {y | ∀ i < m, y i = x i}

/-- Membership in a cylinder. -/
theorem mem_cyl {x y : ℕ → Fin N} {m : ℕ} : y ∈ cyl x m ↔ ∀ i < m, y i = x i := Iff.rfl

/-- A point lies in each of its cylinders. -/
theorem self_mem_cyl (x : ℕ → Fin N) (m : ℕ) : x ∈ cyl x m := fun _ _ => rfl

/-- The cylinder of length `0` is the whole space. -/
theorem cyl_zero (x : ℕ → Fin N) : cyl x 0 = Set.univ := by
  ext y
  simp [cyl]

/-- The Birkhoff sum `S_n φ(x) = ∑_{k < n} φ(σ^k x)`, where `σ` is the left shift. -/
def birkhoff (φ : (ℕ → Fin N) → ℝ) (n : ℕ) (x : ℕ → Fin N) : ℝ :=
  ∑ k ∈ range n, φ (fun i => x (i + k))

/-- The Birkhoff sum of length `0` vanishes. -/
@[simp] theorem birkhoff_zero (φ : (ℕ → Fin N) → ℝ) (x : ℕ → Fin N) : birkhoff φ 0 x = 0 := by
  simp [birkhoff]

/-- Additivity of Birkhoff sums: `S_{m+n} φ(x) = S_m φ(x) + S_n φ(σ^m x)`. -/
theorem birkhoff_add (φ : (ℕ → Fin N) → ℝ) (m n : ℕ) (x : ℕ → Fin N) :
    birkhoff φ (m + n) x = birkhoff φ m x + birkhoff φ n (fun i => x (i + m)) := by
  unfold birkhoff
  rw [sum_range_add]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  congr 1
  funext i
  congr 1
  omega

/-- The variation of `φ` on cylinders of length `k` is at most `b α^k`. -/
def HasExpVariation (φ : (ℕ → Fin N) → ℝ) (b α : ℝ) : Prop :=
  ∀ (k : ℕ) (x y : ℕ → Fin N), (∀ i < k, x i = y i) → |φ x - φ y| ≤ b * α ^ k

/-- Bounded distortion: Birkhoff sums of length `n` at two points that agree on the first `n`
coordinates differ by at most `D`. -/
def HasBoundedDistortion (φ : (ℕ → Fin N) → ℝ) (D : ℝ) : Prop :=
  ∀ (n : ℕ) (x y : ℕ → Fin N), (∀ i < n, x i = y i) → |birkhoff φ n x - birkhoff φ n y| ≤ D

/-- A geometric sum is at most `(1 - α)⁻¹`. -/
theorem sum_pow_le_inv {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (n : ℕ) :
    ∑ j ∈ range n, α ^ j ≤ (1 - α)⁻¹ := by
  have hpos : 0 < 1 - α := by linarith
  have hg := geom_sum_mul α n
  rw [← one_div, le_div_iff₀ hpos]
  nlinarith [pow_nonneg h0 n]

/-- Exponential variation implies bounded distortion with constant `b (1 - α)⁻¹`: the `k`-th
terms of the two Birkhoff sums are evaluated at points that agree on `n - k` coordinates. -/
theorem HasExpVariation.hasBoundedDistortion {φ : (ℕ → Fin N) → ℝ} {b α : ℝ}
    (h : HasExpVariation φ b α) (hb : 0 ≤ b) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    HasBoundedDistortion φ (b * (1 - α)⁻¹) := by
  intro n x y hxy
  unfold birkhoff
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ k ∈ range n,
      |φ (fun i => x (i + k)) - φ (fun i => y (i + k))| ≤ b * α ^ (n - 1 - k) := by
    intro k hk
    have hk' := mem_range.1 hk
    exact h (n - 1 - k) _ _ fun i hi => hxy (i + k) (by omega)
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  have hrefl : ∑ j ∈ range n, α ^ (n - 1 - j) = ∑ j ∈ range n, α ^ j :=
    sum_range_reflect (fun j => α ^ j) n
  rw [hrefl]
  exact mul_le_mul_of_nonneg_left (sum_pow_le_inv hα0 hα1 n) hb

/-- The distortion constant is nonnegative as soon as the space is nonempty. -/
theorem HasBoundedDistortion.nonneg {φ : (ℕ → Fin N) → ℝ} {D : ℝ} (h : HasBoundedDistortion φ D)
    (x : ℕ → Fin N) : 0 ≤ D := by
  simpa using h 0 x x fun _ hi => absurd hi (Nat.not_lt_zero _)

section Extension

variable [NeZero N]

/-- The extension `u 0 0 0 ⋯` of a finite word `u` by the symbol `0`. -/
def ext0 {n : ℕ} (u : Fin n → Fin N) : ℕ → Fin N := fun i => if h : i < n then u ⟨i, h⟩ else 0

/-- The extension of `u` agrees with `u` on the first `n` coordinates. -/
theorem ext0_of_lt {n : ℕ} (u : Fin n → Fin N) {i : ℕ} (h : i < n) : ext0 u i = u ⟨i, h⟩ :=
  dite_eq_left h

/-- The extension of `u` agrees with `u` on `Fin n`. -/
theorem ext0_fin {n : ℕ} (u : Fin n → Fin N) (i : Fin n) : ext0 u i = u i := ext0_of_lt u i.2

/-- Restricting the extension of `u` to `Fin n` gives back `u`. -/
theorem restrict_ext0 {n : ℕ} (u : Fin n → Fin N) : (fun i : Fin n => ext0 u i) = u :=
  funext (ext0_fin u)

/-- The extension of a concatenation `v w` agrees with `v` on the first `m` coordinates. -/
theorem ext0_append_of_lt {m k : ℕ} (v : Fin m → Fin N) (w : Fin k → Fin N) {i : ℕ}
    (hi : i < m) : ext0 (Fin.append v w) i = v ⟨i, hi⟩ := by
  rw [ext0_of_lt _ (by omega : i < m + k)]
  exact Fin.append_left v w ⟨i, hi⟩

/-- Shifting the extension of a concatenation `v w` by the length of `v` gives the extension
of `w`. -/
theorem ext0_append_shift {m k : ℕ} (v : Fin m → Fin N) (w : Fin k → Fin N) :
    (fun i => ext0 (Fin.append v w) (i + m)) = ext0 w := by
  funext i
  by_cases hi : i < k
  · rw [ext0_of_lt _ (by omega : i + m < m + k), ext0_of_lt _ hi]
    have e : (⟨i + m, by omega⟩ : Fin (m + k)) = Fin.natAdd m ⟨i, hi⟩ := by
      ext
      simp [add_comm]
    rw [e, Fin.append_right]
  · rw [ext0, dite_eq_right (by omega), ext0, dite_eq_right hi]

/-- The extension of `v w` lies in the cylinder of length `m` around `x` if and only if `v` is
the word `x₀ ⋯ x_{m-1}`. -/
theorem ext0_append_mem_cyl_iff {m k : ℕ} (x : ℕ → Fin N) (v : Fin m → Fin N)
    (w : Fin k → Fin N) : ext0 (Fin.append v w) ∈ cyl x m ↔ v = fun i : Fin m => x i := by
  constructor
  · intro h
    funext i
    rw [← ext0_append_of_lt v w i.2]
    exact h i i.2
  · rintro rfl i hi
    exact ext0_append_of_lt _ w hi

end Extension

end FractalGeometry.Bowen
