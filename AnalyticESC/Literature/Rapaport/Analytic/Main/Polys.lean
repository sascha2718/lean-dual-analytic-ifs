module

public import AnalyticESC.Literature.Rapaport.Analytic.Dyadic

@[expose] public section

/-!
# The rescaled Taylor polynomials of Section 4

In the proof of Theorem 1.2 of A. Rapaport, *Dimension of self-conformal measures associated to
an exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2, Section 4, the Taylor
polynomial `P_{k,a} φ_v` is renormalised to
`S_{α r} T_{-x} R_{ψ⁻¹} P_{k,a} φ_v`, where `ψ(y) = r (y - a)` is an affine map. Its coefficients
are `α r (r⁻¹)^j φ_v^{(j)}(a) / j!`, shifted by `-α r x` in degree `0` (Rapaport's (4.9)). This
file defines the polynomial by its coefficients and proves the bounds on its norm and on its
derivative, and the separation of polynomials in the same dyadic cell.

## Main declarations

* `polyOf k α r a x f`: the renormalised Taylor polynomial.
* `eval_polyOf`: `q(ψ(y)) = α r (P_{k,a} f (y) - x)`.
* `norm_le_of_forall_abs_le`, `le_abs_derivEval_of_coeff`: norm and derivative bounds from
  coefficient bounds.
* `abs_eval_sub_lt_of_cellIdxVec_eq`: polynomials in the same level-`ℓ` cell are
  `(k+1) 2^{-ℓ}`-close on `[-1, 1]`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Main.Polys`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic.SectionFour

open MeasureTheory Set Filter Topology FractalGeometry.SelfConformal
open FractalGeometry.Rapaport.Analytic

variable {k : ℕ}

/-- The renormalised Taylor polynomial `S_{α r} T_{-x} R_{ψ⁻¹} P_{k,a} f` for `ψ(y) = r (y - a)`,
by its coefficients `α r ((r⁻¹)^j f^{(j)}(a) / j! - [j = 0] x)`. -/
noncomputable def polyOf (k : ℕ) (α r a x : ℝ) (f : ℝ → ℝ) : Poly k :=
  WithLp.toLp 2 fun j : Fin (k + 1) =>
    α * r * ((r⁻¹) ^ (j : ℕ) * (iteratedDeriv j f a / ((j : ℕ).factorial : ℝ)) -
      if (j : ℕ) = 0 then x else 0)

/-- The coefficients of `polyOf`. -/
theorem polyOf_apply (α r a x : ℝ) (f : ℝ → ℝ) (j : Fin (k + 1)) :
    polyOf k α r a x f j = α * r * ((r⁻¹) ^ (j : ℕ) *
      (iteratedDeriv j f a / ((j : ℕ).factorial : ℝ)) - if (j : ℕ) = 0 then x else 0) := rfl

/-- The constant coefficient: `α r (f(a) - x)`. -/
theorem polyOf_zero (α r a x : ℝ) (f : ℝ → ℝ) :
    polyOf k α r a x f 0 = α * r * (f a - x) := by
  simp [polyOf_apply]

/-- The coefficients of positive degree: `α r (r⁻¹)^j f^{(j)}(a) / j!`. -/
theorem polyOf_of_ne_zero (α r a x : ℝ) (f : ℝ → ℝ) {j : Fin (k + 1)} (hj : (j : ℕ) ≠ 0) :
    polyOf k α r a x f j =
      α * r * ((r⁻¹) ^ (j : ℕ) * (iteratedDeriv j f a / ((j : ℕ).factorial : ℝ))) := by
  simp [polyOf_apply, hj]

/-- `q(ψ(y)) = α r (P_{k,a} f (y) - x)` for `ψ(y) = r (y - a)`. -/
theorem eval_polyOf (α : ℝ) {r : ℝ} (hr : r ≠ 0) (a x : ℝ) (f : ℝ → ℝ) (y : ℝ) :
    Poly.eval (polyOf k α r a x f) (r * (y - a)) =
      α * r * (Poly.eval (Poly.taylor k a f) y - x) := by
  rw [Poly.eval, Poly.eval_taylor]
  have h : ∀ j : Fin (k + 1), polyOf k α r a x f j * (r * (y - a)) ^ (j : ℕ) =
      α * r * (iteratedDeriv j f a / ((j : ℕ).factorial : ℝ) * (y - a) ^ (j : ℕ)) -
        α * r * (if (j : ℕ) = 0 then x else 0) := by
    intro j
    rw [polyOf_apply, mul_pow]
    split_ifs with hj
    · rw [hj]
      simp only [pow_zero, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one,
        one_mul, mul_one]
      ring
    · have : (r⁻¹) ^ (j : ℕ) * r ^ (j : ℕ) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hr, one_pow]
      linear_combination (α * r * (iteratedDeriv j f a / ((j : ℕ).factorial : ℝ)) *
        (y - a) ^ (j : ℕ)) * this
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, mul_sub]
  congr 2
  rw [Fin.sum_univ_succ]
  simp

/-- The Euclidean norm of a coefficient vector is at most `k + 1` times a bound on its
coefficients. -/
theorem norm_le_of_forall_abs_le (q : Poly k) {B : ℝ} (hB : ∀ j, |q j| ≤ B) :
    ‖q‖ ≤ (k + 1) * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  rw [EuclideanSpace.norm_eq]
  rw [Real.sqrt_le_left (by positivity)]
  calc ∑ j, ‖q j‖ ^ 2 ≤ ∑ _j : Fin (k + 1), B ^ 2 := Finset.sum_le_sum fun j _ => by
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hB j) 2
    _ = (k + 1) * B ^ 2 := by simp
    _ ≤ ((k + 1) * B) ^ 2 := by
        have : (1 : ℝ) ≤ k + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
        nlinarith [sq_nonneg B]

/-- Lower bound on the derivative on `[-1, 1]` from the coefficients: if `|q_1| ≥ A` and
`|q_j| ≤ B` for `j ≥ 2`, then `|q'(z)| ≥ A - k (k+1) B` for `|z| ≤ 1`. -/
theorem le_abs_derivEval_of_coeff (hk : 1 ≤ k) (q : Poly k) {A B z : ℝ} (hB0 : 0 ≤ B)
    (hA : A ≤ |q ⟨1, by omega⟩|) (hB : ∀ j : Fin (k + 1), 2 ≤ (j : ℕ) → |q j| ≤ B)
    (hz : |z| ≤ 1) : A - k * (k + 1) * B ≤ |Poly.derivEval q z| := by
  set j₁ : Fin (k + 1) := ⟨1, by omega⟩ with hj₁
  set t : Fin (k + 1) → ℝ := fun j => q j * ((j : ℕ) * z ^ ((j : ℕ) - 1)) with ht
  have hsplit : Poly.derivEval q z = t j₁ + ∑ j ∈ Finset.univ.erase j₁, t j :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ j₁)).symm
  have ht1 : t j₁ = q j₁ := by simp [ht, hj₁]
  have hrest : ∀ j ∈ Finset.univ.erase j₁, |t j| ≤ k * B := by
    intro j hj
    have hjne : j ≠ j₁ := Finset.ne_of_mem_erase hj
    by_cases h0 : (j : ℕ) = 0
    · simp [ht, h0]
      positivity
    · have h2 : 2 ≤ (j : ℕ) := by
        have : (j : ℕ) ≠ 1 := fun h => hjne (Fin.ext h)
        omega
      have hjk : ((j : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.1 j.2
      rw [ht, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
      calc |q j| * (((j : ℕ) : ℝ) * |z| ^ ((j : ℕ) - 1)) ≤ B * (k * 1) := by
            refine mul_le_mul (hB j h2) (mul_le_mul hjk (pow_le_one₀ (abs_nonneg _) hz)
              (by positivity) (by positivity)) (by positivity) hB0
        _ = k * B := by ring
  have hsum : |∑ j ∈ Finset.univ.erase j₁, t j| ≤ k * (k + 1) * B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hrest).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ.erase j₁).card : ℝ) ≤ k + 1 := by
      have := Finset.card_erase_le (s := Finset.univ) (a := j₁)
      rw [Finset.card_univ, Fintype.card_fin] at this
      exact_mod_cast this
    have : 0 ≤ (k : ℝ) * B := by positivity
    nlinarith
  rw [hsplit, ht1]
  have := abs_add_le (q j₁ + ∑ j ∈ Finset.univ.erase j₁, t j) (-∑ j ∈ Finset.univ.erase j₁, t j)
  rw [add_neg_cancel_right, abs_neg] at this
  linarith

/-- Polynomials in the same level-`ℓ` dyadic cell of `𝒫_k` are `(k+1) 2^{-ℓ}`-close on
`[-1, 1]`. -/
theorem abs_eval_sub_lt_of_cellIdxVec_eq {ℓ : ℕ} {q q' : Poly k}
    (h : cellIdxVec ℓ q = cellIdxVec ℓ q') {z : ℝ} (hz : |z| ≤ 1) :
    |Poly.eval q z - Poly.eval q' z| < (k + 1) / 2 ^ ℓ := by
  have hj : ∀ j, |q j - q' j| < 1 / 2 ^ ℓ := fun j =>
    abs_sub_lt_of_cellIdx_eq (congrFun h j)
  rw [Poly.eval, Poly.eval, ← Finset.sum_sub_distrib]
  calc |∑ j, (q j * z ^ (j : ℕ) - q' j * z ^ (j : ℕ))|
      ≤ ∑ j, |q j * z ^ (j : ℕ) - q' j * z ^ (j : ℕ)| := Finset.abs_sum_le_sum_abs _ _
    _ < ∑ _j : Fin (k + 1), 1 / 2 ^ ℓ := by
        refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun j _ => ?_
        rw [← sub_mul, abs_mul, abs_pow]
        calc |q j - q' j| * |z| ^ (j : ℕ) ≤ |q j - q' j| * 1 :=
              mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) hz) (abs_nonneg _)
          _ < 1 / 2 ^ ℓ := by rw [mul_one]; exact hj j
    _ = (k + 1) / 2 ^ ℓ := by simp [div_eq_mul_inv]

end FractalGeometry.Rapaport.Analytic.SectionFour
