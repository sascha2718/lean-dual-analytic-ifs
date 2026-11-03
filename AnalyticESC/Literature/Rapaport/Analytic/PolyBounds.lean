module

public import AnalyticESC.Literature.Rapaport.Analytic.Dyadic

@[expose] public section

/-!
# Elementary bounds for polynomials on the unit interval

Bounds for `q ∈ 𝒫_k` with coefficients bounded by `B`, on `[-1, 1]` or on `I = [0, 1]`: the value,
the Lipschitz constant, the derivative and the first-order Taylor remainder. They are the
elementary estimates behind the linearisation (Lemma 3.9) and Lemma 3.10 of A. Rapaport,
*Dimension of self-conformal measures associated to an exponentially separated analytic IFS on
ℝ*, arXiv:2412.16753v2.

## Main declarations

* `abs_eval_le`, `abs_eval_sub_le`, `abs_derivEval_le_of_coeff`, `abs_derivEval_sub_le`.
* `abs_eval_sub_sub_le`: `|q(y) - q(x) - q'(x) (y - x)| ≤ (k + 1) k² B |y - x|²` on `I`.
* `abs_derivEval_le`: `|q'(x)| ≤ k (k + 1) ‖q‖` on `I`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.PolyBounds`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic

open MeasureTheory Set

variable {k : ℕ}

/-- Points of `I` have absolute value at most `1`. -/
theorem abs_le_one_of_mem_I {x : ℝ} (hx : x ∈ AnalyticESC.I) : |x| ≤ 1 :=
  abs_le.2 ⟨by linarith [hx.1], hx.2⟩

/-- `|y^j - x^j| ≤ j |y - x|` on `[-1, 1]`. -/
theorem abs_pow_sub_pow_le_of_abs_le_one {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (j : ℕ) :
    |y ^ j - x ^ j| ≤ j * |y - x| := by
  have h := abs_pow_sub_pow_le (a := y) (b := x) (n := j)
  have hmax : max |y| |x| ^ (j - 1) ≤ 1 :=
    pow_le_one₀ (le_max_of_le_left (abs_nonneg _)) (max_le hy hx)
  calc |y ^ j - x ^ j| ≤ |y - x| * j * max |y| |x| ^ (j - 1) := h
    _ ≤ |y - x| * j * 1 := by gcongr
    _ = j * |y - x| := by ring

/-- `|q(y)| ≤ (k + 1) B` for coefficients bounded by `B` and `|y| ≤ 1`. -/
theorem abs_eval_le (q : Poly k) {B : ℝ} (hq : ∀ j, |q j| ≤ B) {y : ℝ} (hy : |y| ≤ 1) :
    |Poly.eval q y| ≤ (k + 1) * B := by
  unfold Poly.eval
  calc |∑ j, q j * y ^ (j : ℕ)| ≤ ∑ j, |q j * y ^ (j : ℕ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin (k + 1), B := Finset.sum_le_sum fun j _ => by
        rw [abs_mul, abs_pow]
        have h1 : |y| ^ (j : ℕ) ≤ 1 := pow_le_one₀ (abs_nonneg _) hy
        have h2 := hq j
        have h3 : 0 ≤ |q j| := abs_nonneg _
        nlinarith [pow_nonneg (abs_nonneg y) (j : ℕ)]
    _ = (k + 1) * B := by simp

/-- `|q(y) - q(x)| ≤ (k + 1) k B |y - x|` on `[-1, 1]`. -/
theorem abs_eval_sub_le (q : Poly k) {B : ℝ} (hq : ∀ j, |q j| ≤ B) {x y : ℝ} (hx : |x| ≤ 1)
    (hy : |y| ≤ 1) : |Poly.eval q y - Poly.eval q x| ≤ (k + 1) * (k * B) * |y - x| := by
  unfold Poly.eval
  rw [← Finset.sum_sub_distrib]
  have hB : 0 ≤ B := (abs_nonneg _).trans (hq 0)
  calc |∑ j, (q j * y ^ (j : ℕ) - q j * x ^ (j : ℕ))|
      ≤ ∑ j, |q j * y ^ (j : ℕ) - q j * x ^ (j : ℕ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin (k + 1), k * B * |y - x| := Finset.sum_le_sum fun j _ => by
        rw [← mul_sub, abs_mul]
        have h1 := abs_pow_sub_pow_le_of_abs_le_one hx hy j
        have h2 := hq j
        have hj : (j : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.1 j.isLt
        calc |q j| * |y ^ (j : ℕ) - x ^ (j : ℕ)| ≤ B * (j * |y - x|) :=
              mul_le_mul h2 h1 (abs_nonneg _) hB
          _ ≤ B * (k * |y - x|) := by gcongr
          _ = k * B * |y - x| := by ring
    _ = (k + 1) * (k * B) * |y - x| := by simp; ring

/-- `|q'(x)| ≤ (k + 1) k B` for coefficients bounded by `B` and `|x| ≤ 1`. -/
theorem abs_derivEval_le_of_coeff (q : Poly k) {B : ℝ} (hq : ∀ j, |q j| ≤ B) {x : ℝ}
    (hx : |x| ≤ 1) : |Poly.derivEval q x| ≤ (k + 1) * (k * B) := by
  unfold Poly.derivEval
  have hB : 0 ≤ B := (abs_nonneg _).trans (hq 0)
  calc |∑ j : Fin (k + 1), q j * ((j : ℕ) * x ^ ((j : ℕ) - 1))|
      ≤ ∑ j : Fin (k + 1), |q j * ((j : ℕ) * x ^ ((j : ℕ) - 1))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin (k + 1), k * B := Finset.sum_le_sum fun j _ => by
        rw [abs_mul, abs_mul, abs_pow, Nat.abs_cast]
        have h1 : |x| ^ ((j : ℕ) - 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
        have hj : (j : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.1 j.isLt
        have h2 := hq j
        calc |q j| * ((j : ℝ) * |x| ^ ((j : ℕ) - 1)) ≤ B * (k * 1) := by
              gcongr
          _ = k * B := by ring
    _ = (k + 1) * (k * B) := by simp

/-- `|q'(x)| ≤ k (k + 1) ‖q‖` for `x ∈ I`. -/
theorem abs_derivEval_le (q : Poly k) {x : ℝ} (hx : x ∈ AnalyticESC.I) :
    |Poly.derivEval q x| ≤ k * (k + 1) * ‖q‖ := by
  have := abs_derivEval_le_of_coeff q (B := ‖q‖) (abs_apply_le_norm q)
    (abs_le_one_of_mem_I hx)
  linarith

/-- `|q'(y) - q'(x)| ≤ (k + 1) k² B |y - x|` on `[-1, 1]`. -/
theorem abs_derivEval_sub_le (q : Poly k) {B : ℝ} (hq : ∀ j, |q j| ≤ B) {x y : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |Poly.derivEval q y - Poly.derivEval q x| ≤ (k + 1) * (k * (k * B)) * |y - x| := by
  unfold Poly.derivEval
  rw [← Finset.sum_sub_distrib]
  have hB : 0 ≤ B := (abs_nonneg _).trans (hq 0)
  calc |∑ j : Fin (k + 1), (q j * ((j : ℕ) * y ^ ((j : ℕ) - 1)) -
        q j * ((j : ℕ) * x ^ ((j : ℕ) - 1)))|
      ≤ ∑ j : Fin (k + 1), |q j * ((j : ℕ) * y ^ ((j : ℕ) - 1)) -
        q j * ((j : ℕ) * x ^ ((j : ℕ) - 1))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin (k + 1), k * (k * B) * |y - x| := Finset.sum_le_sum fun j _ => by
        rw [← mul_sub, ← mul_sub, abs_mul, abs_mul, Nat.abs_cast]
        have h1 := abs_pow_sub_pow_le_of_abs_le_one hx hy ((j : ℕ) - 1)
        have hj : (j : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.1 j.isLt
        have hj1 : (((j : ℕ) - 1 : ℕ) : ℝ) ≤ k := by
          have : (j : ℕ) - 1 ≤ k := by omega
          exact_mod_cast this
        have h2 := hq j
        calc |q j| * ((j : ℝ) * |y ^ ((j : ℕ) - 1) - x ^ ((j : ℕ) - 1)|)
            ≤ B * (k * ((((j : ℕ) - 1 : ℕ) : ℝ) * |y - x|)) := by gcongr
          _ ≤ B * (k * (k * |y - x|)) := by gcongr
          _ = k * (k * B) * |y - x| := by ring
    _ = (k + 1) * (k * (k * B)) * |y - x| := by simp; ring

/-- The mean value theorem for `q ∈ 𝒫_k`. -/
theorem exists_eval_sub_eq (q : Poly k) {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Ioo a b, Poly.eval q b - Poly.eval q a = Poly.derivEval q t * (b - a) := by
  obtain ⟨t, ht, h⟩ := exists_hasDerivAt_eq_slope (Poly.eval q) (Poly.derivEval q) hab
    (Poly.continuous_eval q).continuousOn fun t _ => Poly.hasDerivAt_eval q t
  refine ⟨t, ht, ?_⟩
  rw [h]
  field_simp [sub_ne_zero.2 hab.ne']

/-- The first-order Taylor remainder on `I`: `|q(y) - q(x) - q'(x)(y - x)| ≤ C |y - x|²`. -/
theorem abs_eval_sub_sub_le (q : Poly k) {B : ℝ} (hq : ∀ j, |q j| ≤ B) {x y : ℝ}
    (hx : x ∈ AnalyticESC.I) (hy : y ∈ AnalyticESC.I) :
    |Poly.eval q y - Poly.eval q x - Poly.derivEval q x * (y - x)| ≤
      (k + 1) * (k * (k * B)) * |y - x| ^ 2 := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hq 0)
  have hC : 0 ≤ (k + 1) * (k * (k * B)) := by positivity
  have key : ∀ t, t ∈ AnalyticESC.I → |t - x| ≤ |y - x| →
      Poly.eval q y - Poly.eval q x = Poly.derivEval q t * (y - x) →
      |Poly.eval q y - Poly.eval q x - Poly.derivEval q x * (y - x)| ≤
        (k + 1) * (k * (k * B)) * |y - x| ^ 2 := by
    intro t ht htx he
    rw [he, ← sub_mul, abs_mul]
    have h1 := abs_derivEval_sub_le q hq (abs_le_one_of_mem_I hx) (abs_le_one_of_mem_I ht)
    calc |Poly.derivEval q t - Poly.derivEval q x| * |y - x|
        ≤ (k + 1) * (k * (k * B)) * |t - x| * |y - x| := by gcongr
      _ ≤ (k + 1) * (k * (k * B)) * |y - x| * |y - x| := by gcongr
      _ = (k + 1) * (k * (k * B)) * |y - x| ^ 2 := by ring
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · obtain ⟨t, ht, he⟩ := exists_eval_sub_eq q hxy
    refine key t ⟨hx.1.trans ht.1.le, ht.2.le.trans hy.2⟩ ?_ he
    rw [abs_of_pos (sub_pos.2 ht.1), abs_of_pos (sub_pos.2 hxy)]
    linarith [ht.2]
  · simp
  · obtain ⟨t, ht, he⟩ := exists_eval_sub_eq q hxy
    refine key t ⟨hy.1.trans ht.1.le, ht.2.le.trans hx.2⟩ ?_ (by linarith)
    rw [abs_of_neg (sub_neg.2 ht.2), abs_of_neg (sub_neg.2 hxy)]
    linarith [ht.1]

end FractalGeometry.Rapaport.Analytic
