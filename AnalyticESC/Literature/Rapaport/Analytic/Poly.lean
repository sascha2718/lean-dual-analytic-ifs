module

public import AnalyticESC.Literature.SelfConformal.Vocabulary
public import Mathlib

@[expose] public section

/-!
# Spaces of polynomials and their action on measures of the line

The function spaces of Section 2.5 and the dyadic partitions of polynomial spaces of Section 2.8
of A. Rapaport, *Dimension of self-conformal measures associated to an exponentially separated
analytic IFS on ℝ*, arXiv:2412.16753v2.

A polynomial `q(X) = ∑_{j ≤ k} q_j X^j` of degree at most `k` is its coefficient vector in
`Poly k = EuclideanSpace ℝ (Fin (k + 1))`, so that `‖q‖` is Rapaport's `‖q‖₂` and the level-`n`
dyadic partition `𝒟_n^{𝒫_k}` is the coordinatewise dyadic partition of `ℝ^{k+1}`.

## Main declarations

* `Poly k`: polynomials of degree at most `k`, with the Euclidean norm on coefficients.
* `Poly.eval q x`, `Poly.derivEval q x`: the values `q(x)` and `q'(x)`.
* `Poly.toPolynomial`, `Poly.ofPolynomial`: the bridge to Mathlib's `Polynomial ℝ`.
* `Poly.scale c` and `Poly.translate w`: Rapaport's `S_c q = c q` and `T_w q = q + w`.
* `Poly.compAffine s t q = q(s X + t)`, and `Poly.reparamInv r t q = q ∘ ψ⁻¹` for the affine map
  `ψ x = r x + t` (Rapaport's `R_{ψ⁻¹}`).
* `Poly.taylorCoeff k a f` (coefficients `f^{(j)}(a) / j!`) and `Poly.taylor k a f`, Rapaport's
  Taylor polynomial `P_{k,a} f = ∑_j f^{(j)}(a) / j! (X - a)^j`.
* `cellIdxVec`, `cellVec`, `cellOfVec`: dyadic cells of `Poly k`; `dyadicEntropyVec ν n`, Rapaport's
  `H(ν, 𝒟_n^{𝒫_k})` in bits; `componentVec ν n q`, the component `ν_{q,n}`; `levelProbVec`.
* `act ν θ`, Rapaport's `ν.θ`, the image of `ν × θ` under `(q, x) ↦ q(x)`, and
  `actPoint ν x = ν.x`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Poly`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic

open MeasureTheory Set Filter Topology FractalGeometry.SelfConformal
open scoped ENNReal

/-- The space `𝒫_k` of real polynomials of degree at most `k`, identified with the coefficient
vectors `(q_0, …, q_k)`. Its norm is Rapaport's `‖q‖₂ = (∑_j q_j²)^{1/2}`. -/
abbrev Poly (k : ℕ) := EuclideanSpace ℝ (Fin (k + 1))

namespace Poly

variable {k : ℕ}

/-! ### Evaluation and derivative -/

/-- The value `q(x) = ∑_j q_j x^j` of the polynomial `q` at `x`. -/
noncomputable def eval (q : Poly k) (x : ℝ) : ℝ := ∑ j, q j * x ^ (j : ℕ)

/-- The value `q'(x) = ∑_j j q_j x^{j-1}` of the derivative of `q` at `x`. -/
noncomputable def derivEval (q : Poly k) (x : ℝ) : ℝ :=
  ∑ j : Fin (k + 1), q j * ((j : ℕ) * x ^ ((j : ℕ) - 1))

/-- The polynomial `∑_j q_j X^j` as an element of Mathlib's `Polynomial ℝ`. -/
noncomputable def toPolynomial (q : Poly k) : Polynomial ℝ :=
  ∑ j : Fin (k + 1), Polynomial.C (q j) * Polynomial.X ^ (j : ℕ)

/-- The coefficient vector `(P_0, …, P_k)` of a polynomial `P`, truncated at degree `k`. -/
noncomputable def ofPolynomial (k : ℕ) (P : Polynomial ℝ) : Poly k :=
  WithLp.toLp 2 fun j => P.coeff j

/-- The coefficients of `ofPolynomial k P`. -/
@[simp]
theorem ofPolynomial_apply (P : Polynomial ℝ) (j : Fin (k + 1)) :
    ofPolynomial k P j = P.coeff j := rfl

/-- The coefficients of `toPolynomial q`. -/
theorem coeff_toPolynomial (q : Poly k) (i : ℕ) :
    (toPolynomial q).coeff i = if h : i < k + 1 then q ⟨i, h⟩ else 0 := by
  classical
  simp only [toPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i, h⟩]
    · simp
    · intro b _ hb
      rw [ite_eq_right]
      intro hib
      exact absurd (Fin.ext hib.symm) hb
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [ite_eq_right]
    intro hij
    exact absurd (hij ▸ j.isLt) h

/-- The coefficients of `toPolynomial q` of degree at most `k`. -/
@[simp]
theorem coeff_toPolynomial_fin (q : Poly k) (j : Fin (k + 1)) :
    (toPolynomial q).coeff j = q j := by
  rw [coeff_toPolynomial, dite_eq_left j.isLt]

/-- `toPolynomial q` has degree at most `k`. -/
theorem natDegree_toPolynomial_le (q : Poly k) : (toPolynomial q).natDegree ≤ k := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [coeff_toPolynomial, dite_eq_right (by omega : ¬ i < k + 1)]

/-- `ofPolynomial` is a left inverse of `toPolynomial`. -/
@[simp]
theorem ofPolynomial_toPolynomial (q : Poly k) : ofPolynomial k (toPolynomial q) = q := by
  ext j
  simp

/-- `toPolynomial` is a left inverse of `ofPolynomial` on polynomials of degree at most `k`. -/
theorem toPolynomial_ofPolynomial {P : Polynomial ℝ} (hP : P.natDegree ≤ k) :
    toPolynomial (ofPolynomial k P) = P := by
  ext i
  rw [coeff_toPolynomial]
  split_ifs with h
  · simp
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    omega

/-- Evaluation agrees with the evaluation of `toPolynomial q`. -/
theorem eval_eq_eval_toPolynomial (q : Poly k) (x : ℝ) :
    eval q x = (toPolynomial q).eval x := by
  simp [eval, toPolynomial, Polynomial.eval_finsetSum]

/-- Evaluation of `ofPolynomial k P` for `P` of degree at most `k`. -/
theorem eval_ofPolynomial {P : Polynomial ℝ} (hP : P.natDegree ≤ k) (x : ℝ) :
    eval (ofPolynomial k P) x = P.eval x := by
  rw [eval_eq_eval_toPolynomial, toPolynomial_ofPolynomial hP]

/-- `q'(x)` is the evaluation of the derivative of `toPolynomial q`. -/
theorem derivEval_eq_eval_derivative (q : Poly k) (x : ℝ) :
    derivEval q x = (Polynomial.derivative (toPolynomial q)).eval x := by
  simp only [derivEval, toPolynomial, Polynomial.derivative_sum, Polynomial.eval_finsetSum,
    Polynomial.derivative_C_mul_X_pow, Polynomial.eval_C_mul, Polynomial.eval_pow,
    Polynomial.eval_X]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The derivative of `x ↦ q(x)` is `q'`. -/
theorem hasDerivAt_eval (q : Poly k) (x : ℝ) : HasDerivAt (eval q) (derivEval q x) x := by
  have h := (toPolynomial q).hasDerivAt x
  rw [derivEval_eq_eval_derivative]
  convert h using 1
  funext y
  exact eval_eq_eval_toPolynomial q y

/-- The derivative of `x ↦ q(x)` is `q'`. -/
theorem deriv_eval (q : Poly k) (x : ℝ) : deriv (eval q) x = derivEval q x :=
  (hasDerivAt_eval q x).deriv

/-- Polynomials are differentiable. -/
theorem differentiable_eval (q : Poly k) : Differentiable ℝ (eval q) :=
  fun x => (hasDerivAt_eval q x).differentiableAt

/-- Evaluation `(q, x) ↦ q(x)` is jointly continuous. -/
theorem continuous_eval_uncurry :
    Continuous fun z : Poly k × ℝ => eval z.1 z.2 := by
  unfold eval
  refine continuous_finsetSum _ fun j _ => ?_
  refine Continuous.mul ?_ (continuous_snd.pow _)
  exact (PiLp.continuous_apply 2 _ j).comp continuous_fst

/-- Polynomials are continuous. -/
theorem continuous_eval (q : Poly k) : Continuous (eval q) :=
  continuous_eval_uncurry.comp (Continuous.prodMk continuous_const continuous_id)

/-- Evaluation at a point is continuous on `𝒫_k`. -/
theorem continuous_eval_left (x : ℝ) : Continuous fun q : Poly k => eval q x :=
  continuous_eval_uncurry.comp (Continuous.prodMk continuous_id continuous_const)

/-- Evaluation `(q, x) ↦ q(x)` is measurable. -/
theorem measurable_eval_uncurry :
    Measurable fun z : Poly k × ℝ => eval z.1 z.2 :=
  continuous_eval_uncurry.measurable

/-- Evaluation at a point is measurable on `𝒫_k`. -/
theorem measurable_eval_left (x : ℝ) : Measurable fun q : Poly k => eval q x :=
  (continuous_eval_left x).measurable

/-- The zero polynomial vanishes. -/
@[simp]
theorem eval_zero (x : ℝ) : eval (0 : Poly k) x = 0 := by simp [eval]

/-- Evaluation is additive. -/
@[simp]
theorem eval_add (q r : Poly k) (x : ℝ) : eval (q + r) x = eval q x + eval r x := by
  simp [eval, add_mul, Finset.sum_add_distrib]

/-- Evaluation is homogeneous. -/
@[simp]
theorem eval_smul (c : ℝ) (q : Poly k) (x : ℝ) : eval (c • q) x = c * eval q x := by
  simp [eval, Finset.mul_sum, mul_assoc]

/-- Evaluation commutes with negation. -/
@[simp]
theorem eval_neg (q : Poly k) (x : ℝ) : eval (-q) x = -eval q x := by
  simp [eval]

/-- Evaluation commutes with subtraction. -/
@[simp]
theorem eval_sub (q r : Poly k) (x : ℝ) : eval (q - r) x = eval q x - eval r x := by
  simp [eval, sub_mul]

/-- The derivative is additive. -/
@[simp]
theorem derivEval_add (q r : Poly k) (x : ℝ) :
    derivEval (q + r) x = derivEval q x + derivEval r x := by
  simp [derivEval, add_mul, Finset.sum_add_distrib]

/-- The derivative is homogeneous. -/
@[simp]
theorem derivEval_smul (c : ℝ) (q : Poly k) (x : ℝ) :
    derivEval (c • q) x = c * derivEval q x := by
  simp [derivEval, Finset.mul_sum, mul_assoc]

/-- The derivative commutes with subtraction. -/
@[simp]
theorem derivEval_sub (q r : Poly k) (x : ℝ) :
    derivEval (q - r) x = derivEval q x - derivEval r x := by
  simp [derivEval, sub_mul]

/-- The evaluation map `q ↦ q(x)` as a continuous linear functional. -/
noncomputable def evalCLM (k : ℕ) (x : ℝ) : Poly k →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => eval q x
      map_add' := fun q r => eval_add q r x
      map_smul' := fun c q => eval_smul c q x }

/-- The value of `evalCLM`. -/
@[simp]
theorem evalCLM_apply (x : ℝ) (q : Poly k) : evalCLM k x q = eval q x := rfl

/-! ### Constants, scaling and translation -/

/-- The constant polynomial `1`, the first vector of the monomial basis. -/
noncomputable def one (k : ℕ) : Poly k := EuclideanSpace.single 0 1

/-- The constant polynomial `1` has value `1`. -/
@[simp]
theorem eval_one (x : ℝ) : eval (one k) x = 1 := by
  rw [eval, Finset.sum_eq_single 0]
  · simp [one]
  · intro j _ hj
    simp [one, hj]
  · simp

/-- The constant polynomial `1` has derivative `0`. -/
@[simp]
theorem derivEval_one (x : ℝ) : derivEval (one k) x = 0 := by
  rw [derivEval, Finset.sum_eq_zero]
  intro j _
  by_cases hj : j = 0
  · subst hj
    simp
  · simp [one, hj]

/-- Rapaport's scaling `S_c q = c q` on `𝒫_k`. -/
noncomputable def scale (c : ℝ) (q : Poly k) : Poly k := c • q

/-- Rapaport's translation `T_w q = q + w` on `𝒫_k`, which adds the constant `w`. -/
noncomputable def translate (w : ℝ) (q : Poly k) : Poly k := q + w • one k

/-- `(S_c q)(x) = c q(x)`. -/
@[simp]
theorem eval_scale (c : ℝ) (q : Poly k) (x : ℝ) : eval (scale c q) x = c * eval q x :=
  eval_smul c q x

/-- `(T_w q)(x) = q(x) + w`. -/
@[simp]
theorem eval_translate (w : ℝ) (q : Poly k) (x : ℝ) : eval (translate w q) x = eval q x + w := by
  simp [translate]

/-- `(S_c q)'(x) = c q'(x)`. -/
@[simp]
theorem derivEval_scale (c : ℝ) (q : Poly k) (x : ℝ) :
    derivEval (scale c q) x = c * derivEval q x :=
  derivEval_smul c q x

/-- `(T_w q)' = q'`. -/
@[simp]
theorem derivEval_translate (w : ℝ) (q : Poly k) (x : ℝ) :
    derivEval (translate w q) x = derivEval q x := by
  simp [translate]

/-! ### Affine reparametrisation and Taylor polynomials -/

/-- The polynomial `q(s X + t)`, of degree at most `k` again. -/
noncomputable def compAffine (s t : ℝ) (q : Poly k) : Poly k :=
  ofPolynomial k ((toPolynomial q).comp (Polynomial.C s * Polynomial.X + Polynomial.C t))

/-- Composition with an affine map keeps the degree at most `k`. -/
theorem natDegree_comp_affine_le (q : Poly k) (s t : ℝ) :
    ((toPolynomial q).comp (Polynomial.C s * Polynomial.X + Polynomial.C t)).natDegree ≤ k := by
  refine (Polynomial.natDegree_comp_le).trans ?_
  have h1 : (Polynomial.C s * Polynomial.X + Polynomial.C t).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    · simp
  calc (toPolynomial q).natDegree * (Polynomial.C s * Polynomial.X + Polynomial.C t).natDegree
      ≤ k * 1 := Nat.mul_le_mul (natDegree_toPolynomial_le q) h1
    _ = k := mul_one k

/-- `(compAffine s t q)(x) = q(s x + t)`. -/
@[simp]
theorem eval_compAffine (s t : ℝ) (q : Poly k) (x : ℝ) :
    eval (compAffine s t q) x = eval q (s * x + t) := by
  rw [compAffine, eval_ofPolynomial (natDegree_comp_affine_le q s t), Polynomial.eval_comp,
    eval_eq_eval_toPolynomial]
  simp

/-- Rapaport's reparametrisation `R_{ψ⁻¹} q = q ∘ ψ⁻¹` for the affine map `ψ x = r x + t`,
`r ≠ 0`: the polynomial `q(r⁻¹ X - r⁻¹ t)`. -/
noncomputable def reparamInv (r t : ℝ) (q : Poly k) : Poly k :=
  compAffine r⁻¹ (-(r⁻¹ * t)) q

/-- `(R_{ψ⁻¹} q)(x) = q((x - t) / r)` for `ψ x = r x + t`. -/
theorem eval_reparamInv {r : ℝ} (hr : r ≠ 0) (t : ℝ) (q : Poly k) (x : ℝ) :
    eval (reparamInv r t q) x = eval q ((x - t) / r) := by
  rw [reparamInv, eval_compAffine]
  congr 1
  field_simp
  ring

/-- `(R_{ψ⁻¹} q)(ψ y) = q(y)`. -/
theorem eval_reparamInv_affine {r : ℝ} (hr : r ≠ 0) (t : ℝ) (q : Poly k) (y : ℝ) :
    eval (reparamInv r t q) (r * y + t) = eval q y := by
  rw [eval_reparamInv hr]
  congr 1
  field_simp
  ring

/-- The coefficient vector `(f^{(j)}(a) / j!)_{j ≤ k}` of the Taylor polynomial of `f` at `a`,
written in powers of `X - a`; it is the Taylor polynomial `P_{k,0}` of `y ↦ f(a + y)` at `0`. -/
noncomputable def taylorCoeff (k : ℕ) (a : ℝ) (f : ℝ → ℝ) : Poly k :=
  WithLp.toLp 2 fun j => iteratedDeriv j f a / ((j : ℕ).factorial : ℝ)

/-- The coefficients of `taylorCoeff k a f`. -/
@[simp]
theorem taylorCoeff_apply (a : ℝ) (f : ℝ → ℝ) (j : Fin (k + 1)) :
    taylorCoeff k a f j = iteratedDeriv j f a / ((j : ℕ).factorial : ℝ) := rfl

/-- Rapaport's `P_{k,a} f`, the `k`-th order Taylor polynomial
`∑_{j ≤ k} f^{(j)}(a) / j! (X - a)^j` of `f` at `a`, as an element of `𝒫_k`. -/
noncomputable def taylor (k : ℕ) (a : ℝ) (f : ℝ → ℝ) : Poly k :=
  compAffine 1 (-a) (taylorCoeff k a f)

/-- The value of `taylorCoeff k a f`. -/
theorem eval_taylorCoeff (a : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    eval (taylorCoeff k a f) x =
      ∑ j : Fin (k + 1), iteratedDeriv j f a / ((j : ℕ).factorial : ℝ) * x ^ (j : ℕ) := rfl

/-- The value of the Taylor polynomial `P_{k,a} f`. -/
theorem eval_taylor (a : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    eval (taylor k a f) x =
      ∑ j : Fin (k + 1), iteratedDeriv j f a / ((j : ℕ).factorial : ℝ) * (x - a) ^ (j : ℕ) := by
  rw [taylor, eval_compAffine, eval_taylorCoeff, one_mul, sub_eq_add_neg]

end Poly

/-! ### Dyadic partitions of `𝒫_k` -/

variable {k : ℕ}

/-- The index `(⌊2^n q_j⌋)_j` of the level-`n` dyadic cell of `𝒫_k ≅ ℝ^{k+1}` containing `q`. -/
noncomputable def cellIdxVec (n : ℕ) (q : Poly k) : Fin (k + 1) → ℤ := fun j => cellIdx n (q j)

/-- The level-`n` dyadic cell of `𝒫_k` with index `c`, the product of the cells `cell n (c j)`. -/
def cellVec (n : ℕ) (c : Fin (k + 1) → ℤ) : Set (Poly k) := {q | cellIdxVec n q = c}

/-- The level-`n` dyadic cell `𝒟_n^{𝒫_k}(q)` of `q`. -/
def cellOfVec (n : ℕ) (q : Poly k) : Set (Poly k) := cellVec n (cellIdxVec n q)

/-- The dyadic entropy `H(ν, 𝒟_n^{𝒫_k}) = -∑_D ν(D) log₂ ν(D)` in bits. -/
noncomputable def dyadicEntropyVec (ν : Measure (Poly k)) (n : ℕ) : ℝ :=
  (∑' c : Fin (k + 1) → ℤ, Real.negMulLog (ν.real (cellVec n c))) / Real.log 2

/-- The level-`n` component `ν_{q,n}` of `ν` at `q`: `ν` conditioned on the dyadic cell of `q`.
It is the zero measure when the cell has measure zero or infinity. -/
noncomputable def componentVec (ν : Measure (Poly k)) (n : ℕ) (q : Poly k) : Measure (Poly k) :=
  (ν (cellOfVec n q))⁻¹ • ν.restrict (cellOfVec n q)

/-- The probability `ℙ_{i ≤ j ≤ i+n} (P j q)` that a property holds for a uniformly random level
`j ∈ {i, …, i + n}` and a `ν`-random polynomial `q`. -/
noncomputable def levelProbVec (ν : Measure (Poly k)) (i n : ℕ) (P : ℕ → Poly k → Prop) : ℝ :=
  (∑ j ∈ Finset.Icc i (i + n), ν.real {q | P j q}) / ((n : ℝ) + 1)

/-- A polynomial lies in the cell `c` exactly when each coefficient lies in the cell `c j`. -/
theorem mem_cellVec_iff {n : ℕ} {c : Fin (k + 1) → ℤ} {q : Poly k} :
    q ∈ cellVec n c ↔ ∀ j, q j ∈ cell n (c j) := by
  simp only [cellVec, mem_ofPred_eq, funext_iff, cellIdxVec, cellIdx, cell, mem_Ico]
  refine forall_congr' fun j => ?_
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [Int.floor_eq_iff, div_le_iff₀ h2, lt_div_iff₀ h2]
  constructor <;> rintro ⟨h1, h3⟩ <;> constructor <;> linarith

/-- A polynomial lies in its own cell. -/
theorem mem_cellOfVec_self (n : ℕ) (q : Poly k) : q ∈ cellOfVec n q := rfl

/-- The cell index on `𝒫_k` is measurable. -/
theorem measurable_cellIdxVec (n : ℕ) : Measurable (cellIdxVec (k := k) n) := by
  refine Measurable.of_eval fun j => ?_
  unfold cellIdxVec cellIdx
  exact Int.measurable_floor.comp
    (measurable_const.mul ((PiLp.continuous_apply 2 _ j).measurable))

/-- Dyadic cells of `𝒫_k` are measurable. -/
theorem measurableSet_cellVec (n : ℕ) (c : Fin (k + 1) → ℤ) :
    MeasurableSet (cellVec (k := k) n c) :=
  measurable_cellIdxVec n (measurableSet_singleton c)

/-- The cell of a polynomial is measurable. -/
theorem measurableSet_cellOfVec (n : ℕ) (q : Poly k) : MeasurableSet (cellOfVec n q) :=
  measurableSet_cellVec n _

/-! ### The action of measures on polynomials -/

/-- Rapaport's `ν.θ`: the image of `ν × θ` under `(q, x) ↦ q(x)`. -/
noncomputable def act (ν : Measure (Poly k)) (θ : Measure ℝ) : Measure ℝ :=
  (ν.prod θ).map fun z => Poly.eval z.1 z.2

/-- Rapaport's `ν.x = ν.δ_x`: the image of `ν` under `q ↦ q(x)`. -/
noncomputable def actPoint (ν : Measure (Poly k)) (x : ℝ) : Measure ℝ :=
  ν.map fun q => Poly.eval q x

/-- `ν.θ` is a probability measure for probability measures `ν` and `θ`. -/
instance isProbabilityMeasure_act (ν : Measure (Poly k)) (θ : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure θ] : IsProbabilityMeasure (act ν θ) := by
  unfold act
  infer_instance

/-- `ν.x` is a probability measure for a probability measure `ν`. -/
instance isProbabilityMeasure_actPoint (ν : Measure (Poly k)) (x : ℝ)
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (actPoint ν x) := by
  unfold actPoint
  infer_instance

/-- `ν.θ` is a finite measure for finite measures `ν` and `θ`. -/
instance isFiniteMeasure_act (ν : Measure (Poly k)) (θ : Measure ℝ)
    [IsFiniteMeasure ν] [IsFiniteMeasure θ] : IsFiniteMeasure (act ν θ) := by
  unfold act
  infer_instance

/-- `ν.x` is a finite measure for a finite measure `ν`. -/
instance isFiniteMeasure_actPoint (ν : Measure (Poly k)) (x : ℝ)
    [IsFiniteMeasure ν] : IsFiniteMeasure (actPoint ν x) := by
  unfold actPoint
  infer_instance

/-- `ν.θ(s) = ∫ θ(q⁻¹ s) dν(q)`. -/
theorem act_apply (ν : Measure (Poly k)) (θ : Measure ℝ) [SFinite θ] {s : Set ℝ}
    (hs : MeasurableSet s) :
    act ν θ s = ∫⁻ q, θ ((Poly.eval q) ⁻¹' s) ∂ν := by
  rw [act, Measure.map_apply Poly.measurable_eval_uncurry hs,
    Measure.prod_apply (Poly.measurable_eval_uncurry hs)]
  rfl

/-- `ν.x(s) = ν{q : q(x) ∈ s}`. -/
theorem actPoint_apply (ν : Measure (Poly k)) (x : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    actPoint ν x s = ν {q | Poly.eval q x ∈ s} := by
  rw [actPoint, Measure.map_apply (Poly.measurable_eval_left x) hs]
  rfl

/-- `ν.θ = ∫ ν.x dθ(x)`. -/
theorem act_apply_eq_lintegral_actPoint (ν : Measure (Poly k)) (θ : Measure ℝ) [SFinite ν]
    [SFinite θ] {s : Set ℝ} (hs : MeasurableSet s) :
    act ν θ s = ∫⁻ x, actPoint ν x s ∂θ := by
  rw [act, Measure.map_apply Poly.measurable_eval_uncurry hs,
    Measure.prod_apply_symm (Poly.measurable_eval_uncurry hs)]
  refine lintegral_congr fun x => ?_
  rw [actPoint_apply ν x hs]
  rfl

/-- `ν.δ_x = ν.x`. -/
theorem act_dirac (ν : Measure (Poly k)) [SFinite ν] (x : ℝ) :
    act ν (Measure.dirac x) = actPoint ν x := by
  rw [act, Measure.prod_dirac, Measure.map_map (g := fun z : Poly k × ℝ => Poly.eval z.1 z.2)
    (f := fun q => (q, x)) Poly.measurable_eval_uncurry (by fun_prop)]
  rfl

/-- `δ_q.θ` is the image of `θ` under `q`. -/
theorem dirac_act (q : Poly k) (θ : Measure ℝ) [SFinite θ] :
    act (Measure.dirac q) θ = θ.map (Poly.eval q) := by
  rw [act, Measure.dirac_prod, Measure.map_map (g := fun z : Poly k × ℝ => Poly.eval z.1 z.2)
    (f := Prod.mk q) Poly.measurable_eval_uncurry (by fun_prop)]
  rfl

/-- `ν.θ` is additive in `ν`. -/
theorem act_add_left (ν₁ ν₂ : Measure (Poly k)) (θ : Measure ℝ) [SFinite ν₁] [SFinite ν₂]
    [SFinite θ] : act (ν₁ + ν₂) θ = act ν₁ θ + act ν₂ θ := by
  rw [act, Measure.add_prod, Measure.map_add _ _ Poly.measurable_eval_uncurry]
  rfl

/-- `ν.θ` is additive in `θ`. -/
theorem act_add_right (ν : Measure (Poly k)) (θ₁ θ₂ : Measure ℝ) [SFinite ν] [SFinite θ₁]
    [SFinite θ₂] : act ν (θ₁ + θ₂) = act ν θ₁ + act ν θ₂ := by
  rw [act, Measure.prod_add, Measure.map_add _ _ Poly.measurable_eval_uncurry]
  rfl

/-- `ν.θ` is homogeneous in `ν`. -/
theorem act_smul_left (c : ℝ≥0∞) (ν : Measure (Poly k)) (θ : Measure ℝ) [SFinite θ] :
    act (c • ν) θ = c • act ν θ := by
  rw [act, Measure.prod_smul_left, Measure.map_smul]
  all_goals first | rfl | exact Poly.measurable_eval_uncurry.aemeasurable

/-- `ν.θ` is homogeneous in `θ`. -/
theorem act_smul_right (c : ℝ≥0∞) (ν : Measure (Poly k)) (θ : Measure ℝ) [SFinite ν]
    [SFinite θ] : act ν (c • θ) = c • act ν θ := by
  ext s hs
  rw [act_apply_eq_lintegral_actPoint ν _ hs, Measure.smul_apply, act_apply_eq_lintegral_actPoint
    ν _ hs, lintegral_smul_measure]

/-- `0.θ = 0`. -/
theorem act_zero_left (θ : Measure ℝ) : act (0 : Measure (Poly k)) θ = 0 := by
  simp [act]

/-- `ν.0 = 0`. -/
theorem act_zero_right (ν : Measure (Poly k)) : act ν 0 = 0 := by
  simp [act]

end FractalGeometry.Rapaport.Analytic
