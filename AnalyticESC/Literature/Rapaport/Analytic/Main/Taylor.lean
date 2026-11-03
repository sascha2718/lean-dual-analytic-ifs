module

public import AnalyticESC.Literature.Rapaport.Analytic.Main.Statements

@[expose] public section

/-!
# Taylor approximation of the maps `φ_u`

The Taylor approximation used in Section 4 of A. Rapaport, *Dimension of self-conformal measures
associated to an exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2: by Taylor's
theorem with Lagrange remainder and Lemma 2.1(2) (the bound on the higher derivatives),
`|φ_u(y) - P_{k,a} φ_u (y)| ≤ C^{k+1} |φ_u'(0)| |y - a|^{k+1}` for `a, y ∈ I`.

## Main declarations

* `analyticAt_realComp`, `contDiffAt_realComp`: `φ_u` is analytic at the points of `I`.
* `eval_taylor_eq_taylorWithinEval`: Rapaport's `P_{k,a} f` is Mathlib's Taylor polynomial.
* `abs_sub_eval_taylor_le`: the remainder bound.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Main.Taylor`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic.SectionFour

open MeasureTheory Set Filter Topology FractalGeometry.SelfConformal
open FractalGeometry.Rapaport.Analytic
open AnalyticESC (I realComp RapaportHyp)

variable {N : ℕ} {φ : Fin N → ℝ → ℝ}

/-- `φ_u` is analytic at every point of `I`. -/
theorem analyticAt_realComp (hφ : RapaportHyp φ) (u : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    AnalyticAt ℝ (realComp φ u) x := by
  induction u with
  | nil => exact analyticAt_id
  | cons i u ih =>
    rw [realComp_cons]
    exact (hφ.analytic i _ (mapsTo_realComp hφ u hx)).comp ih

/-- `φ_u` is smooth at every point of `I`. -/
theorem contDiffAt_realComp (hφ : RapaportHyp φ) (u : List (Fin N)) {x : ℝ} (hx : x ∈ I)
    (n : WithTop ℕ∞) : ContDiffAt ℝ n (realComp φ u) x :=
  (analyticAt_realComp hφ u hx).contDiffAt.of_le le_top

/-- `uIcc a y ⊆ I` for `a, y ∈ I`. -/
theorem uIcc_subset_I {a y : ℝ} (ha : a ∈ I) (hy : y ∈ I) : uIcc a y ⊆ I :=
  uIcc_subset_Icc ha hy

/-- Rapaport's Taylor polynomial `P_{k,a} f` evaluated at `y` is Mathlib's `taylorWithinEval` on
`[a, y]` for a function smooth at the points of `I`. -/
theorem eval_taylor_eq_taylorWithinEval {f : ℝ → ℝ} (hf : ∀ z ∈ I, ContDiffAt ℝ ⊤ f z)
    (k : ℕ) {a y : ℝ} (ha : a ∈ I) (hay : a ≠ y) :
    Poly.eval (Poly.taylor k a f) y = taylorWithinEval f k (uIcc a y) a y := by
  have hu : UniqueDiffOn ℝ (uIcc a y) := by
    rw [uIcc]
    exact uniqueDiffOn_Icc (min_lt_max.2 hay)
  rw [Poly.eval_taylor, taylor_within_apply, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedDerivWithin_eq_iteratedDeriv hu ((hf a ha).of_le le_top) left_mem_uIcc,
    smul_eq_mul]
  ring

/-- Lemma 2.1(2) with the Lagrange remainder: for `a, y ∈ I`,
`|φ_u(y) - P_{k,a} φ_u (y)| ≤ C^{k+1} |φ_u'(0)| |y - a|^{k+1}`. -/
theorem abs_sub_eval_taylor_le (hφ : RapaportHyp φ) {C : ℝ}
    (hC : ∀ (u : List (Fin N)) (l : ℕ), 1 ≤ l → ∀ x ∈ I,
      |iteratedDeriv l (realComp φ u) x| ≤ l.factorial * C ^ l * |deriv (realComp φ u) 0|)
    (u : List (Fin N)) (k : ℕ) {a y : ℝ} (ha : a ∈ I) (hy : y ∈ I) :
    |realComp φ u y - Poly.eval (Poly.taylor k a (realComp φ u)) y| ≤
      C ^ (k + 1) * |deriv (realComp φ u) 0| * |y - a| ^ (k + 1) := by
  rcases eq_or_ne a y with rfl | hay
  · have h0 : Poly.eval (Poly.taylor k a (realComp φ u)) a = realComp φ u a := by
      rw [Poly.eval_taylor, Fin.sum_univ_succ]
      simp
    rw [h0, sub_self, abs_zero, sub_self, abs_zero, zero_pow (Nat.succ_ne_zero k), mul_zero]
  · have hsmooth : ∀ z ∈ I, ContDiffAt ℝ ⊤ (realComp φ u) z := fun z hz =>
      contDiffAt_realComp hφ u hz ⊤
    have hcd : ContDiffOn ℝ (k + 1) (realComp φ u) (uIcc a y) := fun z hz =>
      (contDiffAt_realComp hφ u (uIcc_subset_I ha hy hz) _).contDiffWithinAt
    obtain ⟨ξ, hξ, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hay hcd
    have hξI : ξ ∈ I := uIcc_subset_I ha hy (uIoo_subset_uIcc_self hξ)
    rw [eval_taylor_eq_taylorWithinEval hsmooth k ha hay, heq]
    have hb := hC u (k + 1) (Nat.succ_pos k) ξ hξI
    have hfac : (0 : ℝ) < ((k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [abs_div, abs_mul, abs_pow, Nat.abs_cast, div_le_iff₀ hfac]
    calc |iteratedDeriv (k + 1) (realComp φ u) ξ| * |y - a| ^ (k + 1)
        ≤ ((k + 1).factorial * C ^ (k + 1) * |deriv (realComp φ u) 0|) * |y - a| ^ (k + 1) :=
          mul_le_mul_of_nonneg_right hb (by positivity)
      _ = C ^ (k + 1) * |deriv (realComp φ u) 0| * |y - a| ^ (k + 1) *
          ((k + 1).factorial : ℝ) := by ring

end FractalGeometry.Rapaport.Analytic.SectionFour
