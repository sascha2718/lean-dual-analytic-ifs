module

public import AnalyticESC.Literature.Rapaport.Analytic.Dyadic

@[expose] public section

/-!
# The choice of lengths in the main argument

The numerical relations between the parameters of the proof of Theorem 1.2 of A. Rapaport,
*Dimension of self-conformal measures associated to an exponentially separated analytic IFS on
ℝ*, arXiv:2412.16753v2, Section 4 (the relations (4.2) `Δ⁻¹, c⁻¹, C ≪ M ≪ k ≪ ρ⁻¹ ≪ δ⁻¹ ≪ n`).
For a total length `m`, the second length is `n' = ⌊κ m⌋` with `κ = Δ / (4 log N)`, the first is
`n = m - n'`, and the level `L = ⌊χ m / log 2⌋` corresponds to Rapaport's `𝒟_{χ(n+n')}` (`χ` in
nats). This file proves that, for fixed `M, k, C, δ`, all the inequalities between these
quantities used in the main argument hold for every large `m`.

## Main declarations

* `lengths_basic`: `n + n' = m`, `κ m - 1 < n' ≤ κ m`, `m ≤ 2 n`.
* `two_pow_floor_le`, `exp_le_two_mul_two_pow_floor`: `e^{χ m} / 2 < 2^L ≤ e^{χ m}`.
* `eventually_numeric`: the numerical conditions.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Main.Numeric`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic.SectionFour

open Set Filter Topology

/-- `x^n = e^{n log x}` for `x > 0`. -/
theorem pow_eq_exp_mul_log {x : ℝ} (hx : 0 < x) (n : ℕ) : x ^ n = Real.exp (n * Real.log x) := by
  rw [Real.exp_nat_mul, Real.exp_log hx]

/-- The basic relations between the lengths. -/
theorem lengths_basic {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 8) (m : ℕ) :
    ((⌊κ * m⌋₊ : ℕ) : ℝ) ≤ κ * m ∧ κ * m - 1 < ((⌊κ * m⌋₊ : ℕ) : ℝ) ∧
      (m - ⌊κ * m⌋₊) + ⌊κ * m⌋₊ = m ∧ (m : ℝ) ≤ 2 * ((m - ⌊κ * m⌋₊ : ℕ) : ℝ) := by
  have h1 : ((⌊κ * m⌋₊ : ℕ) : ℝ) ≤ κ * m := Nat.floor_le (by positivity)
  have h2 : κ * m - 1 < ((⌊κ * m⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (κ * m)
    linarith
  have hle : ⌊κ * m⌋₊ ≤ m := by
    have : ((⌊κ * m⌋₊ : ℕ) : ℝ) ≤ m := h1.trans (by nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])
    exact_mod_cast this
  refine ⟨h1, h2, Nat.sub_add_cancel hle, ?_⟩
  rw [Nat.cast_sub hle]
  nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]

/-- `2^{⌊χ m / log 2⌋} ≤ e^{χ m}`. -/
theorem two_pow_floor_le {χ : ℝ} (hχ : 0 ≤ χ) (m : ℕ) :
    (2 : ℝ) ^ ⌊χ * m / Real.log 2⌋₊ ≤ Real.exp (χ * m) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [pow_eq_exp_mul_log (by norm_num : (0 : ℝ) < 2)]
  refine Real.exp_le_exp.2 ?_
  have := Nat.floor_le (by positivity : 0 ≤ χ * m / Real.log 2)
  rw [le_div_iff₀ hlog2] at this
  exact this

/-- `e^{χ m} ≤ 2 · 2^{⌊χ m / log 2⌋}`. -/
theorem exp_le_two_mul_two_pow_floor (χ : ℝ) (m : ℕ) :
    Real.exp (χ * m) ≤ 2 * (2 : ℝ) ^ ⌊χ * m / Real.log 2⌋₊ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [← pow_succ', pow_eq_exp_mul_log (by norm_num : (0 : ℝ) < 2)]
  refine Real.exp_le_exp.2 ?_
  have := Nat.lt_floor_add_one (χ * m / Real.log 2)
  rw [div_lt_iff₀ hlog2] at this
  push_cast
  linarith

/-- An affine lower bound in `n` eventually dominates a constant. -/
theorem eventually_const_le_mul {f : ℕ → ℕ} (hf : Tendsto f atTop atTop) {a b : ℝ}
    (hb : 0 < b) : ∀ᶠ m in atTop, a ≤ b * f m := by
  have h := (tendsto_natCast_atTop_atTop.comp hf).const_mul_atTop hb
  exact h.eventually_ge_atTop a

/-- Condition (4.4) on the number of labels: `log((S+2) N^{n'}) + 2δ n log N ≤ (2/3) Δ n`. -/
theorem numeric_count {δ Δ Λ κ : ℝ} {N n n' m : ℕ} (hδ0 : 0 < δ)
    (hδΔ1 : δ ≤ Δ * Real.log 2 / 40) (hδΔ2 : δ ≤ Δ / (24 * Λ)) (hΔ : 0 < Δ) (hΛ : 0 < Λ)
    (hΛN : Λ = Real.log N) (hκ : κ = Δ / (4 * Λ)) (hn'κ : (n' : ℝ) ≤ κ * m)
    (hm : (m : ℝ) ≤ 2 * n) (hnT : 30 / Δ ≤ n) :
    Real.log ((⌊2 * n * δ / Real.log 2⌋₊ + 2) * N ^ n') + 2 * δ * (n * Real.log N) ≤
      2 / 3 * (Δ * n) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN0 : (0 : ℝ) < N := by
    by_contra h
    have : (N : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg N)
    rw [this, Real.log_zero] at hΛN
    linarith
  have hS : ((⌊2 * n * δ / Real.log 2⌋₊ : ℕ) : ℝ) ≤ 2 * n * δ / Real.log 2 :=
    Nat.floor_le (by positivity)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, ← hΛN]
  have h1 : Real.log ((⌊2 * n * δ / Real.log 2⌋₊ : ℕ) + 2) ≤ 2 * n * δ / Real.log 2 + 1 := by
    have := Real.log_le_sub_one_of_pos (by positivity :
      (0 : ℝ) < (⌊2 * n * δ / Real.log 2⌋₊ : ℕ) + 2)
    linarith
  have h2 : 2 * n * δ / Real.log 2 ≤ Δ * n / 20 := by
    rw [div_le_iff₀ hlog2]
    have : δ * 40 ≤ Δ * Real.log 2 := by
      rw [le_div_iff₀ (by norm_num)] at hδΔ1
      linarith
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h3 : (n' : ℝ) * Λ ≤ Δ * n / 2 := by
    have : κ * Λ = Δ / 4 := by rw [hκ]; field_simp
    have h4 : (n' : ℝ) * Λ ≤ κ * m * Λ := mul_le_mul_of_nonneg_right hn'κ hΛ.le
    have h5 : κ * m * Λ = Δ / 4 * m := by rw [mul_comm κ, mul_assoc, this]; ring
    nlinarith
  have h4 : 2 * δ * (n * Λ) ≤ Δ * n / 12 := by
    have : δ * (24 * Λ) ≤ Δ := by
      rw [le_div_iff₀ (by positivity)] at hδΔ2
      exact hδΔ2
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h5 : 1 ≤ Δ * n / 30 := by
    rw [div_le_iff₀ hΔ] at hnT
    linarith
  linarith

/-- Condition (4.5) on the bi-Lipschitz error:
`log (2 D₀ / (2^L C⁻¹ e^{-m(χ+δ)}) + 2) ≤ 3 δ M n`. -/
theorem numeric_err₁ {χ δ C D₀ : ℝ} {M n n' m L : ℕ} (hδ0 : 0 < δ)
    (hC1 : 1 ≤ C) (hD₀ : D₀ ≤ C) (hD0 : 0 < D₀) (hM : 1 ≤ M) (hsum : n + n' = m)
    (hm : (m : ℝ) ≤ 2 * n) (hL : Real.exp (χ * m) ≤ 2 * 2 ^ L)
    (hnT : Real.log (6 * C ^ 2) / δ ≤ n) :
    Real.log (2 * D₀ / (2 ^ L * (C⁻¹ * Real.exp (-(n * (χ + δ))) *
      Real.exp (-(n' * (χ + δ))))) + 2) ≤ 3 * δ * (M * n : ℕ) := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC1
  have hexp : Real.exp (-(n * (χ + δ))) * Real.exp (-(n' * (χ + δ))) =
      Real.exp (-(χ * m)) * Real.exp (-(δ * m)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    have : (m : ℝ) = n + n' := by exact_mod_cast hsum.symm
    rw [this]
    ring
  have hβ : Real.exp (-(δ * m)) / (2 * C) ≤
      2 ^ L * (C⁻¹ * Real.exp (-(n * (χ + δ))) * Real.exp (-(n' * (χ + δ)))) := by
    rw [mul_assoc C⁻¹, hexp]
    have h1 : Real.exp (-(χ * m)) * Real.exp (χ * m) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h2 : Real.exp (χ * m) / 2 ≤ 2 ^ L := by linarith
    have e : (Real.exp (χ * m) / 2) * (C⁻¹ * (Real.exp (-(χ * m)) * Real.exp (-(δ * m)))) =
        Real.exp (-(δ * m)) / (2 * C) := by
      calc (Real.exp (χ * m) / 2) * (C⁻¹ * (Real.exp (-(χ * m)) * Real.exp (-(δ * m))))
          = (Real.exp (-(χ * m)) * Real.exp (χ * m)) * Real.exp (-(δ * m)) / (2 * C) := by
            field_simp
        _ = Real.exp (-(δ * m)) / (2 * C) := by rw [h1, one_mul]
    rw [← e]
    gcongr
  have hβ0 : 0 < Real.exp (-(δ * m)) / (2 * C) := by positivity
  have hq : 2 * D₀ / (2 ^ L * (C⁻¹ * Real.exp (-(n * (χ + δ))) *
      Real.exp (-(n' * (χ + δ))))) ≤ 4 * C ^ 2 * Real.exp (δ * m) := by
    calc _ ≤ 2 * D₀ / (Real.exp (-(δ * m)) / (2 * C)) := by gcongr
      _ ≤ 2 * C / (Real.exp (-(δ * m)) / (2 * C)) := by gcongr
      _ = 4 * C ^ 2 * Real.exp (δ * m) := by
          rw [Real.exp_neg]
          field_simp
          ring
  have hexp1 : 1 ≤ Real.exp (δ * m) := Real.one_le_exp (by positivity)
  have hlog : Real.log (2 * D₀ / (2 ^ L * (C⁻¹ * Real.exp (-(n * (χ + δ))) *
      Real.exp (-(n' * (χ + δ))))) + 2) ≤ Real.log (6 * C ^ 2) + δ * m := by
    rw [← Real.log_exp (δ * m), ← Real.log_mul (by positivity) (Real.exp_pos _).ne']
    refine Real.log_le_log (by positivity) ?_
    have : 2 ≤ 2 * C ^ 2 * Real.exp (δ * m) := by
      have : 1 ≤ C ^ 2 := one_le_pow₀ hC1
      nlinarith
    linarith
  have hM' : (n : ℝ) ≤ ((M * n : ℕ) : ℝ) := by exact_mod_cast Nat.le_mul_of_pos_left _ hM
  have h3 : Real.log (6 * C ^ 2) ≤ δ * n := by
    rw [div_le_iff₀ hδ0] at hnT
    linarith
  nlinarith

/-- Condition on the error of the high-entropy pieces:
`log 8 + log (2 A + 2) ≤ 3 δ M n` for `A = 2 C e^{δ m}`. -/
theorem numeric_err₂ {δ C : ℝ} {M n m : ℕ} (hδ0 : 0 < δ) (hC1 : 1 ≤ C) (hM : 1 ≤ M)
    (hm : (m : ℝ) ≤ 2 * n) (hnT : Real.log (48 * C) / δ ≤ n) :
    Real.log 8 + Real.log (2 * (2 * C * Real.exp (δ * m)) + 2) ≤ 3 * δ * (M * n : ℕ) := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC1
  have hexp1 : 1 ≤ Real.exp (δ * m) := Real.one_le_exp (by positivity)
  have hlog : Real.log (2 * (2 * C * Real.exp (δ * m)) + 2) ≤ Real.log (6 * C) + δ * m := by
    have e : Real.log (6 * C) + δ * m = Real.log (6 * C * Real.exp (δ * m)) := by
      rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    rw [e]
    refine Real.log_le_log (by positivity) ?_
    nlinarith
  have h8 : Real.log 8 + Real.log (6 * C) = Real.log (48 * C) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    ring_nf
  have hM' : (n : ℝ) ≤ ((M * n : ℕ) : ℝ) := by exact_mod_cast Nat.le_mul_of_pos_left _ hM
  have h3 : Real.log (48 * C) ≤ δ * n := by
    rw [div_le_iff₀ hδ0] at hnT
    linarith
  nlinarith

/-- The Taylor remainder condition (4.6):
`C^{k+1} e^{-n(χ-δ)} (C e^{-n'(χ-δ)})^{k+1} ≤ 2^{-(Mn+L)}`. -/
theorem numeric_taylor {χ δ κ C : ℝ} {M k n n' m L : ℕ} (hχ : 0 < χ)
    (hδχ : δ ≤ χ / 4) (hδ1 : δ ≤ 1 / 4) (hC1 : 1 ≤ C) (hk : 1 ≤ k)
    (hkM : M * Real.log 2 + 1 ≤ κ * k * χ / 2) (hκ0 : 0 ≤ κ) (hsum : n + n' = m)
    (hn' : κ * m - 1 < n') (hL : (2 : ℝ) ^ L ≤ Real.exp (χ * m))
    (hnT : 4 / 3 * ((2 * k + 2) * Real.log C + k * χ / 2) ≤ n) :
    C ^ (k + 1) * Real.exp (-(n * (χ - δ))) * (C * Real.exp (-(n' * (χ - δ)))) ^ (k + 1) ≤
      1 / 2 ^ (M * n + L) := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmr : (m : ℝ) = n + n' := by exact_mod_cast hsum.symm
  -- both sides as exponentials
  have hlhs : C ^ (k + 1) * Real.exp (-(n * (χ - δ))) * (C * Real.exp (-(n' * (χ - δ)))) ^ (k + 1) =
      Real.exp ((2 * k + 2) * Real.log C - n * (χ - δ) - (k + 1) * n' * (χ - δ)) := by
    rw [mul_pow, ← Real.exp_nat_mul, pow_eq_exp_mul_log hC0, ← mul_assoc, ← Real.exp_add,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hrhs : Real.exp (-(M * n * Real.log 2 + χ * m)) ≤ 1 / 2 ^ (M * n + L) := by
    rw [one_div, pow_eq_exp_mul_log (by norm_num), ← Real.exp_neg]
    refine Real.exp_le_exp.2 ?_
    have h1 : (L : ℝ) * Real.log 2 ≤ χ * m := by
      have := Real.log_le_log (by positivity) hL
      rwa [Real.log_pow, Real.log_exp] at this
    push_cast
    nlinarith
  rw [hlhs]
  refine le_trans (Real.exp_le_exp.2 ?_) hrhs
  -- the exponents
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hgap : (k : ℝ) * χ / 2 ≤ (k + 1) * (χ - δ) - χ := by nlinarith
  have hn'n : κ * n - 1 < n' := by
    have : κ * n ≤ κ * m := by rw [hmr]; nlinarith [(Nat.cast_nonneg n' : (0 : ℝ) ≤ n')]
    linarith
  have hn'0 : (0 : ℝ) ≤ n' := Nat.cast_nonneg n'
  have h2 : (κ * n - 1) * (k * χ / 2) ≤ n' * ((k + 1) * (χ - δ) - χ) := by
    have h3 : 0 ≤ (k : ℝ) * χ / 2 := by positivity
    calc (κ * n - 1) * (k * χ / 2) ≤ n' * (k * χ / 2) :=
          mul_le_mul_of_nonneg_right hn'n.le h3
      _ ≤ n' * ((k + 1) * (χ - δ) - χ) := mul_le_mul_of_nonneg_left hgap hn'0
  have h4 : (n : ℝ) * (M * Real.log 2 + 1) ≤ n * (κ * k * χ / 2) :=
    mul_le_mul_of_nonneg_left hkM (Nat.cast_nonneg n)
  rw [hmr]
  nlinarith

/-- The condition `r ≥ 8 k (k+1) C^{k+1}` behind the derivative bound (4.10). -/
theorem numeric_rbig {χ δ C : ℝ} {k n' : ℕ} (hδχ : δ < χ) (hC1 : 1 ≤ C)
    (hnT : Real.log (8 * k * (k + 1) * C ^ (k + 1) * C + 1) / (χ - δ) ≤ n') :
    8 * k * (k + 1) * C ^ (k + 1) * (C * Real.exp (-(n' * (χ - δ)))) ≤ 1 := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC1
  have hχδ : 0 < χ - δ := sub_pos.2 hδχ
  set K := 8 * k * (k + 1) * C ^ (k + 1) * C with hK
  have hK0 : 0 ≤ K := by positivity
  have h1 : Real.log (K + 1) ≤ n' * (χ - δ) := by
    rw [div_le_iff₀ hχδ] at hnT
    exact hnT
  have h2 : K + 1 ≤ Real.exp (n' * (χ - δ)) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < K + 1)]
    exact Real.exp_le_exp.2 h1
  have h3 : 8 * k * (k + 1) * C ^ (k + 1) * (C * Real.exp (-(n' * (χ - δ)))) =
      K * (Real.exp (n' * (χ - δ)))⁻¹ := by
    rw [hK, Real.exp_neg]
    ring
  rw [h3, mul_inv_le_iff₀ (Real.exp_pos _)]
  linarith

/-- The scale condition `C e^{m(χ+δ)} ≤ 2^L A` for `A = 2 C e^{δ m}`. -/
theorem numeric_scale {χ δ C : ℝ} {n n' m L : ℕ} (hC1 : 1 ≤ C) (hsum : n + n' = m)
    (hL : Real.exp (χ * m) ≤ 2 * 2 ^ L) :
    C * Real.exp (n * (χ + δ)) * Real.exp (n' * (χ + δ)) ≤
      2 ^ L * (2 * C * Real.exp (δ * m)) := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC1
  have hmr : (m : ℝ) = n + n' := by exact_mod_cast hsum.symm
  have h1 : Real.exp (n * (χ + δ)) * Real.exp (n' * (χ + δ)) =
      Real.exp (χ * m) * Real.exp (δ * m) := by
    rw [← Real.exp_add, ← Real.exp_add, hmr]
    congr 1
    ring
  calc C * Real.exp (n * (χ + δ)) * Real.exp (n' * (χ + δ))
      = C * (Real.exp (χ * m) * Real.exp (δ * m)) := by rw [mul_assoc, h1]
    _ ≤ C * ((2 * 2 ^ L) * Real.exp (δ * m)) := by gcongr
    _ = 2 ^ L * (2 * C * Real.exp (δ * m)) := by ring

/-- The separation condition `(k+3) 2^{-Mn} < c^m`. -/
theorem numeric_sep {c : ℝ} {M k n m : ℕ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hMc : 2 ≤ 2 ^ M * c ^ 2) (hm : m ≤ 2 * n) (hnT : k + 3 ≤ n) :
    (k + 3) / 2 ^ (M * n) < c ^ m := by
  have h1 : (c ^ 2) ^ n ≤ c ^ m := by
    rw [← pow_mul]
    exact pow_le_pow_of_le_one hc0.le hc1 (by omega)
  have h2 : (2 : ℝ) ^ n ≤ (2 ^ M * c ^ 2) ^ n := pow_le_pow_left₀ (by norm_num) hMc n
  have h3 : ((k + 3 : ℕ) : ℝ) < 2 ^ n := by
    have := Nat.lt_two_pow_self (n := n)
    exact_mod_cast (show k + 3 < 2 ^ n by omega)
  rw [div_lt_iff₀ (by positivity)]
  calc ((k : ℝ) + 3) < 2 ^ n := by exact_mod_cast h3
    _ ≤ (2 ^ M * c ^ 2) ^ n := h2
    _ = (c ^ 2) ^ n * 2 ^ (M * n) := by rw [mul_pow, pow_mul]; ring
    _ ≤ c ^ m * 2 ^ (M * n) := by gcongr

/-- The numerical conditions of the main argument hold for all large total lengths `m`. -/
theorem eventually_numeric {χ δ Δ Λ κ C D₀ c : ℝ} {M k N : ℕ} (hχ : 0 < χ) (hδ0 : 0 < δ)
    (hδχ : δ ≤ χ / 4) (hδ1 : δ ≤ 1 / 4) (hδΔ1 : δ ≤ Δ * Real.log 2 / 40)
    (hδΔ2 : δ ≤ Δ / (24 * Λ)) (hΔ : 0 < Δ) (hΛ : 0 < Λ) (hΛN : Λ = Real.log N)
    (hκ : κ = Δ / (4 * Λ)) (hκ1 : κ ≤ 1 / 8) (hC1 : 1 ≤ C) (hD₀ : D₀ ≤ C) (hD0 : 0 < D₀)
    (hM : 1 ≤ M) (hk : 1 ≤ k) (hkM : M * Real.log 2 + 1 ≤ κ * k * χ / 2) (hc0 : 0 < c)
    (hc1 : c ≤ 1) (hMc : 2 ≤ 2 ^ M * c ^ 2) :
    ∀ᶠ m : ℕ in atTop,
      let n' := ⌊κ * m⌋₊
      let n := m - n'
      let L := ⌊χ * m / Real.log 2⌋₊
      0 < n ∧
      Real.log ((⌊2 * n * δ / Real.log 2⌋₊ + 2) * N ^ n') + 2 * δ * (n * Real.log N) ≤
        2 / 3 * (Δ * n) ∧
      Real.log (2 * D₀ / (2 ^ L * (C⁻¹ * Real.exp (-(n * (χ + δ))) *
        Real.exp (-(n' * (χ + δ))))) + 2) ≤ 3 * δ * (M * n : ℕ) ∧
      Real.log 8 + Real.log (2 * (2 * C * Real.exp (δ * m)) + 2) ≤ 3 * δ * (M * n : ℕ) ∧
      C ^ (k + 1) * Real.exp (-(n * (χ - δ))) * (C * Real.exp (-(n' * (χ - δ)))) ^ (k + 1) ≤
        1 / 2 ^ (M * n + L) ∧
      8 * k * (k + 1) * C ^ (k + 1) * (C * Real.exp (-(n' * (χ - δ)))) ≤ 1 ∧
      C * Real.exp (n * (χ + δ)) * Real.exp (n' * (χ + δ)) ≤
        2 ^ L * (2 * C * Real.exp (δ * m)) ∧
      (k + 3) / 2 ^ (M * n) < c ^ m := by
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hn'T : Tendsto (fun m : ℕ => ⌊κ * m⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hκ0)
  have hnT : Tendsto (fun m : ℕ => m - ⌊κ * m⌋₊) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b => ⟨2 * b, fun m hm => ?_⟩
    have h := (lengths_basic hκ0.le hκ1 m).2.2.2
    have h2 : (2 * b : ℝ) ≤ m := by exact_mod_cast hm
    have : (b : ℝ) ≤ ((m - ⌊κ * m⌋₊ : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  set T₁ : ℝ := max 1 (max (30 / Δ) (max (Real.log (6 * C ^ 2) / δ) (max (Real.log (48 * C) / δ)
    (max (4 / 3 * ((2 * k + 2) * Real.log C + k * χ / 2)) (k + 3))))) with hT₁
  set T₂ : ℝ := Real.log (8 * k * (k + 1) * C ^ (k + 1) * C + 1) / (χ - δ) with hT₂
  filter_upwards [(tendsto_natCast_atTop_atTop.comp hnT).eventually_ge_atTop T₁,
    (tendsto_natCast_atTop_atTop.comp hn'T).eventually_ge_atTop T₂] with m h1 h2
  simp only [Function.comp_apply] at h1 h2
  intro n' n L
  obtain ⟨hb1, hb2, hb3, hb4⟩ := lengths_basic hκ0.le hκ1 m
  have hT1 : (1 : ℝ) ≤ n := (le_max_left _ _).trans h1
  have hT2 : 30 / Δ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans h1
  have hT3 : Real.log (6 * C ^ 2) / δ ≤ n :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans h1
  have hT4 : Real.log (48 * C) / δ ≤ n := ((le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))).trans h1
  have hT5 : 4 / 3 * ((2 * k + 2) * Real.log C + k * χ / 2) ≤ n :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))))).trans h1
  have hT6 : (k : ℝ) + 3 ≤ n := ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))).trans h1
  have hL1 := two_pow_floor_le hχ.le m
  have hL2 := exp_le_two_mul_two_pow_floor χ m
  have hδχ' : δ < χ := by linarith
  have hm2 : m ≤ 2 * n := by exact_mod_cast hb4
  refine ⟨?_, numeric_count hδ0 hδΔ1 hδΔ2 hΔ hΛ hΛN hκ hb1 hb4 hT2,
    numeric_err₁ hδ0 hC1 hD₀ hD0 hM hb3 hb4 hL2 hT3, numeric_err₂ hδ0 hC1 hM hb4 hT4,
    numeric_taylor hχ hδχ hδ1 hC1 hk hkM hκ0.le hb3 hb2 hL1 hT5,
    numeric_rbig hδχ' hC1 h2, numeric_scale hC1 hb3 hL2,
    numeric_sep hc0 hc1 hMc hm2 (by exact_mod_cast hT6)⟩
  exact_mod_cast hT1

end FractalGeometry.Rapaport.Analytic.SectionFour
