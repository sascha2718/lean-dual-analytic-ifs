module

public import AnalyticESC.Generic.Class
public import AnalyticESC.Analysis

@[expose] public section

/-!
# Proposition 4.2

The proof of Proposition 4.2 of the paper: a perturbation `g` of a map `f ∈ S^ω(I)` with
`f([0,1]) ⊆ (0,1)` that is small in `𝒞¹` on `[0,1]`, agrees with `f` to first order on a finite
set `𝒴 ∪ 𝒵` and to second order on `𝒵`, and changes `f''/f'` by at least `δ` at the points of
`𝒴`, at a cost of `C δ` in the second derivative.

## Construction

As in (4.2), `g = f e^{φ ψ A}` with
`φ(z) = ∏_{y ∈ 𝒴} (z - y)²`, `ψ(z) = ∏_{w ∈ 𝒵} (z - w)⁴` and
`A(z) = ∑_{y ∈ 𝒴} a_y e^{-(z - y)²/η}`. The same formulas define `g` on `ℂ`; it is holomorphic
wherever `f` is, and real on `ℝ`. Write `h = φ ψ A`. Then `g' = (f' + f h') e^h`,
`g'' = (f'' + 2 f' h' + f h'² + f h'') e^h`, `h' = φ' ψ A + φ ψ' A + φ ψ A'` and
`h'' = φ'' ψ A + φ ψ'' A + φ ψ A'' + 2 φ' ψ' A + 2 φ' ψ A' + 2 φ ψ' A'`, with the derivatives of
`φ`, `ψ` and `A` given by the formulas of the paper (`P1`, `P2`, `A1`, `A2`). Since `φ` vanishes
to second order on `𝒴` and `ψ` to fourth order on `𝒵`, `g = f` and `g' = f'` on `𝒴 ∪ 𝒵`,
`g'' = f''` on `𝒵`, and `g''(y) = f''(y) + 2 f(y) ∏_{y' ≠ y} (y - y')² ψ(y) A(y)` for `y ∈ 𝒴`.
The amplitudes `a_y` of (4.4) give the lower bound in (iii), since `A(y) ≥ a_y`.

## Estimates

The norms are bounded at the points of `[0,1]` term by term, as in the paper, with the trivial
bounds on `φ`, `ψ` and their derivatives and the bound (4.3) (`gaussian_bound`). The norms
`‖φ ψ A‖`, `‖φ' ψ A‖`, `‖φ ψ' A‖`, `‖φ ψ'' A‖`, `‖φ' ψ' A‖` are handled by `(C1)` and the norms
`‖φ ψ A'‖`, `‖φ ψ' A'‖` by `(C2)`. In the three remaining norms the paper's bound on `φ''`,
`(C3)`, `(C4)` and `(C2)` split off a sum `∑_y a_y ψ(x) ∏_{y' ≠ y} (x - y')² F((x - y)²/η)`: for
`‖φ'' ψ A‖` it is the paper's `I(x)` with `F(t) = 2 e^{-t}`, for `‖φ ψ A''‖` it is the whole term
with `F(t) = |4t² - 2t| e^{-t}`, and for `‖φ' ψ A'‖` it is the diagonal part with
`F(t) = 4t e^{-t}`. Such a sum is split as in the paper: far from `𝒴` (at distance at least
`η^{1/3}` from every point) `F` is exponentially small by (4.6) and its analogue, and near a
point `y` of `𝒴`, which by (4.5) is far from the others, the choice (4.4) of `a_y` bounds the
summand by `F_max δ |f'(y)|/|f(y)|`. The paper's "Hence `g ∈ S^ω([0,1])`" is `exists_inClass`.

## Choices and details

* All widths are equal, `η_y = ρ³`, and `(C1)`-`(C4)`, (4.5), (4.6) and the comparison near `𝒴`
  are conditions on `ρ`, which is taken small last. The conditions from (4.3) are imposed with
  `c = a_y` and a common right-hand side `ν`, which absorbs the fixed factors.
* An empty `𝒵` is padded by a point outside `𝒴`, as in the manuscript. Thus `Q ≥ 1`, and the
  factors `16Q² + 12Q` and `8Q` in `(C1)` and `(C2)` apply without changing them.
* The paper writes out the near/far split for `‖φ'' ψ A‖` and leaves `‖φ ψ A''‖` and
  `‖φ' ψ A'‖` to the reader. These two norms are not small: near `y` they are of order
  `a_y ψ(y) ∏_{y' ≠ y} (y - y')² = δ |f'(y)|/(2 |f(y)|)`, so they contribute to `C δ`. Their
  profiles `|4t² - 2t| e^{-t}` and
  `4t e^{-t}` need the analogue of (4.6) with `e^{-η^{-1/3}/2}` in place of `e^{-η^{-1/3}}` far
  from `𝒴`, and the off-diagonal part of `φ' ψ A'` needs (4.3) with `p = 3`, `q = -1` as in
  `(C2)`, with `c = 4 M a_y`.
* The paper bounds the ratio of `ψ(x) ∏_{y' ≠ y} (x - y')²` to its value at `y` by explicit
  products and makes it at most `2` for small `η`; we use continuity at `y`.
* The three norms contribute `2 δ/m`, `10 δ/m` and `2 · 4 δ/m` to `|h''|` on `[0,1]`, where
  `m ≤ f ≤ 1 - m` (`MultiplicativeBump.exists_margin`). With `|f| ≤ 1` and `|e^h| ≤ 2` this gives
  `C = 40/m`, which depends on `f` only.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace MultiplicativeBump

/-- A margin `m > 0` with `m ≤ f ≤ 1 - m` and `m ≤ |f'| ≤ 1 - m` on `I`. -/
theorem exists_margin {ε : ℝ} (hε : 0 < ε) {f : ℂ → ℂ} (hf : InClass ε f)
    (hI : ∀ x ∈ I, (f x).re ∈ Ioo 0 1) :
    ∃ m > 0, ∀ x ∈ I,
      m ≤ (f x).re ∧ (f x).re ≤ 1 - m ∧ m ≤ ‖deriv f x‖ ∧ ‖deriv f x‖ ≤ 1 - m := by
  have hmem : MapsTo ((↑) : ℝ → ℂ) I (nbhd (2 * ε)) := fun x hx =>
    ofReal_mem_nbhd (by positivity) hx
  have hf0 : ContinuousOn (fun x : ℝ => (f x).re) I :=
    Complex.continuous_re.comp_continuousOn
      (hf.differentiableOn.continuousOn.comp Complex.continuous_ofReal.continuousOn hmem)
  have hf1 : ContinuousOn (fun x : ℝ => ‖deriv f x‖) I :=
    ((hf.differentiableOn.deriv (isOpen_nbhd _)).continuousOn.comp
      Complex.continuous_ofReal.continuousOn hmem).norm
  set h : ℝ → ℝ := fun x =>
    min (min (f x).re (1 - (f x).re)) (min ‖deriv f x‖ (1 - ‖deriv f x‖)) with hh
  have hcont : ContinuousOn h I :=
    (hf0.inf (continuousOn_const.sub hf0)).inf (hf1.inf (continuousOn_const.sub hf1))
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, by norm_num⟩ hcont
  have hpos : ∀ x ∈ I, 0 < h x := fun x hx => by
    have hcl : (x : ℂ) ∈ closure (nbhd ε) := subset_closure (ofReal_mem_nbhd hε hx)
    have h1 := hI x hx
    have h2 := norm_pos_iff.2 (hf.deriv_ne_zero x hcl)
    have h3 := hf.norm_deriv_lt_one x hcl
    simp only [hh, lt_min_iff]
    exact ⟨⟨h1.1, by linarith [h1.2]⟩, h2, by linarith⟩
  refine ⟨h x₀, hpos x₀ hx₀, fun x hx => ?_⟩
  have h1 : h x₀ ≤ h x := isMinOn_iff.1 hmin x hx
  simp only [hh, le_min_iff] at h1 ⊢
  exact ⟨h1.1.1, by linarith [h1.1.2], h1.2.1, by linarith [h1.2.2]⟩

/-! ## The polynomial factors `φ` and `ψ` -/

/-- The product `P_{m,W}(z) = ∏_{w ∈ W} (z - w)^{m+2}`; `φ = P_{0,𝒴}` and `ψ = P_{2,𝒵}`. -/
noncomputable def P (m : ℕ) (W : Finset ℝ) (z : ℂ) : ℂ := ∏ w ∈ W, (z - w) ^ (m + 2)

/-- The derivative `P'_{m,W}(z) = ∑_{i ∈ W} (m+2) (z - i)^{m+1} P_{m,W∖{i}}(z)`. -/
noncomputable def P1 (m : ℕ) (W : Finset ℝ) (z : ℂ) : ℂ :=
  ∑ i ∈ W, ((m + 2 : ℕ) : ℂ) * (z - i) ^ (m + 1) * P m (W.erase i) z

/-- The second derivative `P''_{m,W}(z) = ∑_{i ∈ W} ((m+2)(m+1) (z - i)^m P_{m,W∖{i}}(z) +
(m+2) (z - i)^{m+1} P'_{m,W∖{i}}(z))`. -/
noncomputable def P2 (m : ℕ) (W : Finset ℝ) (z : ℂ) : ℂ :=
  ∑ i ∈ W, (((m + 2 : ℕ) : ℂ) * ((m + 1 : ℕ) : ℂ) * (z - i) ^ m * P m (W.erase i) z +
    ((m + 2 : ℕ) : ℂ) * (z - i) ^ (m + 1) * P1 m (W.erase i) z)

/-- `P'_{m,W}` is the derivative of `P_{m,W}`. -/
theorem hasDerivAt_P (m : ℕ) (W : Finset ℝ) (z : ℂ) : HasDerivAt (P m W) (P1 m W z) z := by
  have h := HasDerivAt.fun_finsetProd (u := W) (f := fun w z => (z - (w : ℂ)) ^ (m + 2))
    (f' := fun w => ((m + 2 : ℕ) : ℂ) * (z - w) ^ (m + 1)) (x := z) fun w _ => by
      simpa using ((hasDerivAt_id' z).sub_const (w : ℂ)).fun_pow (m + 2)
  refine h.congr_deriv (Finset.sum_congr rfl fun i _ => ?_)
  rw [smul_eq_mul]
  simp only [P]
  ring

/-- `P''_{m,W}` is the derivative of `P'_{m,W}`. -/
theorem hasDerivAt_P1 (m : ℕ) (W : Finset ℝ) (z : ℂ) : HasDerivAt (P1 m W) (P2 m W z) z := by
  have h := HasDerivAt.fun_sum (u := W)
    (A := fun i z => ((m + 2 : ℕ) : ℂ) * (z - i) ^ (m + 1) * P m (W.erase i) z)
    (A' := fun i => ((m + 2 : ℕ) : ℂ) * (((m + 1 : ℕ) : ℂ) * (z - i) ^ m) * P m (W.erase i) z +
      ((m + 2 : ℕ) : ℂ) * (z - i) ^ (m + 1) * P1 m (W.erase i) z) (x := z) fun i _ => by
      have h1 : HasDerivAt (fun z : ℂ => (z - i) ^ (m + 1))
          (((m + 1 : ℕ) : ℂ) * (z - i) ^ m) z := by
        simpa using ((hasDerivAt_id' z).sub_const (i : ℂ)).fun_pow (m + 1)
      exact (h1.const_mul _).mul (hasDerivAt_P m (W.erase i) z)
  refine h.congr_deriv (Finset.sum_congr rfl fun i _ => ?_)
  ring

/-- `φ'` and `ψ'` are given by `P'`. -/
theorem deriv_P (m : ℕ) (W : Finset ℝ) : deriv (P m W) = P1 m W :=
  funext fun z => (hasDerivAt_P m W z).deriv

/-- `φ''` and `ψ''` are given by `P''`. -/
theorem deriv_P1 (m : ℕ) (W : Finset ℝ) : deriv (P1 m W) = P2 m W :=
  funext fun z => (hasDerivAt_P1 m W z).deriv

/-- `P_{m,W}` is entire. -/
theorem differentiable_P (m : ℕ) (W : Finset ℝ) : Differentiable ℂ (P m W) :=
  fun z => (hasDerivAt_P m W z).differentiableAt

/-- `P_{m,W}(z) ≠ 0` for `z ∉ W`. -/
theorem P_ne_zero (m : ℕ) {W : Finset ℝ} {y : ℝ} (hy : y ∉ W) : P m W y ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun w hw => pow_ne_zero _ (sub_ne_zero.2 fun h =>
    hy (by rw [Complex.ofReal_injective h]; exact hw))

/-- `P_{m,W}` vanishes on `W`. -/
theorem P_of_mem (m : ℕ) {W : Finset ℝ} {w : ℝ} (hw : w ∈ W) : P m W w = 0 :=
  Finset.prod_eq_zero hw (by simp)

/-- `P'_{m,W}` vanishes on `W`. -/
theorem P1_of_mem (m : ℕ) {W : Finset ℝ} {w : ℝ} (hw : w ∈ W) : P1 m W w = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  by_cases hiw : i = w
  · subst hiw
    simp
  · rw [P_of_mem m (Finset.mem_erase.2 ⟨Ne.symm hiw, hw⟩), mul_zero]

/-- `P''_{m,W}(w) = (m+2)(m+1) 0^m P_{m,W∖{w}}(w)` for `w ∈ W`. -/
theorem P2_of_mem (m : ℕ) {W : Finset ℝ} {w : ℝ} (hw : w ∈ W) :
    P2 m W w = ((m + 2 : ℕ) : ℂ) * ((m + 1 : ℕ) : ℂ) * 0 ^ m * P m (W.erase w) w := by
  rw [P2, Finset.sum_eq_single w]
  · simp
  · intro i _ hiw
    have hw' : w ∈ W.erase i := Finset.mem_erase.2 ⟨Ne.symm hiw, hw⟩
    rw [P_of_mem m hw', P1_of_mem m hw']
    ring
  · intro h
    exact absurd hw h

/-! ## Trivial bounds on `φ`, `ψ` and their derivatives -/

section Bounds

variable {m : ℕ} {W : Finset ℝ} {z : ℂ}

/-- `|P_{m,W}| ≤ 1` at points within distance `1` of `W`. -/
theorem norm_P_le_one (hW : ∀ w ∈ W, ‖z - w‖ ≤ 1) : ‖P m W z‖ ≤ 1 := by
  rw [P, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun w hw => by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hW w hw)

/-- `P_{m,W} = (z - l)^{m+2} P_{m,W∖{l}}` for `l ∈ W`. -/
theorem P_eq_mul {l : ℝ} (hl : l ∈ W) (z : ℂ) :
    P m W z = (z - l) ^ (m + 2) * P m (W.erase l) z :=
  (Finset.mul_prod_erase W (fun w : ℝ => (z - w) ^ (m + 2)) hl).symm

/-- `|P_{m,W}(z)| ≤ |z - l|^{m+2}` for `l ∈ W`. -/
theorem norm_P_le (hW : ∀ w ∈ W, ‖z - w‖ ≤ 1) {l : ℝ} (hl : l ∈ W) :
    ‖P m W z‖ ≤ ‖z - l‖ ^ (m + 2) := by
  rw [P_eq_mul hl, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity)
    (norm_P_le_one (W := W.erase l) fun w hw => hW w (Finset.mem_of_mem_erase hw))

/-- `|P'_{m,W}| ≤ (m+2) #W`. -/
theorem norm_P1_le (hW : ∀ w ∈ W, ‖z - w‖ ≤ 1) : ‖P1 m W z‖ ≤ (m + 2) * W.card := by
  rw [P1]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ W, ‖((m + 2 : ℕ) : ℂ) * (z - i) ^ (m + 1) * P m (W.erase i) z‖
      ≤ ∑ _i ∈ W, ((m : ℝ) + 2) := Finset.sum_le_sum fun i hi => by
        rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
        push_cast
        have h1 : ‖z - i‖ ^ (m + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) (hW i hi)
        have h2 := norm_P_le_one (m := m) (W := W.erase i)
          fun w hw => hW w (Finset.mem_of_mem_erase hw)
        calc ((m : ℝ) + 2) * ‖z - i‖ ^ (m + 1) * ‖P m (W.erase i) z‖ ≤ ((m : ℝ) + 2) * 1 * 1 := by
              gcongr
          _ = (m : ℝ) + 2 := by ring
    _ = (m + 2) * W.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- `|P'_{m,W}(z)| ≤ (m+2) #W |z - l|^{m+1}` for `l ∈ W`. -/
theorem norm_P1_le_of_mem (hW : ∀ w ∈ W, ‖z - w‖ ≤ 1) {l : ℝ} (hl : l ∈ W) :
    ‖P1 m W z‖ ≤ (m + 2) * W.card * ‖z - l‖ ^ (m + 1) := by
  rw [P1]
  refine (norm_sum_le _ _).trans ?_
  have hl1 : ‖z - l‖ ≤ 1 := hW l hl
  calc ∑ i ∈ W, ‖((m + 2 : ℕ) : ℂ) * (z - i) ^ (m + 1) * P m (W.erase i) z‖
      ≤ ∑ _i ∈ W, ((m : ℝ) + 2) * ‖z - l‖ ^ (m + 1) := Finset.sum_le_sum fun i hi => by
        rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
        push_cast
        have hWi : ∀ w ∈ W.erase i, ‖z - w‖ ≤ 1 := fun w hw => hW w (Finset.mem_of_mem_erase hw)
        by_cases hil : i = l
        · subst hil
          have h2 := norm_P_le_one (m := m) hWi
          calc ((m : ℝ) + 2) * ‖z - i‖ ^ (m + 1) * ‖P m (W.erase i) z‖
              ≤ ((m : ℝ) + 2) * ‖z - i‖ ^ (m + 1) * 1 := by gcongr
            _ = _ := by ring
        · have h1 : ‖z - i‖ ^ (m + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) (hW i hi)
          have h2 := norm_P_le (m := m) hWi (Finset.mem_erase.2 ⟨Ne.symm hil, hl⟩)
          have h3 : ‖z - l‖ ^ (m + 2) ≤ ‖z - l‖ ^ (m + 1) :=
            pow_le_pow_of_le_one (norm_nonneg _) hl1 (by omega)
          calc ((m : ℝ) + 2) * ‖z - i‖ ^ (m + 1) * ‖P m (W.erase i) z‖
              ≤ ((m : ℝ) + 2) * 1 * ‖z - l‖ ^ (m + 1) := by gcongr; exact h2.trans h3
            _ = _ := by ring
    _ = (m + 2) * W.card * ‖z - l‖ ^ (m + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- `|P''_{m,W}| ≤ (m+2)(m+1) #W + (m+2)² #W²`. -/
theorem norm_P2_le (hW : ∀ w ∈ W, ‖z - w‖ ≤ 1) :
    ‖P2 m W z‖ ≤ (m + 2) * (m + 1) * W.card + (m + 2) ^ 2 * W.card ^ 2 := by
  rw [P2]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ W, ‖((m + 2 : ℕ) : ℂ) * ((m + 1 : ℕ) : ℂ) * (z - i) ^ m * P m (W.erase i) z +
        ((m + 2 : ℕ) : ℂ) * (z - i) ^ (m + 1) * P1 m (W.erase i) z‖
      ≤ ∑ _i ∈ W, (((m : ℝ) + 2) * (m + 1) + (m + 2) ^ 2 * W.card) :=
        Finset.sum_le_sum fun i hi => by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_natCast,
            norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
          push_cast
          have hWi : ∀ w ∈ W.erase i, ‖z - w‖ ≤ 1 :=
            fun w hw => hW w (Finset.mem_of_mem_erase hw)
          have h1 : ‖z - i‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg _) (hW i hi)
          have h1' : ‖z - i‖ ^ (m + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) (hW i hi)
          have h2 := norm_P_le_one (m := m) hWi
          have h3 := norm_P1_le (m := m) hWi
          have h4 : ((W.erase i).card : ℝ) ≤ W.card := by
            exact_mod_cast Finset.card_erase_le
          have h5 : ((m : ℝ) + 2) * (W.erase i).card ≤ (m + 2) * W.card := by gcongr
          calc ((m : ℝ) + 2) * (m + 1) * ‖z - i‖ ^ m * ‖P m (W.erase i) z‖ +
                ((m : ℝ) + 2) * ‖z - i‖ ^ (m + 1) * ‖P1 m (W.erase i) z‖
              ≤ ((m : ℝ) + 2) * (m + 1) * 1 * 1 + ((m : ℝ) + 2) * 1 * ((m + 2) * W.card) := by
                gcongr
                exact h3.trans h5
            _ = _ := by ring
    _ = (m + 2) * (m + 1) * W.card + (m + 2) ^ 2 * W.card ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- `|P''_{m,W}(z) - (m+2)(m+1) ∑_{i ∈ W} (z - i)^m P_{m,W∖{i}}(z)| ≤ (m+2)² #W² |z - l|^{m+1}` for
`l ∈ W`. -/
theorem norm_P2_sub_le (hW : ∀ w ∈ W, ‖z - w‖ ≤ 1) {l : ℝ} (hl : l ∈ W) :
    ‖P2 m W z - ∑ i ∈ W, ((m + 2 : ℕ) : ℂ) * ((m + 1 : ℕ) : ℂ) * (z - i) ^ m * P m (W.erase i) z‖
      ≤ (m + 2) ^ 2 * W.card ^ 2 * ‖z - l‖ ^ (m + 1) := by
  rw [P2, ← Finset.sum_sub_distrib]
  simp only [add_sub_cancel_left]
  refine (norm_sum_le _ _).trans ?_
  have hl1 : ‖z - l‖ ≤ 1 := hW l hl
  calc ∑ i ∈ W, ‖((m + 2 : ℕ) : ℂ) * (z - i) ^ (m + 1) * P1 m (W.erase i) z‖
      ≤ ∑ _i ∈ W, ((m : ℝ) + 2) ^ 2 * W.card * ‖z - l‖ ^ (m + 1) :=
        Finset.sum_le_sum fun i hi => by
          rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
          push_cast
          have hWi : ∀ w ∈ W.erase i, ‖z - w‖ ≤ 1 :=
            fun w hw => hW w (Finset.mem_of_mem_erase hw)
          have h4 : ((W.erase i).card : ℝ) ≤ W.card := by
            exact_mod_cast Finset.card_erase_le
          by_cases hil : i = l
          · subst hil
            have h3 := norm_P1_le (m := m) hWi
            calc ((m : ℝ) + 2) * ‖z - i‖ ^ (m + 1) * ‖P1 m (W.erase i) z‖
                ≤ ((m : ℝ) + 2) * ‖z - i‖ ^ (m + 1) * ((m + 2) * W.card) := by
                  gcongr
                  exact h3.trans (by gcongr)
              _ = _ := by ring
          · have h1 : ‖z - i‖ ^ (m + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) (hW i hi)
            have h3 := norm_P1_le_of_mem (m := m) hWi (Finset.mem_erase.2 ⟨Ne.symm hil, hl⟩)
            calc ((m : ℝ) + 2) * ‖z - i‖ ^ (m + 1) * ‖P1 m (W.erase i) z‖
                ≤ ((m : ℝ) + 2) * 1 * ((m + 2) * W.card * ‖z - l‖ ^ (m + 1)) := by
                  gcongr
                  exact h3.trans (by gcongr)
              _ = _ := by ring
    _ = (m + 2) ^ 2 * W.card ^ 2 * ‖z - l‖ ^ (m + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

end Bounds

/-! ## The Gaussian sum `A` -/

/-- `A(z) = ∑_{y ∈ 𝒴} a_y e^{-(z - y)²/η}`. -/
noncomputable def A (a : ℝ → ℝ) (Y : Finset ℝ) (η : ℝ) (z : ℂ) : ℂ :=
  ∑ k ∈ Y, (a k : ℂ) * Complex.exp (-(z - k) ^ 2 / η)

/-- `A'(z) = ∑_{y ∈ 𝒴} a_y (-2 (z - y)/η) e^{-(z - y)²/η}`. -/
noncomputable def A1 (a : ℝ → ℝ) (Y : Finset ℝ) (η : ℝ) (z : ℂ) : ℂ :=
  ∑ k ∈ Y, (a k : ℂ) * (-2 * (z - k) / η) * Complex.exp (-(z - k) ^ 2 / η)

/-- `A''(z) = ∑_{y ∈ 𝒴} a_y · 2 (2 (z - y)²/η² - 1/η) e^{-(z - y)²/η}`. -/
noncomputable def A2 (a : ℝ → ℝ) (Y : Finset ℝ) (η : ℝ) (z : ℂ) : ℂ :=
  ∑ k ∈ Y, (a k : ℂ) * (2 * (2 * (z - k) ^ 2 / η ^ 2 - 1 / η)) * Complex.exp (-(z - k) ^ 2 / η)

/-- The derivative of the Gaussian `e^{-(z - y)²/η}`. -/
theorem hasDerivAt_gaussian (k η : ℝ) (z : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (-(z - k) ^ 2 / η))
      (-2 * (z - k) / η * Complex.exp (-(z - k) ^ 2 / η)) z := by
  have h := ((((hasDerivAt_id' z).sub_const (k : ℂ)).fun_pow 2).neg.div_const (η : ℂ)).cexp
  refine h.congr_deriv ?_
  norm_num
  ring

/-- `A'` is the derivative of `A`. -/
theorem hasDerivAt_A (a : ℝ → ℝ) (Y : Finset ℝ) (η : ℝ) (z : ℂ) :
    HasDerivAt (A a Y η) (A1 a Y η z) z := by
  have h := HasDerivAt.fun_sum (u := Y)
    (A := fun k z => (a k : ℂ) * Complex.exp (-(z - k) ^ 2 / η)) (x := z)
    fun k _ => (hasDerivAt_gaussian k η z).const_mul (a k : ℂ)
  refine h.congr_deriv (Finset.sum_congr rfl fun k _ => ?_)
  ring

/-- `A''` is the derivative of `A'`. -/
theorem hasDerivAt_A1 (a : ℝ → ℝ) (Y : Finset ℝ) (η : ℝ) (z : ℂ) :
    HasDerivAt (A1 a Y η) (A2 a Y η z) z := by
  have h := HasDerivAt.fun_sum (u := Y)
    (A := fun k z => (a k : ℂ) * (-2 * (z - k) / η) * Complex.exp (-(z - k) ^ 2 / η))
    (x := z) fun k _ =>
      ((((hasDerivAt_id' z).sub_const (k : ℂ)).const_mul (-2 : ℂ)).div_const (η : ℂ)
        |>.const_mul (a k : ℂ)).mul (hasDerivAt_gaussian k η z)
  refine h.congr_deriv (Finset.sum_congr rfl fun k _ => ?_)
  ring

/-! ## The exponent `h = φ ψ A` and its derivatives -/

/-- The exponent `h = φ ψ A` with `φ = P_{0,𝒴}` and `ψ = P_{2,𝒵}`. -/
noncomputable def H (Y Z : Finset ℝ) (a : ℝ → ℝ) (η : ℝ) (z : ℂ) : ℂ :=
  P 0 Y z * P 2 Z z * A a Y η z

/-- `h' = φ' ψ A + φ ψ' A + φ ψ A'`. -/
noncomputable def H1 (Y Z : Finset ℝ) (a : ℝ → ℝ) (η : ℝ) (z : ℂ) : ℂ :=
  P1 0 Y z * P 2 Z z * A a Y η z + P 0 Y z * P1 2 Z z * A a Y η z +
    P 0 Y z * P 2 Z z * A1 a Y η z

/-- `h'' = φ'' ψ A + φ ψ'' A + φ ψ A'' + 2 φ' ψ' A + 2 φ' ψ A' + 2 φ ψ' A'`. -/
noncomputable def H2 (Y Z : Finset ℝ) (a : ℝ → ℝ) (η : ℝ) (z : ℂ) : ℂ :=
  P2 0 Y z * P 2 Z z * A a Y η z + P 0 Y z * P2 2 Z z * A a Y η z +
    P 0 Y z * P 2 Z z * A2 a Y η z + 2 * (P1 0 Y z * P1 2 Z z * A a Y η z) +
    2 * (P1 0 Y z * P 2 Z z * A1 a Y η z) + 2 * (P 0 Y z * P1 2 Z z * A1 a Y η z)

/-- `h'` is the derivative of `h`. -/
theorem hasDerivAt_H (Y Z : Finset ℝ) (a : ℝ → ℝ) (η : ℝ) (z : ℂ) :
    HasDerivAt (H Y Z a η) (H1 Y Z a η z) z := by
  have h := ((hasDerivAt_P 0 Y z).fun_mul (hasDerivAt_P 2 Z z)).fun_mul (hasDerivAt_A a Y η z)
  refine h.congr_deriv ?_
  simp only [H1]
  ring

/-- `h''` is the derivative of `h'`. -/
theorem hasDerivAt_H1 (Y Z : Finset ℝ) (a : ℝ → ℝ) (η : ℝ) (z : ℂ) :
    HasDerivAt (H1 Y Z a η) (H2 Y Z a η z) z := by
  have h1 := ((hasDerivAt_P1 0 Y z).fun_mul (hasDerivAt_P 2 Z z)).fun_mul (hasDerivAt_A a Y η z)
  have h2 := ((hasDerivAt_P 0 Y z).fun_mul (hasDerivAt_P1 2 Z z)).fun_mul (hasDerivAt_A a Y η z)
  have h3 := ((hasDerivAt_P 0 Y z).fun_mul (hasDerivAt_P 2 Z z)).fun_mul (hasDerivAt_A1 a Y η z)
  refine ((h1.fun_add h2).fun_add h3).congr_deriv ?_
  simp only [H2]
  ring

/-- `h` is entire. -/
theorem differentiable_H (Y Z : Finset ℝ) (a : ℝ → ℝ) (η : ℝ) : Differentiable ℂ (H Y Z a η) :=
  fun z => (hasDerivAt_H Y Z a η z).differentiableAt

/-! ## Values at real points -/

/-- `P_{m,W}` is real at real points. -/
theorem P_ofReal (m : ℕ) (W : Finset ℝ) (x : ℝ) :
    P m W x = ((∏ w ∈ W, (x - w) ^ (m + 2) : ℝ) : ℂ) := by
  simp [P]

/-- `A` is real at real points. -/
theorem A_ofReal (a : ℝ → ℝ) (Y : Finset ℝ) (η x : ℝ) :
    A a Y η x = ((∑ k ∈ Y, a k * Real.exp (-(x - k) ^ 2 / η) : ℝ) : ℂ) := by
  simp [A, Complex.ofReal_exp]

/-- `h` is real at real points. -/
theorem im_H_ofReal (Y Z : Finset ℝ) (a : ℝ → ℝ) (η x : ℝ) : (H Y Z a η x).im = 0 := by
  rw [H, P_ofReal, P_ofReal, A_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    Complex.ofReal_im]

/-- `|x - w|` for real `x` and `w`. -/
theorem norm_ofReal_sub (x w : ℝ) : ‖(x : ℂ) - w‖ = |x - w| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- `|e^{-(x - y)²/η}| = e^{-(x - y)²/η}` at real points. -/
theorem norm_gaussian (x k η : ℝ) :
    ‖Complex.exp (-((x : ℂ) - k) ^ 2 / η)‖ = Real.exp (-(x - k) ^ 2 / η) := by
  rw [show -((x : ℂ) - k) ^ 2 / η = ((-(x - k) ^ 2 / η : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_exp_ofReal]

/-! ## The map `g = f e^{φ ψ A}` -/

/-- The perturbed map `g = f e^{φ ψ A}` of (4.2). -/
noncomputable def G (f : ℂ → ℂ) (Y Z : Finset ℝ) (a : ℝ → ℝ) (η : ℝ) (z : ℂ) : ℂ :=
  f z * Complex.exp (H Y Z a η z)

section Map

variable {f : ℂ → ℂ} {Y Z : Finset ℝ} {a : ℝ → ℝ} {η : ℝ}

/-- `g' = (f' + f h') e^h` where `f` is differentiable. -/
theorem hasDerivAt_G {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    HasDerivAt (G f Y Z a η) ((deriv f z + f z * H1 Y Z a η z) * Complex.exp (H Y Z a η z)) z := by
  refine (hf.hasDerivAt.fun_mul (hasDerivAt_H Y Z a η z).cexp).congr_deriv ?_
  ring

/-- On an open set on which `f` is holomorphic, `g' = (f' + f h') e^h` and
`g'' = (f'' + 2 f' h' + f h'² + f h'') e^h`. -/
theorem deriv_G {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {z : ℂ} (hz : z ∈ U) :
    deriv (G f Y Z a η) z = (deriv f z + f z * H1 Y Z a η z) * Complex.exp (H Y Z a η z) ∧
      deriv (deriv (G f Y Z a η)) z = (deriv (deriv f) z + 2 * deriv f z * H1 Y Z a η z +
        f z * H1 Y Z a η z ^ 2 + f z * H2 Y Z a η z) * Complex.exp (H Y Z a η z) := by
  have h1 : ∀ w ∈ U, deriv (G f Y Z a η) w =
      (deriv f w + f w * H1 Y Z a η w) * Complex.exp (H Y Z a η w) :=
    fun w hw => (hasDerivAt_G (hf.differentiableAt (hU.mem_nhds hw))).deriv
  refine ⟨h1 z hz, ?_⟩
  have heq : deriv (G f Y Z a η) =ᶠ[𝓝 z]
      fun w => (deriv f w + f w * H1 Y Z a η w) * Complex.exp (H Y Z a η w) :=
    Filter.eventually_of_mem (hU.mem_nhds hz) h1
  rw [heq.deriv_eq]
  have hf1 : DifferentiableAt ℂ (deriv f) z := (hf.deriv hU).differentiableAt (hU.mem_nhds hz)
  have hfz : DifferentiableAt ℂ f z := hf.differentiableAt (hU.mem_nhds hz)
  have h := (hf1.hasDerivAt.fun_add (hfz.hasDerivAt.fun_mul (hasDerivAt_H1 Y Z a η z))).fun_mul
    (hasDerivAt_H Y Z a η z).cexp
  rw [h.deriv]
  ring

/-- `h = h' = 0` on `𝒴`. -/
theorem H_of_mem_Y {y : ℝ} (hy : y ∈ Y) : H Y Z a η y = 0 ∧ H1 Y Z a η y = 0 := by
  simp [H, H1, P_of_mem 0 hy, P1_of_mem 0 hy]

/-- `h''(y) = 2 ∏_{y' ≠ y} (y - y')² ψ(y) A(y)` for `y ∈ 𝒴`. -/
theorem H2_of_mem_Y {y : ℝ} (hy : y ∈ Y) :
    H2 Y Z a η y = 2 * P 0 (Y.erase y) y * P 2 Z y * A a Y η y := by
  simp [H2, P_of_mem 0 hy, P1_of_mem 0 hy, P2_of_mem 0 hy]

/-- `h = h' = h'' = 0` on `𝒵`. -/
theorem H_of_mem_Z {w : ℝ} (hw : w ∈ Z) :
    H Y Z a η w = 0 ∧ H1 Y Z a η w = 0 ∧ H2 Y Z a η w = 0 := by
  simp [H, H1, H2, P_of_mem 2 hw, P1_of_mem 2 hw, P2_of_mem 2 hw]

end Map

/-! ## Elementary bounds -/

/-- `t e^{-t} ≤ 1`. -/
theorem mul_exp_neg_le_one (t : ℝ) : t * Real.exp (-t) ≤ 1 := by
  have h := Real.add_one_le_exp t
  have h2 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc t * Real.exp (-t) ≤ Real.exp t * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ = 1 := h2

/-- `t² e^{-t} ≤ 2` for `t ≥ 0`. -/
theorem sq_mul_exp_neg_le_two {t : ℝ} (ht : 0 ≤ t) : t ^ 2 * Real.exp (-t) ≤ 2 := by
  have h := Real.quadratic_le_exp_of_nonneg ht
  have h2 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc t ^ 2 * Real.exp (-t) ≤ (2 * Real.exp t) * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ = 2 := by rw [mul_assoc, h2, mul_one]

/-- `e^{-t} = e^{-t/2} e^{-t/2}`. -/
theorem exp_neg_eq_sq_half (t : ℝ) : Real.exp (-t) = Real.exp (-(t / 2)) * Real.exp (-(t / 2)) := by
  rw [← Real.exp_add]
  ring_nf

/-- `t e^{-t} ≤ 2 e^{-t/2}`. -/
theorem mul_exp_neg_le_half (t : ℝ) :
    t * Real.exp (-t) ≤ 2 * Real.exp (-(t / 2)) := by
  have h := mul_exp_neg_le_one (t / 2)
  calc t * Real.exp (-t) = 2 * (t / 2 * Real.exp (-(t / 2))) * Real.exp (-(t / 2)) := by
        rw [exp_neg_eq_sq_half]; ring
    _ ≤ 2 * 1 * Real.exp (-(t / 2)) := by gcongr
    _ = 2 * Real.exp (-(t / 2)) := by ring

/-- `t² e^{-t} ≤ 8 e^{-t/2}` for `t ≥ 0`. -/
theorem sq_mul_exp_neg_le_half {t : ℝ} (ht : 0 ≤ t) :
    t ^ 2 * Real.exp (-t) ≤ 8 * Real.exp (-(t / 2)) := by
  have h := sq_mul_exp_neg_le_two (t := t / 2) (by positivity)
  calc t ^ 2 * Real.exp (-t) = 4 * ((t / 2) ^ 2 * Real.exp (-(t / 2))) * Real.exp (-(t / 2)) := by
        rw [exp_neg_eq_sq_half]; ring
    _ ≤ 4 * 2 * Real.exp (-(t / 2)) := by gcongr
    _ = 8 * Real.exp (-(t / 2)) := by ring

/-- The profile `|4t² - 2t| e^{-t}` of the term `φ ψ A''` near a point of `𝒴`. -/
theorem abs_mul_exp_neg_le {t : ℝ} (ht : 0 ≤ t) :
    |4 * t ^ 2 - 2 * t| * Real.exp (-t) ≤ 10 ∧
      |4 * t ^ 2 - 2 * t| * Real.exp (-t) ≤ 36 * Real.exp (-(t / 2)) := by
  have habs : |4 * t ^ 2 - 2 * t| ≤ 4 * t ^ 2 + 2 * t := by
    rw [abs_le]; constructor <;> nlinarith
  have he := (Real.exp_pos (-t)).le
  have h1 := mul_exp_neg_le_one t
  have h2 := sq_mul_exp_neg_le_two ht
  have h3 := mul_exp_neg_le_half t
  have h4 := sq_mul_exp_neg_le_half ht
  have hb : |4 * t ^ 2 - 2 * t| * Real.exp (-t) ≤
      4 * (t ^ 2 * Real.exp (-t)) + 2 * (t * Real.exp (-t)) := by
    calc |4 * t ^ 2 - 2 * t| * Real.exp (-t) ≤ (4 * t ^ 2 + 2 * t) * Real.exp (-t) :=
          mul_le_mul_of_nonneg_right habs he
      _ = _ := by ring
  constructor <;> linarith

/-! ## Splitting a sum near and far from the points of `𝒴` -/

/-- The near/far split. Let the points of `𝒴` be `2ρ`-separated, and let `w_y ≤ a_y` and
`0 ≤ F_y ≤ K` for every `y`, `w_y ≤ B` if `|x - y| < ρ`, and `F_y ≤ b` if
`|x - y| ≥ ρ`. Then `∑_y w_y F_y ≤ K B + b ∑_y a_y`: at most one point of `𝒴` is near `x`. -/
theorem sum_le_near_far {Y : Finset ℝ} {x ρ B K b : ℝ} {w a F : ℝ → ℝ}
    (hsep : ∀ k ∈ Y, ∀ k' ∈ Y, k ≠ k' → 2 * ρ < |k - k'|) (hB : 0 ≤ B) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (ha : ∀ k ∈ Y, 0 ≤ a k) (hwa : ∀ k ∈ Y, w k ≤ a k)
    (hwB : ∀ k ∈ Y, |x - k| < ρ → w k ≤ B) (hF0 : ∀ k ∈ Y, 0 ≤ F k) (hFK : ∀ k ∈ Y, F k ≤ K)
    (hFb : ∀ k ∈ Y, ρ ≤ |x - k| → F k ≤ b) :
    ∑ k ∈ Y, w k * F k ≤ K * B + (∑ k ∈ Y, a k) * b := by
  have hcard : (Y.filter fun k => |x - k| < ρ).card ≤ 1 := by
    refine Finset.card_le_one.2 fun k hk k' hk' => ?_
    obtain ⟨hkY, hxk⟩ := Finset.mem_filter.1 hk
    obtain ⟨hk'Y, hxk'⟩ := Finset.mem_filter.1 hk'
    by_contra hne
    have h1 := hsep k hkY k' hk'Y hne
    have h2 : |k - k'| ≤ |k - x| + |x - k'| := abs_sub_le k x k'
    rw [abs_sub_comm k x] at h2
    linarith
  have hnear : ∀ k ∈ Y.filter fun k => |x - k| < ρ, w k * F k ≤ K * B := fun k hk => by
    obtain ⟨hkY, hxk⟩ := Finset.mem_filter.1 hk
    calc w k * F k ≤ B * K := mul_le_mul (hwB k hkY hxk) (hFK k hkY) (hF0 k hkY) hB
      _ = K * B := mul_comm _ _
  have hfar : ∀ k ∈ Y.filter fun k => ¬ |x - k| < ρ, w k * F k ≤ a k * b := fun k hk => by
    obtain ⟨hkY, hxk⟩ := Finset.mem_filter.1 hk
    exact mul_le_mul (hwa k hkY) (hFb k hkY (not_lt.1 hxk)) (hF0 k hkY) (ha k hkY)
  calc ∑ k ∈ Y, w k * F k
      = ∑ k ∈ Y with |x - k| < ρ, w k * F k + ∑ k ∈ Y with ¬ |x - k| < ρ, w k * F k :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ K * B + ∑ k ∈ Y, a k * b := by
        gcongr
        · calc ∑ k ∈ Y with |x - k| < ρ, w k * F k
              ≤ (Y.filter fun k => |x - k| < ρ).card • (K * B) :=
                Finset.sum_le_card_nsmul _ _ _ hnear
            _ ≤ 1 • (K * B) := by
                rw [nsmul_eq_mul, nsmul_eq_mul]
                exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (mul_nonneg hK hB)
            _ = K * B := one_nsmul _
        · calc ∑ k ∈ Y with ¬ |x - k| < ρ, w k * F k
              ≤ ∑ k ∈ Y with ¬ |x - k| < ρ, a k * b := Finset.sum_le_sum hfar
            _ ≤ ∑ k ∈ Y, a k * b :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                  fun k hk _ => mul_nonneg (ha k hk) hb
    _ = K * B + (∑ k ∈ Y, a k) * b := by rw [Finset.sum_mul]

/-! ## Small widths -/

/-- `σ = ρ³` is eventually below any positive threshold as `ρ → 0+`. -/
theorem eventually_pow_three_le {T : ℝ} (hT : 0 < T) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 < ρ ∧ ρ ^ 3 ≤ T := by
  have h : ∀ᶠ ρ in 𝓝 (0 : ℝ), ρ ^ 3 < T :=
    ((continuous_pow 3).tendsto (0 : ℝ)).eventually (gt_mem_nhds (by simpa using hT))
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h] with ρ hρ h3 using ⟨hρ, h3.le⟩

/-- The bound (4.3) with `p = 1`, `q = 0`, as used for `(C1)` and `(C3)`: for small `ρ`,
`c |u| e^{-u²/ρ³} ≤ ν` for every `u`. -/
theorem eventually_gauss_one {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ u : ℝ, c * |u| * Real.exp (-u ^ 2 / ρ ^ 3) ≤ ν := by
  have hT : 0 < (2 * Real.exp 1 / 1) ^ ((1 : ℝ) / (2 * 0 + 1)) *
      (ν / c) ^ (1 / ((0 : ℝ) + 1 / 2)) := by positivity
  filter_upwards [eventually_pow_three_le hT] with ρ ⟨hρ, hle⟩ u
  have h := gaussian_bound (p := 1) (q := 0) hc one_pos hν (by norm_num) (pow_pos hρ 3) hle u
  simpa using h

/-- The bound (4.3) with `p = 2`, `q = 0`, as used for `(C4)`. -/
theorem eventually_gauss_two {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ u : ℝ, c * |u| ^ 2 * Real.exp (-u ^ 2 / ρ ^ 3) ≤ ν := by
  have hT : 0 < (2 * Real.exp 1 / 2) ^ ((2 : ℝ) / (2 * 0 + 2)) *
      (ν / c) ^ (1 / ((0 : ℝ) + 2 / 2)) := by positivity
  filter_upwards [eventually_pow_three_le hT] with ρ ⟨hρ, hle⟩ u
  have h := gaussian_bound (p := 2) (q := 0) hc two_pos hν (by norm_num) (pow_pos hρ 3) hle u
  simpa using h

/-- The bound (4.3) with `p = 3`, `q = -1`, as used for `(C2)` and for the off-diagonal part of
`φ' ψ A'`. -/
theorem eventually_gauss_three {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ u : ℝ, c * |u| ^ 3 / ρ ^ 3 * Real.exp (-u ^ 2 / ρ ^ 3) ≤ ν := by
  have hT : 0 < (2 * Real.exp 1 / 3) ^ ((3 : ℝ) / (2 * -1 + 3)) *
      (ν / c) ^ (1 / ((-1 : ℝ) + 3 / 2)) := by positivity
  filter_upwards [eventually_pow_three_le hT] with ρ ⟨hρ, hle⟩ u
  have h := gaussian_bound (p := 3) (q := -1) hc (by norm_num) hν (by norm_num) (pow_pos hρ 3)
    hle u
  rw [Real.rpow_neg_one] at h
  have h3 : |u| ^ (3 : ℝ) = |u| ^ 3 := by exact_mod_cast Real.rpow_natCast |u| 3
  rw [h3] at h
  calc c * |u| ^ 3 / ρ ^ 3 * Real.exp (-u ^ 2 / ρ ^ 3) =
      c * (ρ ^ 3)⁻¹ * |u| ^ 3 * Real.exp (-u ^ 2 / ρ ^ 3) := by ring
    _ ≤ ν := h

/-- The far terms: `K e^{-c/ρ} ≤ ν` for small `ρ`. -/
theorem eventually_exp_neg_div_le (K : ℝ) {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), K * Real.exp (-(c / ρ)) ≤ ν := by
  have h1 : Tendsto (fun ρ : ℝ => c / ρ) (𝓝[>] 0) atTop := by
    simpa [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hc
  have h2 : Tendsto (fun ρ : ℝ => K * Real.exp (-(c / ρ))) (𝓝[>] 0) (𝓝 (K * 0)) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul K
  rw [mul_zero] at h2
  filter_upwards [h2.eventually (gt_mem_nhds hν)] with ρ hρ using hρ.le

/-- Small radii separate the points of a finite set: `2ρ < |y - y'|` for `y ≠ y'`. -/
theorem eventually_sep (Y : Finset ℝ) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ k ∈ Y, ∀ k' ∈ Y, k ≠ k' → 2 * ρ < |k - k'| := by
  refine (eventually_all_finset Y).2 fun k _ => (eventually_all_finset Y).2 fun k' _ => ?_
  by_cases hkk : k = k'
  · exact Eventually.of_forall fun _ h => absurd hkk h
  · have h : 0 < |k - k'| / 2 := by
      have := abs_pos.2 (sub_ne_zero.2 hkk)
      positivity
    filter_upwards [Ioo_mem_nhdsGT h] with ρ hρ _
    linarith [hρ.2]

/-- Near a point `y` with `F(y) ≠ 0`, `|F| ≤ 2 |F(y)|` for a continuous `F`. -/
theorem eventually_near {F : ℂ → ℂ} (hF : Continuous F) {y : ℝ} (hy : F y ≠ 0) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ x : ℝ, |x - y| < ρ → ‖F x‖ ≤ 2 * ‖F y‖ := by
  obtain ⟨r, hr, h⟩ := Metric.continuousAt_iff.1 hF.continuousAt (‖F y‖) (norm_pos_iff.2 hy)
  filter_upwards [Ioo_mem_nhdsGT hr] with ρ hρ x hx
  have hd : dist (x : ℂ) y < r := by
    rw [dist_eq_norm, norm_ofReal_sub]
    exact hx.trans hρ.2
  have h1 := h hd
  rw [dist_eq_norm] at h1
  have h2 := norm_sub_norm_le (F x) (F y)
  linarith

/-! ## The estimates on `[0,1]` -/

section Estimates

variable {Y Z : Finset ℝ} {a : ℝ → ℝ} {η x : ℝ}

/-- `|x - w| ≤ 1` for `x, w ∈ [0,1]`. -/
theorem norm_ofReal_sub_le_one {x w : ℝ} (hx : x ∈ I) (hw : w ∈ I) : ‖(x : ℂ) - w‖ ≤ 1 := by
  rw [norm_ofReal_sub, abs_le]
  constructor <;> linarith [hx.1, hx.2, hw.1, hw.2]

/-- `φ' = ∑_{y ∈ 𝒴} 2 (z - y) ∏_{y' ≠ y} (z - y')²`. -/
theorem P1_zero (W : Finset ℝ) (z : ℂ) : P1 0 W z = ∑ i ∈ W, 2 * (z - i) * P 0 (W.erase i) z := by
  simp only [P1]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-- The bound on `φ''` of the paper:
`|φ'' - 2 ∑_{y ∈ 𝒴} ∏_{y' ≠ y} (z - y')²| ≤ 4 M² |z - l|` for `l ∈ 𝒴`. -/
theorem norm_P2_zero_sub_le {W : Finset ℝ} {z : ℂ} (hW : ∀ w ∈ W, ‖z - w‖ ≤ 1) {l : ℝ}
    (hl : l ∈ W) : ‖P2 0 W z - 2 * ∑ i ∈ W, P 0 (W.erase i) z‖ ≤ 4 * W.card ^ 2 * ‖z - l‖ := by
  have h := norm_P2_sub_le (m := 0) hW hl
  have e : ∑ i ∈ W, ((0 + 2 : ℕ) : ℂ) * ((0 + 1 : ℕ) : ℂ) * (z - i) ^ 0 * P 0 (W.erase i) z =
      2 * ∑ i ∈ W, P 0 (W.erase i) z := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  rw [e] at h
  convert h using 1
  norm_num

/-- The products `∏_{y' ≠ y} (z - y')²` with `y ≠ k` contain the factor `(z - k)²`. -/
theorem sum_norm_P_erase_le {W : Finset ℝ} {z : ℂ} (hW : ∀ w ∈ W, ‖z - w‖ ≤ 1) {k : ℝ}
    (hk : k ∈ W) : ∑ i ∈ W.erase k, ‖P 0 (W.erase i) z‖ ≤ W.card * ‖z - k‖ ^ 2 := by
  calc ∑ i ∈ W.erase k, ‖P 0 (W.erase i) z‖ ≤ ∑ _i ∈ W.erase k, ‖z - k‖ ^ 2 :=
        Finset.sum_le_sum fun i hi => by
          have hki : k ∈ W.erase i := Finset.mem_erase.2 ⟨(Finset.ne_of_mem_erase hi).symm, hk⟩
          simpa using norm_P_le (m := 0) (fun w hw => hW w (Finset.mem_of_mem_erase hw)) hki
    _ ≤ W.card * ‖z - k‖ ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact Finset.erase_subset k W

/-- `|u A(x)| ≤ ∑_y a_y e^{-(x-y)²/η} v_y` if `|u| ≤ v_y` for every `y ∈ 𝒴`. -/
theorem norm_mul_A_le {u : ℂ} {v : ℝ → ℝ} (ha : ∀ k ∈ Y, 0 ≤ a k) (hu : ∀ k ∈ Y, ‖u‖ ≤ v k) :
    ‖u * A a Y η x‖ ≤ ∑ k ∈ Y, a k * Real.exp (-(x - k) ^ 2 / η) * v k := by
  rw [A, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha k hk), norm_gaussian]
  have := ha k hk
  calc ‖u‖ * (a k * Real.exp (-(x - k) ^ 2 / η)) ≤ v k * (a k * Real.exp (-(x - k) ^ 2 / η)) :=
        mul_le_mul_of_nonneg_right (hu k hk) (by positivity)
    _ = _ := by ring

/-- `|-2 (x - y)/η| = 2 |x - y|/η` at real points. -/
theorem norm_A1_coeff (hη : 0 < η) (x k : ℝ) :
    ‖(-2 * ((x : ℂ) - k) / η)‖ = 2 * |x - k| / η := by
  rw [show (-2 * ((x : ℂ) - k) / η) = ((-2 * (x - k) / η : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hη]
  norm_num

/-- `|u A'(x)| ≤ ∑_y a_y (2|x - y|/η) e^{-(x-y)²/η} v_y` if `|u| ≤ v_y` for every `y ∈ 𝒴`. -/
theorem norm_mul_A1_le {u : ℂ} {v : ℝ → ℝ} (hη : 0 < η) (ha : ∀ k ∈ Y, 0 ≤ a k)
    (hu : ∀ k ∈ Y, ‖u‖ ≤ v k) :
    ‖u * A1 a Y η x‖ ≤
      ∑ k ∈ Y, a k * (2 * |x - k| / η) * Real.exp (-(x - k) ^ 2 / η) * v k := by
  rw [A1, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha k hk),
    norm_gaussian, norm_A1_coeff hη]
  have := ha k hk
  calc ‖u‖ * (a k * (2 * |x - k| / η) * Real.exp (-(x - k) ^ 2 / η))
      ≤ v k * (a k * (2 * |x - k| / η) * Real.exp (-(x - k) ^ 2 / η)) :=
        mul_le_mul_of_nonneg_right (hu k hk) (by positivity)
    _ = _ := by ring

/-- A term `u A` with `|u| ≤ c |x - y|^p` for every `y ∈ 𝒴`, given the bound (4.3) in the form
`a_y |x - y|^p e^{-(x-y)²/η} ≤ ν`. -/
theorem norm_mul_A_le_of {u : ℂ} {c ν : ℝ} {p : ℕ} (hc : 0 ≤ c) (ha : ∀ k ∈ Y, 0 ≤ a k)
    (hu : ∀ k ∈ Y, ‖u‖ ≤ c * |x - k| ^ p)
    (hν : ∀ k ∈ Y, a k * |x - k| ^ p * Real.exp (-(x - k) ^ 2 / η) ≤ ν) :
    ‖u * A a Y η x‖ ≤ c * (Y.card * ν) := by
  refine (norm_mul_A_le ha hu).trans ?_
  calc ∑ k ∈ Y, a k * Real.exp (-(x - k) ^ 2 / η) * (c * |x - k| ^ p)
      = ∑ k ∈ Y, c * (a k * |x - k| ^ p * Real.exp (-(x - k) ^ 2 / η)) :=
        Finset.sum_congr rfl fun k _ => by ring
    _ ≤ ∑ _k ∈ Y, c * ν := Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hν k hk) hc
    _ = c * (Y.card * ν) := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- A term `u A'` with `|u| ≤ c |x - y|²` for every `y ∈ 𝒴`, given the bound (4.3) in the form
`a_y |x - y|³ η⁻¹ e^{-(x-y)²/η} ≤ ν`. -/
theorem norm_mul_A1_le_of {u : ℂ} {c ν : ℝ} (hη : 0 < η) (hc : 0 ≤ c) (ha : ∀ k ∈ Y, 0 ≤ a k)
    (hu : ∀ k ∈ Y, ‖u‖ ≤ c * |x - k| ^ 2)
    (hν : ∀ k ∈ Y, a k * |x - k| ^ 3 / η * Real.exp (-(x - k) ^ 2 / η) ≤ ν) :
    ‖u * A1 a Y η x‖ ≤ 2 * c * (Y.card * ν) := by
  refine (norm_mul_A1_le hη ha hu).trans ?_
  calc ∑ k ∈ Y, a k * (2 * |x - k| / η) * Real.exp (-(x - k) ^ 2 / η) * (c * |x - k| ^ 2)
      = ∑ k ∈ Y, 2 * c * (a k * |x - k| ^ 3 / η * Real.exp (-(x - k) ^ 2 / η)) :=
        Finset.sum_congr rfl fun k _ => by ring
    _ ≤ ∑ _k ∈ Y, 2 * c * ν :=
        Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hν k hk) (by positivity)
    _ = 2 * c * (Y.card * ν) := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- The term `φ'' ψ A`: the bound on `φ''`, `(C3)` and `(C4)` reduce it to
`I(x) = 2 ψ(x) ∑_y a_y e^{-(x-y)²/η} ∏_{y' ≠ y} (x - y')²`. -/
theorem norm_P2_mul_A_le (hY : ∀ y ∈ Y, y ∈ I) (hZ : ∀ w ∈ Z, w ∈ I) (hx : x ∈ I)
    (ha : ∀ k ∈ Y, 0 ≤ a k) {ν : ℝ}
    (h1 : ∀ k ∈ Y, a k * |x - k| ^ 1 * Real.exp (-(x - k) ^ 2 / η) ≤ ν)
    (h2 : ∀ k ∈ Y, a k * |x - k| ^ 2 * Real.exp (-(x - k) ^ 2 / η) ≤ ν) :
    ‖P2 0 Y x * P 2 Z x * A a Y η x‖ ≤ 4 * Y.card ^ 2 * (Y.card * ν) + 2 * Y.card * (Y.card * ν) +
      ∑ k ∈ Y, a k * ‖P 2 Z x * P 0 (Y.erase k) x‖ * (2 * Real.exp (-(x - k) ^ 2 / η)) := by
  have hYx : ∀ w ∈ Y, ‖(x : ℂ) - w‖ ≤ 1 := fun w hw => norm_ofReal_sub_le_one hx (hY w hw)
  have hZx : ∀ w ∈ Z, ‖(x : ℂ) - w‖ ≤ 1 := fun w hw => norm_ofReal_sub_le_one hx (hZ w hw)
  have hψ : ‖P 2 Z x‖ ≤ 1 := norm_P_le_one hZx
  have hsplit : P2 0 Y x * P 2 Z x * A a Y η x =
      ((P2 0 Y x - 2 * ∑ i ∈ Y, P 0 (Y.erase i) x) * P 2 Z x) * A a Y η x +
        (P 2 Z x * (2 * ∑ i ∈ Y, P 0 (Y.erase i) x)) * A a Y η x := by ring
  have hR : ‖((P2 0 Y x - 2 * ∑ i ∈ Y, P 0 (Y.erase i) x) * P 2 Z x) * A a Y η x‖ ≤
      4 * Y.card ^ 2 * (Y.card * ν) := by
    refine norm_mul_A_le_of (p := 1) (by positivity) ha (fun k hk => ?_) h1
    rw [norm_mul, pow_one]
    have := norm_P2_zero_sub_le hYx hk
    rw [norm_ofReal_sub] at this
    calc _ ≤ 4 * Y.card ^ 2 * |x - k| * 1 := mul_le_mul this hψ (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hD : ‖(P 2 Z x * (2 * ∑ i ∈ Y, P 0 (Y.erase i) x)) * A a Y η x‖ ≤
      ∑ k ∈ Y, a k * Real.exp (-(x - k) ^ 2 / η) *
        (2 * ‖P 2 Z x * P 0 (Y.erase k) x‖ + 2 * Y.card * |x - k| ^ 2) := by
    refine norm_mul_A_le ha fun k hk => ?_
    have e := (Finset.add_sum_erase Y (fun i => P 0 (Y.erase i) (x : ℂ)) hk).symm
    rw [e, mul_add, mul_add]
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
    · rw [show P 2 Z x * (2 * P 0 (Y.erase k) x) = 2 * (P 2 Z x * P 0 (Y.erase k) x) by ring,
        norm_mul, Complex.norm_two]
    · have h3 := sum_norm_P_erase_le hYx hk
      rw [norm_ofReal_sub, sq_abs] at h3
      calc ‖P 2 Z x * (2 * ∑ i ∈ Y.erase k, P 0 (Y.erase i) x)‖
          ≤ 1 * (2 * ∑ i ∈ Y.erase k, ‖P 0 (Y.erase i) x‖) := by
            rw [norm_mul, norm_mul, Complex.norm_two]
            gcongr
            exact norm_sum_le _ _
        _ ≤ 1 * (2 * (Y.card * (x - k) ^ 2)) := by gcongr
        _ = 2 * Y.card * |x - k| ^ 2 := by rw [sq_abs]; ring
  have hS : ∑ k ∈ Y, a k * Real.exp (-(x - k) ^ 2 / η) *
      (2 * ‖P 2 Z x * P 0 (Y.erase k) x‖ + 2 * Y.card * |x - k| ^ 2) ≤
      2 * Y.card * (Y.card * ν) +
        ∑ k ∈ Y, a k * ‖P 2 Z x * P 0 (Y.erase k) x‖ * (2 * Real.exp (-(x - k) ^ 2 / η)) := by
    calc _ = ∑ k ∈ Y, a k * ‖P 2 Z x * P 0 (Y.erase k) x‖ * (2 * Real.exp (-(x - k) ^ 2 / η)) +
          ∑ k ∈ Y, 2 * Y.card * (a k * |x - k| ^ 2 * Real.exp (-(x - k) ^ 2 / η)) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ ∑ k ∈ Y, a k * ‖P 2 Z x * P 0 (Y.erase k) x‖ * (2 * Real.exp (-(x - k) ^ 2 / η)) +
          ∑ _k ∈ Y, 2 * Y.card * ν := by
          gcongr with k hk
          exact h2 k hk
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [hsplit]
  linarith [norm_add_le (((P2 0 Y x - 2 * ∑ i ∈ Y, P 0 (Y.erase i) x) * P 2 Z x) * A a Y η x)
    ((P 2 Z x * (2 * ∑ i ∈ Y, P 0 (Y.erase i) x)) * A a Y η x)]

/-- The term `φ ψ A''`: with `t = (x - y)²/η`, the summand of `y` is
`a_y ψ(x) ∏_{y' ≠ y} (x - y')² (4t² - 2t) e^{-t}`. -/
theorem norm_P_mul_A2_le (ha : ∀ k ∈ Y, 0 ≤ a k) :
    ‖P 0 Y x * P 2 Z x * A2 a Y η x‖ ≤
      ∑ k ∈ Y, a k * ‖P 2 Z x * P 0 (Y.erase k) x‖ *
        (|4 * ((x - k) ^ 2 / η) ^ 2 - 2 * ((x - k) ^ 2 / η)| * Real.exp (-((x - k) ^ 2 / η))) := by
  rw [A2, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k hk => ?_))
  rw [P_eq_mul (m := 0) hk]
  calc _ = ‖(a k : ℂ) * (P 2 Z x * P 0 (Y.erase k) x) *
        ((4 * ((x - k) ^ 2 / η) ^ 2 - 2 * ((x - k) ^ 2 / η) : ℝ) : ℂ) *
        Complex.exp (-((x : ℂ) - k) ^ 2 / η)‖ := by
        congr 1
        push_cast
        ring
    _ = _ := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg (ha k hk), Real.norm_eq_abs, norm_gaussian, neg_div]
        ring

/-- The term `φ' ψ A'`: the diagonal part is `-4 a_y ψ(x) ∏_{y' ≠ y} (x - y')² t e^{-t}` with
`t = (x - y)²/η`, the rest is bounded by (4.3) with `p = 3`, `q = -1`, as in `(C2)`. -/
theorem norm_P1_mul_A1_le (hY : ∀ y ∈ Y, y ∈ I) (hZ : ∀ w ∈ Z, w ∈ I) (hx : x ∈ I)
    (hη : 0 < η) (ha : ∀ k ∈ Y, 0 ≤ a k) {ν : ℝ}
    (h3 : ∀ k ∈ Y, a k * |x - k| ^ 3 / η * Real.exp (-(x - k) ^ 2 / η) ≤ ν) :
    ‖P1 0 Y x * P 2 Z x * A1 a Y η x‖ ≤ 4 * Y.card * (Y.card * ν) +
      ∑ k ∈ Y, a k * ‖P 2 Z x * P 0 (Y.erase k) x‖ *
        (4 * ((x - k) ^ 2 / η) * Real.exp (-((x - k) ^ 2 / η))) := by
  have hYx : ∀ w ∈ Y, ‖(x : ℂ) - w‖ ≤ 1 := fun w hw => norm_ofReal_sub_le_one hx (hY w hw)
  have hZx : ∀ w ∈ Z, ‖(x : ℂ) - w‖ ≤ 1 := fun w hw => norm_ofReal_sub_le_one hx (hZ w hw)
  have hψ : ‖P 2 Z x‖ ≤ 1 := norm_P_le_one hZx
  rw [A1, Finset.mul_sum]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k ∈ Y, ‖P1 0 Y x * P 2 Z x *
      ((a k : ℂ) * (-2 * ((x : ℂ) - k) / η) * Complex.exp (-((x : ℂ) - k) ^ 2 / η))‖ ≤
      a k * ‖P 2 Z x * P 0 (Y.erase k) x‖ *
        (4 * ((x - k) ^ 2 / η) * Real.exp (-((x - k) ^ 2 / η))) + 4 * Y.card * ν := by
    intro k hk
    have e := (Finset.add_sum_erase Y (fun i => 2 * ((x : ℂ) - i) * P 0 (Y.erase i) x) hk).symm
    rw [P1_zero, e]
    have hsplit : (2 * ((x : ℂ) - k) * P 0 (Y.erase k) x +
        ∑ i ∈ Y.erase k, 2 * ((x : ℂ) - i) * P 0 (Y.erase i) x) * P 2 Z x *
        ((a k : ℂ) * (-2 * ((x : ℂ) - k) / η) * Complex.exp (-((x : ℂ) - k) ^ 2 / η)) =
        (a k : ℂ) * (P 2 Z x * P 0 (Y.erase k) x) * ((-4 * ((x - k) ^ 2 / η) : ℝ) : ℂ) *
          Complex.exp (-((x : ℂ) - k) ^ 2 / η) +
        ((a k : ℂ) * (-2 * ((x : ℂ) - k) / η) * Complex.exp (-((x : ℂ) - k) ^ 2 / η)) *
          (P 2 Z x * ∑ i ∈ Y.erase k, 2 * ((x : ℂ) - i) * P 0 (Y.erase i) x) := by
      push_cast
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
    · rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (ha k hk), Real.norm_eq_abs, norm_gaussian, neg_div,
        abs_of_nonpos (by have : 0 ≤ (x - k) ^ 2 / η := by positivity
                          linarith)]
      ring
    · have hR : ‖P 2 Z x * ∑ i ∈ Y.erase k, 2 * ((x : ℂ) - i) * P 0 (Y.erase i) x‖ ≤
          2 * Y.card * |x - k| ^ 2 := by
        have h4 := sum_norm_P_erase_le hYx hk
        rw [norm_ofReal_sub] at h4
        calc _ ≤ 1 * ∑ i ∈ Y.erase k, 2 * 1 * ‖P 0 (Y.erase i) x‖ := by
              rw [norm_mul]
              gcongr
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
              rw [norm_mul, norm_mul, Complex.norm_two]
              gcongr
              exact hYx i (Finset.mem_of_mem_erase hi)
          _ = 2 * ∑ i ∈ Y.erase k, ‖P 0 (Y.erase i) x‖ := by
              rw [one_mul, Finset.mul_sum]
              simp only [mul_one]
          _ ≤ 2 * (Y.card * |x - k| ^ 2) := by gcongr
          _ = _ := by ring
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha k hk),
        norm_gaussian, norm_A1_coeff hη]
      have hak := ha k hk
      calc a k * (2 * |x - k| / η) * Real.exp (-(x - k) ^ 2 / η) *
            ‖P 2 Z x * ∑ i ∈ Y.erase k, 2 * ((x : ℂ) - i) * P 0 (Y.erase i) x‖
          ≤ a k * (2 * |x - k| / η) * Real.exp (-(x - k) ^ 2 / η) * (2 * Y.card * |x - k| ^ 2) := by
            gcongr
        _ = 4 * Y.card * (a k * |x - k| ^ 3 / η * Real.exp (-(x - k) ^ 2 / η)) := by ring
        _ ≤ 4 * Y.card * ν := by gcongr; exact h3 k hk
  calc _ ≤ ∑ k ∈ Y, (a k * ‖P 2 Z x * P 0 (Y.erase k) x‖ *
        (4 * ((x - k) ^ 2 / η) * Real.exp (-((x - k) ^ 2 / η))) + 4 * Y.card * ν) :=
        Finset.sum_le_sum hterm
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]; ring

/-- Points at distance at least `ρ` from `y` have `t = (x - y)²/ρ³ ≥ 1/ρ`. -/
theorem one_div_le_of_le_abs {ρ x k : ℝ} (hρ : 0 < ρ) (h : ρ ≤ |x - k|) :
    1 / ρ ≤ (x - k) ^ 2 / ρ ^ 3 := by
  have h2 : ρ ^ 2 ≤ (x - k) ^ 2 := by
    have := pow_le_pow_left₀ hρ.le h 2
    rwa [sq_abs] at this
  rw [div_le_div_iff₀ hρ (pow_pos hρ 3)]
  nlinarith

/-- The near/far split for the three norms `‖φ'' ψ A‖`, `‖φ ψ A''‖` and `‖φ' ψ A'‖`: with
`t = (x - y)²/ρ³`, the summand of `y` carries the weight `a_y |ψ(x) ∏_{y' ≠ y} (x - y')²|`, which
is at most `B` near `y`, and the profiles `2 e^{-t}`, `|4t² - 2t| e^{-t}` and `4t e^{-t}`, which
are bounded by `2`, `10` and `4` and are exponentially small far from `y`. -/
theorem sum_near_far_le (hY : ∀ y ∈ Y, y ∈ I) (hx : x ∈ I) {ρ B : ℝ} (hρ : 0 < ρ)
    (ha : ∀ k ∈ Y, 0 ≤ a k) (hB : 0 ≤ B) (hψ : ‖P 2 Z x‖ ≤ 1)
    (hsep : ∀ k ∈ Y, ∀ k' ∈ Y, k ≠ k' → 2 * ρ < |k - k'|)
    (hnear : ∀ k ∈ Y, |x - k| < ρ → a k * ‖P 2 Z x * P 0 (Y.erase k) x‖ ≤ B) :
    ∑ k ∈ Y, a k * ‖P 2 Z x * P 0 (Y.erase k) x‖ * (2 * Real.exp (-(x - k) ^ 2 / ρ ^ 3)) +
      ∑ k ∈ Y, a k * ‖P 2 Z x * P 0 (Y.erase k) x‖ *
        (|4 * ((x - k) ^ 2 / ρ ^ 3) ^ 2 - 2 * ((x - k) ^ 2 / ρ ^ 3)| *
          Real.exp (-((x - k) ^ 2 / ρ ^ 3))) +
      2 * ∑ k ∈ Y, a k * ‖P 2 Z x * P 0 (Y.erase k) x‖ *
        (4 * ((x - k) ^ 2 / ρ ^ 3) * Real.exp (-((x - k) ^ 2 / ρ ^ 3))) ≤
      20 * B + (∑ k ∈ Y, a k) * (2 * Real.exp (-(1 / ρ)) + 52 * Real.exp (-(1 / ρ / 2))) := by
  have hYx : ∀ w ∈ Y, ‖(x : ℂ) - w‖ ≤ 1 := fun w hw => norm_ofReal_sub_le_one hx (hY w hw)
  have hwa : ∀ k ∈ Y, a k * ‖P 2 Z x * P 0 (Y.erase k) x‖ ≤ a k := fun k hk => by
    have h := norm_P_le_one (m := 0) (W := Y.erase k) (z := x)
      fun w hw => hYx w (Finset.mem_of_mem_erase hw)
    have := ha k hk
    rw [norm_mul]
    calc a k * (‖P 2 Z x‖ * ‖P 0 (Y.erase k) x‖) ≤ a k * (1 * 1) := by gcongr
      _ = a k := by ring
  have ht0 : ∀ k : ℝ, 0 ≤ (x - k) ^ 2 / ρ ^ 3 := fun k => by positivity
  have n1 : ∑ k ∈ Y, a k * ‖P 2 Z x * P 0 (Y.erase k) x‖ *
      (2 * Real.exp (-(x - k) ^ 2 / ρ ^ 3)) ≤
      2 * B + (∑ k ∈ Y, a k) * (2 * Real.exp (-(1 / ρ))) := by
    refine sum_le_near_far (w := fun k => a k * ‖P 2 Z x * P 0 (Y.erase k) x‖)
      (F := fun k => 2 * Real.exp (-(x - k) ^ 2 / ρ ^ 3)) hsep hB (by norm_num) (by positivity)
      ha hwa (fun k hk h => hnear k hk h) (fun k _ => by positivity) (fun k _ => ?_)
      (fun k _ hfar => ?_)
    · have : Real.exp (-(x - k) ^ 2 / ρ ^ 3) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_div]
        linarith [ht0 k]
      show 2 * Real.exp (-(x - k) ^ 2 / ρ ^ 3) ≤ 2
      linarith
    · show 2 * Real.exp (-(x - k) ^ 2 / ρ ^ 3) ≤ 2 * Real.exp (-(1 / ρ))
      have := one_div_le_of_le_abs hρ hfar
      gcongr
      rw [neg_div]
      linarith
  have n2 : ∑ k ∈ Y, a k * ‖P 2 Z x * P 0 (Y.erase k) x‖ *
      (|4 * ((x - k) ^ 2 / ρ ^ 3) ^ 2 - 2 * ((x - k) ^ 2 / ρ ^ 3)| *
        Real.exp (-((x - k) ^ 2 / ρ ^ 3))) ≤
      10 * B + (∑ k ∈ Y, a k) * (36 * Real.exp (-(1 / ρ / 2))) := by
    refine sum_le_near_far (w := fun k => a k * ‖P 2 Z x * P 0 (Y.erase k) x‖)
      (F := fun k => |4 * ((x - k) ^ 2 / ρ ^ 3) ^ 2 - 2 * ((x - k) ^ 2 / ρ ^ 3)| *
        Real.exp (-((x - k) ^ 2 / ρ ^ 3))) hsep hB (by norm_num) (by positivity)
      ha hwa (fun k hk h => hnear k hk h) (fun k _ => by positivity)
      (fun k _ => (abs_mul_exp_neg_le (ht0 k)).1) (fun k _ hfar => ?_)
    refine (abs_mul_exp_neg_le (ht0 k)).2.trans ?_
    have := one_div_le_of_le_abs hρ hfar
    gcongr
  have n3 : ∑ k ∈ Y, a k * ‖P 2 Z x * P 0 (Y.erase k) x‖ *
      (4 * ((x - k) ^ 2 / ρ ^ 3) * Real.exp (-((x - k) ^ 2 / ρ ^ 3))) ≤
      4 * B + (∑ k ∈ Y, a k) * (8 * Real.exp (-(1 / ρ / 2))) := by
    refine sum_le_near_far (w := fun k => a k * ‖P 2 Z x * P 0 (Y.erase k) x‖)
      (F := fun k => 4 * ((x - k) ^ 2 / ρ ^ 3) * Real.exp (-((x - k) ^ 2 / ρ ^ 3))) hsep hB
      (by norm_num) (by positivity) ha hwa (fun k hk h => hnear k hk h)
      (fun k _ => by have := ht0 k; positivity) (fun k _ => ?_) (fun k _ hfar => ?_)
    · show 4 * ((x - k) ^ 2 / ρ ^ 3) * Real.exp (-((x - k) ^ 2 / ρ ^ 3)) ≤ 4
      have := mul_exp_neg_le_one ((x - k) ^ 2 / ρ ^ 3)
      linarith
    · show 4 * ((x - k) ^ 2 / ρ ^ 3) * Real.exp (-((x - k) ^ 2 / ρ ^ 3)) ≤
        8 * Real.exp (-(1 / ρ / 2))
      have h1 := mul_exp_neg_le_half ((x - k) ^ 2 / ρ ^ 3)
      have h2 : Real.exp (-((x - k) ^ 2 / ρ ^ 3 / 2)) ≤ Real.exp (-(1 / ρ / 2)) := by
        have := one_div_le_of_le_abs hρ hfar
        gcongr
      linarith
  linarith

/-- The factor `Λ(M, Q) = M (4M² + 10M + 3 L₀ + 16Q)` with `L₀ = 2M(16Q² + 12Q)`,
collecting the small terms of `h`, `h'` and `h''`. -/
noncomputable def coef (M Q : ℝ) : ℝ :=
  M * (4 * M ^ 2 + 10 * M + 3 * (2 * M * (16 * Q ^ 2 + 12 * Q)) + 4 * (4 * Q))

/-- The trivial bounds of the paper on `[0,1]`: `|ψ| ≤ 1`, `|ψ'| ≤ 4Q`, `|ψ''| ≤ 16Q² + 12Q`,
`|φ| ≤ |x - y|²` and `|φ'| ≤ 2M |x - y|` for `y ∈ 𝒴`. -/
theorem trivial_bounds (hY : ∀ y ∈ Y, y ∈ I) (hZ : ∀ w ∈ Z, w ∈ I) (hx : x ∈ I) :
    ‖P 2 Z x‖ ≤ 1 ∧ ‖P1 2 Z x‖ ≤ 4 * Z.card ∧ ‖P2 2 Z x‖ ≤ 16 * Z.card ^ 2 + 12 * Z.card ∧
      (∀ k ∈ Y, ‖P 0 Y x‖ ≤ |x - k| ^ 2) ∧ ∀ k ∈ Y, ‖P1 0 Y x‖ ≤ 2 * Y.card * |x - k| := by
  have hYx : ∀ w ∈ Y, ‖(x : ℂ) - w‖ ≤ 1 := fun w hw => norm_ofReal_sub_le_one hx (hY w hw)
  have hZx : ∀ w ∈ Z, ‖(x : ℂ) - w‖ ≤ 1 := fun w hw => norm_ofReal_sub_le_one hx (hZ w hw)
  refine ⟨norm_P_le_one hZx, ?_, ?_, fun k hk => ?_, fun k hk => ?_⟩
  · have := norm_P1_le (m := 2) hZx
    norm_num at this
    linarith
  · have := norm_P2_le (m := 2) hZx
    norm_num at this
    linarith
  · simpa [norm_ofReal_sub] using norm_P_le (m := 0) hYx hk
  · simpa [norm_ofReal_sub] using norm_P1_le_of_mem (m := 0) hYx hk

/-- The estimates for `h`, `h'` and `h''` at a point of `[0,1]`, for `η = ρ³`. The hypotheses
`h1`, `h2`, `h3` are the conclusions of (4.3) under `(C1)`-`(C4)`, `hsep` is (4.5), and `hnear`
is the comparison of `ψ ∏_{y' ≠ y} (x - y')²` with its value at `y`, used with the choice (4.4)
of the `a_y`. The terms `φ'' ψ A`, `φ ψ A''` and `φ' ψ A'` contribute `20 B` and the far terms of
the near/far split. -/
theorem norm_H_le (hY : ∀ y ∈ Y, y ∈ I) (hZ : ∀ w ∈ Z, w ∈ I) (hZne : Z.Nonempty) (hx : x ∈ I) {ρ ν B : ℝ}
    (hρ : 0 < ρ) (ha : ∀ k ∈ Y, 0 ≤ a k) (hν : 0 ≤ ν) (hB : 0 ≤ B)
    (h1 : ∀ k ∈ Y, a k * |x - k| * Real.exp (-(x - k) ^ 2 / ρ ^ 3) ≤ ν)
    (h2 : ∀ k ∈ Y, a k * |x - k| ^ 2 * Real.exp (-(x - k) ^ 2 / ρ ^ 3) ≤ ν)
    (h3 : ∀ k ∈ Y, a k * |x - k| ^ 3 / ρ ^ 3 * Real.exp (-(x - k) ^ 2 / ρ ^ 3) ≤ ν)
    (hsep : ∀ k ∈ Y, ∀ k' ∈ Y, k ≠ k' → 2 * ρ < |k - k'|)
    (hnear : ∀ k ∈ Y, |x - k| < ρ → a k * ‖P 2 Z x * P 0 (Y.erase k) x‖ ≤ B) :
    ‖H Y Z a (ρ ^ 3) x‖ ≤ coef Y.card Z.card * ν ∧
      ‖H1 Y Z a (ρ ^ 3) x‖ ≤ coef Y.card Z.card * ν ∧
      ‖H2 Y Z a (ρ ^ 3) x‖ ≤ coef Y.card Z.card * ν + 20 * B +
        (∑ k ∈ Y, a k) * (2 * Real.exp (-(1 / ρ)) + 52 * Real.exp (-(1 / ρ / 2))) := by
  obtain ⟨hψ0, hψ1, hψ2, hφ0, hφ1⟩ := trivial_bounds hY hZ hx
  set M : ℝ := (Y.card : ℝ) with hM
  set Q : ℝ := (Z.card : ℝ) with hQ
  have hη : 0 < ρ ^ 3 := pow_pos hρ 3
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hQ0 : 0 ≤ Q := Nat.cast_nonneg _
  have hQ1 : 1 ≤ Q := by
    change (1 : ℝ) ≤ (Z.card : ℝ)
    exact_mod_cast Nat.succ_le_of_lt (Finset.card_pos.2 hZne)
  have hQ2 : 0 ≤ Q ^ 2 := sq_nonneg Q
  have hxk : ∀ k ∈ Y, |x - k| ≤ 1 := fun k hk => by
    simpa [norm_ofReal_sub] using norm_ofReal_sub_le_one hx (hY k hk)
  have hM1 : ∀ k ∈ Y, 1 ≤ M := fun k hk => by
    rw [hM]
    exact_mod_cast Finset.card_pos.2 ⟨k, hk⟩
  set Pc := 16 * Q ^ 2 + 12 * Q with hPc
  set L₀ := 2 * M * Pc with hL₀
  have hφ0' : ∀ k ∈ Y, ‖P 0 Y x‖ ≤ 2 * M * |x - k| := fun k hk => by
    have h0 := abs_nonneg (x - k)
    calc ‖P 0 Y x‖ ≤ |x - k| ^ 2 := hφ0 k hk
      _ = |x - k| * |x - k| := sq _
      _ ≤ 1 * |x - k| := mul_le_mul_of_nonneg_right (hxk k hk) h0
      _ ≤ 2 * M * |x - k| := mul_le_mul_of_nonneg_right (by linarith [hM1 k hk]) h0
  have hψ0' : ‖P 2 Z x‖ ≤ Pc := by linarith
  have hψ1' : ‖P1 2 Z x‖ ≤ Pc := by linarith
  have hψ2' : ‖P2 2 Z x‖ ≤ Pc := by linarith
  have hprod : ∀ Φ Ψ : ℂ, (∀ k ∈ Y, ‖Φ‖ ≤ 2 * M * |x - k|) → ‖Ψ‖ ≤ Pc →
      ∀ k ∈ Y, ‖Φ * Ψ‖ ≤ L₀ * |x - k| ^ 1 := fun Φ Ψ hΦ hΨ k hk => by
    rw [norm_mul, pow_one, hL₀]
    calc ‖Φ‖ * ‖Ψ‖ ≤ (2 * M * |x - k|) * Pc :=
          mul_le_mul (hΦ k hk) hΨ (norm_nonneg _) (by positivity)
      _ = 2 * M * Pc * |x - k| := by ring
  have hprod2 : ∀ Ψ : ℂ, ‖Ψ‖ ≤ 4 * Q →
      ∀ k ∈ Y, ‖P 0 Y x * Ψ‖ ≤ (4 * Q) * |x - k| ^ 2 := fun Ψ hΨ k hk => by
    rw [norm_mul]
    calc ‖P 0 Y x‖ * ‖Ψ‖ ≤ |x - k| ^ 2 * (4 * Q) :=
          mul_le_mul (hφ0 k hk) hΨ (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have h1' : ∀ k ∈ Y, a k * |x - k| ^ 1 * Real.exp (-(x - k) ^ 2 / ρ ^ 3) ≤ ν := fun k hk => by
    rw [pow_one]
    exact h1 k hk
  have hL₀0 : 0 ≤ L₀ := by positivity
  -- the norms handled by `(C1)`
  have g1 : ‖P 0 Y x * P 2 Z x * A a Y (ρ ^ 3) x‖ ≤ L₀ * (M * ν) :=
    norm_mul_A_le_of hL₀0 ha (hprod _ _ hφ0' hψ0') h1'
  have g2 : ‖P1 0 Y x * P 2 Z x * A a Y (ρ ^ 3) x‖ ≤ L₀ * (M * ν) :=
    norm_mul_A_le_of hL₀0 ha (hprod _ _ hφ1 hψ0') h1'
  have g3 : ‖P 0 Y x * P1 2 Z x * A a Y (ρ ^ 3) x‖ ≤ L₀ * (M * ν) :=
    norm_mul_A_le_of hL₀0 ha (hprod _ _ hφ0' hψ1') h1'
  have g4 : ‖P 0 Y x * P2 2 Z x * A a Y (ρ ^ 3) x‖ ≤ L₀ * (M * ν) :=
    norm_mul_A_le_of hL₀0 ha (hprod _ _ hφ0' hψ2') h1'
  have g5 : ‖P1 0 Y x * P1 2 Z x * A a Y (ρ ^ 3) x‖ ≤ L₀ * (M * ν) :=
    norm_mul_A_le_of hL₀0 ha (hprod _ _ hφ1 hψ1') h1'
  -- the norms handled by `(C2)`
  have g6 : ‖P 0 Y x * P 2 Z x * A1 a Y (ρ ^ 3) x‖ ≤ 2 * (4 * Q) * (M * ν) :=
    norm_mul_A1_le_of hη (by positivity) ha (hprod2 _ (by linarith)) h3
  have g7 : ‖P 0 Y x * P1 2 Z x * A1 a Y (ρ ^ 3) x‖ ≤ 2 * (4 * Q) * (M * ν) :=
    norm_mul_A1_le_of hη (by positivity) ha (hprod2 _ (by linarith)) h3
  -- the three remaining norms, and the near/far split
  have d1 := norm_P2_mul_A_le hY hZ hx ha h1' h2
  have d2 := norm_P_mul_A2_le (Y := Y) (Z := Z) (η := ρ ^ 3) (x := x) ha
  have d3 := norm_P1_mul_A1_le hY hZ hx hη ha h3
  have n := sum_near_far_le hY hx hρ ha hB hψ0 hsep hnear
  -- assembling the estimates
  have hMν : 0 ≤ M * ν := mul_nonneg hM0 hν
  have hcoef : coef M Q * ν = 4 * M ^ 2 * (M * ν) + 2 * M * (M * ν) + L₀ * (M * ν) +
      2 * (L₀ * (M * ν)) + 2 * (4 * M * (M * ν)) + 2 * (2 * (4 * Q) * (M * ν)) := by
    simp only [coef, hL₀, hPc]
    ring
  have p1 : 0 ≤ 4 * M ^ 2 * (M * ν) := by positivity
  have p2 : 0 ≤ 2 * M * (M * ν) := by positivity
  have p3 : 0 ≤ L₀ * (M * ν) := by positivity
  have p4 : 0 ≤ 4 * M * (M * ν) := by positivity
  have p5 : 0 ≤ 2 * (4 * Q) * (M * ν) := by positivity
  have e2 : ∀ T : ℂ, ‖2 * T‖ = 2 * ‖T‖ := fun T => by rw [norm_mul, Complex.norm_two]
  refine ⟨?_, ?_, ?_⟩
  · show ‖P 0 Y x * P 2 Z x * A a Y (ρ ^ 3) x‖ ≤ coef M Q * ν
    linarith
  · show ‖P1 0 Y x * P 2 Z x * A a Y (ρ ^ 3) x + P 0 Y x * P1 2 Z x * A a Y (ρ ^ 3) x +
      P 0 Y x * P 2 Z x * A1 a Y (ρ ^ 3) x‖ ≤ coef M Q * ν
    have a1 := norm_add_le (P1 0 Y x * P 2 Z x * A a Y (ρ ^ 3) x +
      P 0 Y x * P1 2 Z x * A a Y (ρ ^ 3) x) (P 0 Y x * P 2 Z x * A1 a Y (ρ ^ 3) x)
    have a2 := norm_add_le (P1 0 Y x * P 2 Z x * A a Y (ρ ^ 3) x)
      (P 0 Y x * P1 2 Z x * A a Y (ρ ^ 3) x)
    linarith
  · simp only [H2]
    set T1 := P2 0 Y x * P 2 Z x * A a Y (ρ ^ 3) x
    set T2 := P 0 Y x * P2 2 Z x * A a Y (ρ ^ 3) x
    set T3 := P 0 Y x * P 2 Z x * A2 a Y (ρ ^ 3) x
    set T4 := P1 0 Y x * P1 2 Z x * A a Y (ρ ^ 3) x
    set T5 := P1 0 Y x * P 2 Z x * A1 a Y (ρ ^ 3) x
    set T6 := P 0 Y x * P1 2 Z x * A1 a Y (ρ ^ 3) x
    have a1 := norm_add_le (T1 + T2 + T3 + 2 * T4 + 2 * T5) (2 * T6)
    have a2 := norm_add_le (T1 + T2 + T3 + 2 * T4) (2 * T5)
    have a3 := norm_add_le (T1 + T2 + T3) (2 * T4)
    have a4 := norm_add_le (T1 + T2) T3
    have a5 := norm_add_le T1 T2
    rw [e2] at a1 a2 a3
    linarith

end Estimates

/-- From the bounds on `h`, `h'`, `h''` to the bounds on `g - f`, `g' - f'`, `g'' - f''`, using
`g - f = f (e^h - 1)`, `g' - f' = f' (e^h - 1) + f h' e^h` and
`g'' - f'' = f'' (e^h - 1) + (2 f' h' + f h'² + f h'') e^h`. -/
theorem norm_sub_le_of_norm_H_le {f0 f1 f2 h h1 h2 : ℂ} {s B2 D : ℝ} (hs : s ≤ 1 / 2)
    (hf0 : ‖f0‖ ≤ 1) (hf1 : ‖f1‖ ≤ 1) (hf2 : ‖f2‖ ≤ B2) (hD : 0 ≤ D)
    (hh : ‖h‖ ≤ s) (hh1 : ‖h1‖ ≤ s) (hh2 : ‖h2‖ ≤ D + s) :
    ‖f0 * Complex.exp h - f0‖ ≤ 2 * s ∧
      ‖(f1 + f0 * h1) * Complex.exp h - f1‖ ≤ 4 * s ∧
      ‖(f2 + 2 * f1 * h1 + f0 * h1 ^ 2 + f0 * h2) * Complex.exp h - f2‖ ≤
        2 * B2 * s + 8 * s + 2 * D := by
  have hs0 : 0 ≤ s := (norm_nonneg _).trans hh
  have he1 : ‖Complex.exp h - 1‖ ≤ 2 * s :=
    (Complex.norm_exp_sub_one_le (by linarith)).trans (by linarith)
  have he : ‖Complex.exp h‖ ≤ 2 := by
    have := norm_sub_norm_le (Complex.exp h) 1
    rw [norm_one] at this
    linarith
  have hB2 : 0 ≤ B2 := (norm_nonneg _).trans hf2
  have hn1 := norm_nonneg f0
  have hn2 := norm_nonneg f1
  have hn3 := norm_nonneg h1
  refine ⟨?_, ?_, ?_⟩
  · rw [show f0 * Complex.exp h - f0 = f0 * (Complex.exp h - 1) by ring, norm_mul]
    calc ‖f0‖ * ‖Complex.exp h - 1‖ ≤ 1 * (2 * s) :=
          mul_le_mul hf0 he1 (norm_nonneg _) zero_le_one
      _ = 2 * s := one_mul _
  · rw [show (f1 + f0 * h1) * Complex.exp h - f1 =
        f1 * (Complex.exp h - 1) + f0 * h1 * Complex.exp h by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul]
    have t1 : ‖f1‖ * ‖Complex.exp h - 1‖ ≤ 1 * (2 * s) :=
      mul_le_mul hf1 he1 (norm_nonneg _) zero_le_one
    have t2 : ‖f0‖ * ‖h1‖ * ‖Complex.exp h‖ ≤ 1 * s * 2 :=
      mul_le_mul (mul_le_mul hf0 hh1 hn3 zero_le_one) he (norm_nonneg _) (by positivity)
    linarith
  · rw [show (f2 + 2 * f1 * h1 + f0 * h1 ^ 2 + f0 * h2) * Complex.exp h - f2 =
        f2 * (Complex.exp h - 1) + (2 * f1 * h1 + f0 * h1 ^ 2 + f0 * h2) * Complex.exp h by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have t1 : ‖f2‖ * ‖Complex.exp h - 1‖ ≤ B2 * (2 * s) :=
      mul_le_mul hf2 he1 (norm_nonneg _) hB2
    have t2 : ‖2 * f1 * h1‖ ≤ 2 * s := by
      rw [norm_mul, norm_mul, Complex.norm_two]
      have := mul_le_mul hf1 hh1 hn3 zero_le_one
      linarith
    have t3 : ‖f0 * h1 ^ 2‖ ≤ s / 2 := by
      rw [norm_mul, norm_pow]
      have h4 : ‖h1‖ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hn3 hh1 2
      have := mul_le_mul hf0 h4 (by positivity) zero_le_one
      nlinarith
    have t4 : ‖f0 * h2‖ ≤ D + s := by
      rw [norm_mul]
      have := mul_le_mul hf0 hh2 (norm_nonneg _) zero_le_one
      linarith
    have t5 : ‖2 * f1 * h1 + f0 * h1 ^ 2 + f0 * h2‖ ≤ 2 * s + s / 2 + (D + s) := by
      have a1 := norm_add_le (2 * f1 * h1 + f0 * h1 ^ 2) (f0 * h2)
      have a2 := norm_add_le (2 * f1 * h1) (f0 * h1 ^ 2)
      linarith
    have t6 : ‖2 * f1 * h1 + f0 * h1 ^ 2 + f0 * h2‖ * ‖Complex.exp h‖ ≤
        (2 * s + s / 2 + (D + s)) * 2 := mul_le_mul t5 he (norm_nonneg _) (by positivity)
    linarith

/-- `|A(y)| ≥ a_y` at `y ∈ 𝒴` for positive amplitudes. -/
theorem le_norm_A {a : ℝ → ℝ} {Y : Finset ℝ} {η y : ℝ} (ha : ∀ k ∈ Y, 0 ≤ a k) (hy : y ∈ Y) :
    a y ≤ ‖A a Y η y‖ := by
  rw [A_ofReal, Complex.norm_real, Real.norm_eq_abs]
  refine le_trans ?_ (le_abs_self _)
  have h := Finset.single_le_sum (f := fun k => a k * Real.exp (-(y - k) ^ 2 / η))
    (fun k hk => mul_nonneg (ha k hk) (Real.exp_pos _).le) hy
  simpa using h

end MultiplicativeBump

open MultiplicativeBump in
/-- Proposition 4.2, by the construction of the paper. Let `f ∈ S^ω(I)` with `f([0,1]) ⊆ (0,1)`.
There is `C > 0` such that for all finite disjoint `𝒴, 𝒵 ⊆ [0,1]`, `η > 0` and `δ > 0` there is
`g ∈ S^ω(I)` with `g = f` and `g' = f'` on `𝒴 ∪ 𝒵`, `g'' = f''` on `𝒵`,
`|g''/g' - f''/f'| ≥ δ` on `𝒴`, `|g - f| < η` and `|g' - f'| < η` on `[0,1]`, and
`|g'' - f''| < C δ + η` on `[0,1]`. The paper writes `ε` for `η`. Here `g = f e^{φ ψ A}` with the
amplitudes (4.4) and all widths equal to `ρ³` for a small `ρ > 0`, and `C = 40/m` for a margin
`m` with `m ≤ f ≤ 1 - m` on `[0,1]`. -/
private theorem proposition_4_2_nonempty {ε : ℝ} (hε : 0 < ε) {f : ℂ → ℂ} (hf : InClass ε f)
    (hI : ∀ x ∈ I, (f x).re ∈ Ioo 0 1) :
    ∃ C > 0, ∀ Y Z : Finset ℝ, (∀ y ∈ Y, y ∈ I) → (∀ z ∈ Z, z ∈ I) → Disjoint Y Z → Z.Nonempty →
      ∀ η > 0, ∀ δ > 0, ∃ g : ℂ → ℂ, (∃ ε' > 0, InClass ε' g) ∧
        (∀ y ∈ Y ∪ Z, g y = f y ∧ deriv g y = deriv f y) ∧
        (∀ z ∈ Z, deriv (deriv g) z = deriv (deriv f) z) ∧
        (∀ y ∈ Y, δ ≤ ‖deriv (deriv g) y / deriv g y - deriv (deriv f) y / deriv f y‖) ∧
        (∀ x ∈ I, ‖g x - f x‖ < η) ∧ (∀ x ∈ I, ‖deriv g x - deriv f x‖ < η) ∧
        (∀ x ∈ I, ‖deriv (deriv g) x - deriv (deriv f) x‖ < C * δ + η) := by
  obtain ⟨m, hm, hmar⟩ := exists_margin hε hf hI
  have h2ε : 0 < 2 * ε := by positivity
  have hU : IsOpen (nbhd (2 * ε)) := isOpen_nbhd _
  have hmem : ∀ x ∈ I, (x : ℂ) ∈ nbhd (2 * ε) := fun x hx => ofReal_mem_nbhd h2ε hx
  have hfU := hf.differentiableOn
  -- a bound `B₂` for `f''` on `[0,1]`
  obtain ⟨B₂, hB₂⟩ : ∃ B₂, ∀ x ∈ I, ‖deriv (deriv f) x‖ ≤ B₂ := by
    have hc : ContinuousOn (fun x : ℝ => deriv (deriv f) (x : ℂ)) I :=
      ((hfU.deriv hU).deriv hU).continuousOn.comp Complex.continuous_ofReal.continuousOn
        fun x hx => hmem x hx
    exact isCompact_Icc.exists_bound_of_continuousOn hc
  have hB₂0 : 0 ≤ B₂ := (norm_nonneg _).trans (hB₂ 0 ⟨le_rfl, zero_le_one⟩)
  -- `f` and `f'` on `[0,1]`
  have hfreal : ∀ x ∈ I, f x = ((f x).re : ℂ) := fun x hx =>
    Complex.ext rfl (by simp [hf.im_eq_zero x (hmem x hx)])
  have hf0 : ∀ x ∈ I, m ≤ ‖f x‖ ∧ ‖f x‖ ≤ 1 := fun x hx => by
    obtain ⟨h1, h2, -, -⟩ := hmar x hx
    rw [hfreal x hx, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    constructor <;> linarith
  have hf1 : ∀ x ∈ I, m ≤ ‖deriv f x‖ ∧ ‖deriv f x‖ ≤ 1 := fun x hx => by
    obtain ⟨-, -, h1, h2⟩ := hmar x hx
    constructor <;> linarith
  refine ⟨40 / m, by positivity, fun Y Z hY hZ hYZ hZne η hη δ hδ => ?_⟩
  have hWI : ∀ w ∈ Y ∪ Z, w ∈ I := fun w hw => (Finset.mem_union.1 hw).elim (hY w) (hZ w)
  -- the amplitudes (4.4)
  set N : ℝ → ℝ := fun k => ‖P 2 Z k * P 0 (Y.erase k) k‖ with hN_def
  have hN0 : ∀ k ∈ Y, P 2 Z k * P 0 (Y.erase k) k ≠ 0 := fun k hk =>
    mul_ne_zero (P_ne_zero 2 (Finset.disjoint_left.1 hYZ hk))
      (P_ne_zero 0 (Finset.notMem_erase k Y))
  have hN : ∀ k ∈ Y, 0 < N k := fun k hk => norm_pos_iff.2 (hN0 k hk)
  set a : ℝ → ℝ := fun k => δ * ‖deriv f k‖ / (2 * ‖f k‖ * N k) with ha_def
  have hfk : ∀ k ∈ Y, 0 < ‖f k‖ := fun k hk => hm.trans_le (hf0 k (hY k hk)).1
  have ha : ∀ k ∈ Y, 0 < a k := fun k hk => by
    have := hm.trans_le (hf1 k (hY k hk)).1
    have := hfk k hk
    have := hN k hk
    simp only [ha_def]
    positivity
  have haN : ∀ k ∈ Y, 2 * a k * N k * ‖f k‖ = δ * ‖deriv f k‖ := fun k hk => by
    have := hfk k hk
    have := hN k hk
    simp only [ha_def]
    field_simp
  -- the size `s` of `h`, `h'` and of `h''` up to `20 δ/m` on `[0,1]`; the paper's `ε`
  set s := min (1 / 2) (min (η / (2 * B₂ + 9)) (m / 5)) with hs_def
  have hs : 0 < s := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hs1 : s ≤ 1 / 2 := min_le_left _ _
  have hsη : (2 * B₂ + 8) * s < η := by
    have h1 : s ≤ η / (2 * B₂ + 9) := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : (2 * B₂ + 8) * s ≤ (2 * B₂ + 8) * (η / (2 * B₂ + 9)) := by gcongr
    have h3 : (2 * B₂ + 8) * (η / (2 * B₂ + 9)) < η := by
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hsm : s ≤ m / 5 := (min_le_right _ _).trans (min_le_right _ _)
  set Λ := coef Y.card Z.card with hΛ
  have hΛ0 : 0 ≤ Λ := by
    simp only [hΛ, coef]
    positivity
  set ν := s / (2 * (Λ + 1)) with hν_def
  have hν : 0 < ν := by positivity
  have hΛν : Λ * ν ≤ s / 2 := by
    rw [hν_def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- the width `η_y = ρ³`: (4.3) under `(C1)`-`(C4)`, (4.5), (4.6) and its analogue, and the
  -- comparison near `𝒴`
  have hcont : ∀ k : ℝ, Continuous fun z => P 2 Z z * P 0 (Y.erase k) z := fun k =>
    ((differentiable_P 2 Z).mul (differentiable_P 0 _)).continuous
  have hs4 : 0 < s / 4 := by positivity
  obtain ⟨ρ, ⟨⟨⟨⟨⟨⟨⟨E1, E2⟩, E3⟩, Esep⟩, Enear⟩, F1⟩, F2⟩, hρ⟩⟩ :=
    (((((((((eventually_all_finset Y).2 fun k hk => eventually_gauss_one (ha k hk) hν).and
      ((eventually_all_finset Y).2 fun k hk => eventually_gauss_two (ha k hk) hν)).and
      ((eventually_all_finset Y).2 fun k hk => eventually_gauss_three (ha k hk) hν)).and
      (eventually_sep Y)).and
      ((eventually_all_finset Y).2 fun k hk => eventually_near (hcont k) (hN0 k hk))).and
      (eventually_exp_neg_div_le ((∑ k ∈ Y, a k) * 2) one_pos hs4)).and
      (eventually_exp_neg_div_le ((∑ k ∈ Y, a k) * 52) (by norm_num : (0 : ℝ) < 1 / 2) hs4)).and
      self_mem_nhdsWithin).exists
  have hρ : 0 < ρ := hρ
  set g := G f Y Z a (ρ ^ 3) with hg_def
  have hderiv := fun (x : ℝ) (hx : x ∈ I) => deriv_G (Y := Y) (Z := Z) (a := a) (η := ρ ^ 3) hU
    hfU (z := (x : ℂ)) (hmem x hx)
  -- the estimates on `[0,1]`
  have hest : ∀ x ∈ I, ‖g x - f x‖ ≤ 2 * s ∧ ‖deriv g x - deriv f x‖ ≤ 4 * s ∧
      ‖deriv (deriv g) x - deriv (deriv f) x‖ ≤ 2 * B₂ * s + 8 * s + 2 * (20 * (δ / m)) := by
    intro x hx
    have hnear : ∀ k ∈ Y, |x - k| < ρ → a k * ‖P 2 Z x * P 0 (Y.erase k) x‖ ≤ δ / m := by
      intro k hk hxk
      have h1 := Enear k hk x hxk
      have h2 := haN k hk
      have h3 := (hf1 k (hY k hk)).2
      have h4 := (hf0 k (hY k hk)).1
      have hak := (ha k hk).le
      calc a k * ‖P 2 Z x * P 0 (Y.erase k) x‖ ≤ a k * (2 * N k) := by gcongr
        _ = δ * ‖deriv f k‖ / ‖f k‖ := by
            rw [eq_div_iff (hfk k hk).ne']
            linarith
        _ ≤ δ * 1 / m := by
            gcongr
        _ = δ / m := by ring
    obtain ⟨n0, n1, n2⟩ := norm_H_le hY hZ hZne hx hρ (fun k hk => (ha k hk).le) hν.le
      (by positivity : 0 ≤ δ / m) (fun k hk => E1 k hk (x - k)) (fun k hk => E2 k hk (x - k))
      (fun k hk => E3 k hk (x - k)) Esep hnear
    rw [← hΛ] at n0 n1 n2
    have hfar : (∑ k ∈ Y, a k) * (2 * Real.exp (-(1 / ρ)) + 52 * Real.exp (-(1 / ρ / 2))) ≤
        s / 2 := by
      have e : -(1 / ρ / 2) = -(1 / 2 / ρ) := by ring
      rw [e]
      linarith
    have k0 : ‖H Y Z a (ρ ^ 3) x‖ ≤ s := by linarith
    have k1 : ‖H1 Y Z a (ρ ^ 3) x‖ ≤ s := by linarith
    have k2 : ‖H2 Y Z a (ρ ^ 3) x‖ ≤ 20 * (δ / m) + s := by linarith
    obtain ⟨r0, r1, r2⟩ := norm_sub_le_of_norm_H_le hs1 (hf0 x hx).2 (hf1 x hx).2 (hB₂ x hx)
      (by positivity) k0 k1 k2
    rw [(hderiv x hx).1, (hderiv x hx).2]
    exact ⟨r0, r1, r2⟩
  refine ⟨g, ?_, fun w hw => ?_, fun w hw => ?_, fun y hy => ?_, fun x hx => ?_, fun x hx => ?_,
    fun x hx => ?_⟩
  · -- "Hence `g ∈ S^ω([0,1])`", by `exists_inClass`
    refine exists_inClass hU ?_ (hfU.fun_mul (differentiable_H Y Z a (ρ ^ 3)).cexp.differentiableOn)
      (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
    · rintro _ ⟨x, hx, rfl⟩
      exact hmem x hx
    · have hH : H Y Z a (ρ ^ 3) x = ((H Y Z a (ρ ^ 3) x).re : ℂ) :=
        Complex.ext rfl (by simp [im_H_ofReal])
      show (f x * Complex.exp (H Y Z a (ρ ^ 3) x)).im = 0
      rw [hH, Complex.mul_im, Complex.exp_ofReal_im, hf.im_eq_zero x hx]
      ring
    · obtain ⟨h1, h2, -, -⟩ := hmar x hx
      have h3 := (Complex.abs_re_le_norm (g x - f x)).trans (hest x hx).1
      rw [abs_le, Complex.sub_re] at h3
      show (g x).re ∈ I
      constructor <;> linarith
    · obtain ⟨-, -, h1, -⟩ := hmar x hx
      have h2 := (hest x hx).2.1
      intro h
      rw [h, zero_sub, norm_neg] at h2
      linarith
    · obtain ⟨-, -, -, h1⟩ := hmar x hx
      have h2 := (hest x hx).2.1
      have h3 := norm_sub_norm_le (deriv g x) (deriv f x)
      linarith
  · -- agreement to first order on `𝒴 ∪ 𝒵`
    have hH : H Y Z a (ρ ^ 3) w = 0 ∧ H1 Y Z a (ρ ^ 3) w = 0 := by
      rcases Finset.mem_union.1 hw with hw | hw
      · exact H_of_mem_Y hw
      · exact ⟨(H_of_mem_Z hw).1, (H_of_mem_Z hw).2.1⟩
    rw [(hderiv w (hWI w hw)).1, hH.1, hH.2]
    refine ⟨?_, by simp⟩
    show f w * Complex.exp (H Y Z a (ρ ^ 3) w) = f w
    rw [hH.1, Complex.exp_zero, mul_one]
  · -- agreement to second order on `𝒵`
    obtain ⟨h0, h1, h2⟩ := H_of_mem_Z (Y := Y) (a := a) (η := ρ ^ 3) hw
    rw [(hderiv w (hZ w hw)).2, h0, h1, h2]
    simp
  · -- the lower bound in (iii)
    have hyI := hY y hy
    obtain ⟨h0, h1⟩ := H_of_mem_Y (Z := Z) (a := a) (η := ρ ^ 3) hy
    have hne : deriv f y ≠ 0 := norm_pos_iff.1 (hm.trans_le (hf1 y hyI).1)
    rw [(hderiv y hyI).2, (hderiv y hyI).1, h0, h1, H2_of_mem_Y hy]
    have e : (deriv (deriv f) y + 2 * deriv f y * 0 + f y * 0 ^ 2 +
        f y * (2 * P 0 (Y.erase y) y * P 2 Z y * A a Y (ρ ^ 3) y)) * Complex.exp 0 /
        ((deriv f y + f y * 0) * Complex.exp 0) - deriv (deriv f) y / deriv f y =
        f y * (2 * (P 2 Z y * P 0 (Y.erase y) y)) * A a Y (ρ ^ 3) y / deriv f y := by
      rw [Complex.exp_zero]
      simp only [mul_zero, add_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow]
      rw [add_div, add_sub_cancel_left]
      ring
    rw [e, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_two,
      le_div_iff₀ (norm_pos_iff.2 hne)]
    have h2 := haN y hy
    have h3 := le_norm_A (η := ρ ^ 3) (fun k hk => (ha k hk).le) hy
    have h4 := (hfk y hy).le
    have h5 := (hN y hy).le
    calc δ * ‖deriv f y‖ = ‖f y‖ * (2 * N y) * a y := by linarith
      _ ≤ ‖f y‖ * (2 * N y) * ‖A a Y (ρ ^ 3) y‖ := by gcongr
  · have := mul_nonneg hB₂0 hs.le
    exact (hest x hx).1.trans_lt (by linarith)
  · have := mul_nonneg hB₂0 hs.le
    exact (hest x hx).2.1.trans_lt (by linarith)
  · have h := (hest x hx).2.2
    have e : 2 * (20 * (δ / m)) = 40 / m * δ := by ring
    linarith

/-- Proposition 4.2. As in the manuscript, pad an empty `Z` by a point of `I \ Y`
before making the multiplicative perturbation. -/
theorem proposition_4_2 {ε : ℝ} (hε : 0 < ε) {f : ℂ → ℂ} (hf : InClass ε f)
    (hI : ∀ x ∈ I, (f x).re ∈ Ioo 0 1) :
    ∃ C > 0, ∀ Y Z : Finset ℝ, (∀ y ∈ Y, y ∈ I) → (∀ z ∈ Z, z ∈ I) → Disjoint Y Z →
      ∀ η > 0, ∀ δ > 0, ∃ g : ℂ → ℂ, (∃ ε' > 0, InClass ε' g) ∧
        (∀ y ∈ Y ∪ Z, g y = f y ∧ deriv g y = deriv f y) ∧
        (∀ z ∈ Z, deriv (deriv g) z = deriv (deriv f) z) ∧
        (∀ y ∈ Y, δ ≤ ‖deriv (deriv g) y / deriv g y - deriv (deriv f) y / deriv f y‖) ∧
        (∀ x ∈ I, ‖g x - f x‖ < η) ∧ (∀ x ∈ I, ‖deriv g x - deriv f x‖ < η) ∧
        (∀ x ∈ I, ‖deriv (deriv g) x - deriv (deriv f) x‖ < C * δ + η) := by
  classical
  obtain ⟨C, hC, h⟩ := proposition_4_2_nonempty hε hf hI
  refine ⟨C, hC, fun Y Z hY hZ hYZ η hη δ hδ => ?_⟩
  by_cases hYe : Y = ∅
  · subst Y
    refine ⟨f, ⟨ε, hε, hf⟩, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl,
      by simp, ?_, ?_, ?_⟩
    · intro x hx; simpa using hη
    · intro x hx; simpa using hη
    · intro x hx; simpa using add_pos (mul_pos hC hδ) hη
  by_cases hZe : Z.Nonempty
  · exact h Y Z hY hZ hYZ hZe η hη δ hδ
  obtain ⟨z, hzI, hzY⟩ := (Set.Icc_infinite zero_lt_one).sdiff (Y.finite_toSet) |>.nonempty
  have hZempty : Z = ∅ := Finset.not_nonempty_iff_eq_empty.1 hZe
  obtain ⟨g, hg, hagree, hsecond, hchange, h0, h1, h2⟩ :=
    h Y {z} hY (by simpa using hzI) (Finset.disjoint_singleton_right.2 hzY)
      (Finset.singleton_nonempty z) η hη δ hδ
  refine ⟨g, hg, fun y hy => hagree y ?_, ?_, hchange, h0, h1, h2⟩
  · simpa only [hZempty, Finset.union_empty] using Finset.mem_union_left {z}
      (by simpa [hZempty] using hy : y ∈ Y)
  · simp [hZempty]

end AnalyticESC
