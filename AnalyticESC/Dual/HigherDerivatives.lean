module

public import AnalyticESC.Dual.Derivatives

@[expose] public section

/-!
# Lemma 2.7

The higher derivatives of the dual natural projection: the identity (2.10),
`f_v^{(k+1)}/f_v' = g_k(H_{v^←}^{(k-1)}, …, H_{v^←})`, and the formula of Lemma 2.7 for
`H_w^{(k)}`, obtained from (2.8) and Faà di Bruno's formula. The set partitions `Π_{k+1}` of the
paper are Mathlib's `OrderedFinpartition (k + 1)`, the partitions of `Fin (k + 1)` with blocks
ordered by their greatest element.
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-- The polynomials `g_k` of Section 2.2. The variable `X ℓ` stands for `y_{ℓ+1}`, which is
evaluated at `H^{(ℓ)}`: `g_0 = 1` and `g_{k+1} = ∑_{ℓ < k} ∂g_k/∂X_ℓ · X_{ℓ+1} + g_k · X_0`, so
that `g_1 = X_0`, `g_2 = X_1 + X_0²` and `g_3 = X_2 + 3 X_0 X_1 + X_0³`. -/
noncomputable def gPoly : ℕ → MvPolynomial ℕ ℤ
  | 0 => 1
  | k + 1 => (∑ ℓ ∈ Finset.range k, MvPolynomial.pderiv ℓ (gPoly k) * MvPolynomial.X (ℓ + 1)) +
      gPoly k * MvPolynomial.X 0

/-! ## Polynomials along curves -/

/-- Partial derivatives preserve the polynomials in the variables of `s`. -/
theorem pderiv_mem_supported {s : Set ℕ} {p : MvPolynomial ℕ ℤ}
    (hp : p ∈ MvPolynomial.supported ℤ s) (ℓ : ℕ) :
    MvPolynomial.pderiv ℓ p ∈ MvPolynomial.supported ℤ s := by
  rw [MvPolynomial.supported_eq_adjoin_X] at hp ⊢
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, -, rfl⟩ := hx
    by_cases h : m = ℓ
    · rw [h, MvPolynomial.pderiv_X_self]
      exact one_mem _
    · rw [MvPolynomial.pderiv_X_of_ne h]
      exact zero_mem _
  | algebraMap r =>
    rw [Derivation.map_algebraMap]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y hx' hy' hx hy =>
    rw [MvPolynomial.pderiv_mul]
    exact add_mem (mul_mem hx hy') (mul_mem hx' hy)

/-- `g_k` is a polynomial in `X 0, …, X (k-1)`, that is, in `y_1, …, y_k`. -/
theorem gPoly_mem_supported (k : ℕ) :
    gPoly k ∈ MvPolynomial.supported ℤ (↑(Finset.range k) : Set ℕ) := by
  induction k with
  | zero => exact one_mem _
  | succ k ih =>
    have hmono : MvPolynomial.supported ℤ (↑(Finset.range k) : Set ℕ) ≤
        MvPolynomial.supported ℤ ↑(Finset.range (k + 1)) :=
      MvPolynomial.supported_mono (Finset.coe_subset.2 (Finset.range_subset_range.2 k.le_succ))
    have hX : ∀ m ≤ k,
        MvPolynomial.X m ∈ MvPolynomial.supported ℤ (↑(Finset.range (k + 1)) : Set ℕ) :=
      fun m hm => MvPolynomial.X_mem_supported.2 (Finset.mem_range.2 (Nat.lt_succ_of_le hm))
    rw [gPoly]
    exact add_mem (Subalgebra.sum_mem _ fun ℓ hℓ => mul_mem (hmono (pderiv_mem_supported ih ℓ))
      (hX _ (Finset.mem_range.1 hℓ))) (mul_mem (hmono ih) (hX 0 k.zero_le))

/-- The chain rule for a polynomial in the variables of `s` along a curve `y`: if each `y_ℓ`,
`ℓ ∈ s`, has derivative `y'_ℓ` at `z`, then `u ↦ p(y(u))` has derivative
`∑_{ℓ ∈ s} ∂_ℓ p(y(z)) · y'_ℓ` at `z`. -/
theorem hasDerivAt_aeval_of_mem_supported {s : Finset ℕ} {p : MvPolynomial ℕ ℤ}
    (hp : p ∈ MvPolynomial.supported ℤ (s : Set ℕ)) {y : ℕ → ℂ → ℂ} {y' : ℕ → ℂ} {z : ℂ}
    (hy : ∀ ℓ ∈ s, HasDerivAt (y ℓ) (y' ℓ) z) :
    HasDerivAt (fun u => MvPolynomial.aeval (fun ℓ => y ℓ u) p)
      (∑ ℓ ∈ s, MvPolynomial.aeval (fun ℓ => y ℓ z) (MvPolynomial.pderiv ℓ p) * y' ℓ) z := by
  rw [MvPolynomial.supported_eq_adjoin_X] at hp
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    rw [Finset.sum_eq_single m (fun ℓ _ hℓ => by rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hℓ),
      map_zero, zero_mul]) (fun h => absurd hm h)]
    simpa [MvPolynomial.pderiv_X_self] using hy m hm
  | algebraMap r =>
    simp only [Derivation.map_algebraMap, map_zero, zero_mul, Finset.sum_const_zero,
      AlgHom.commutes]
    exact hasDerivAt_const z _
  | add p q _ _ hp hq =>
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    exact hp.fun_add hq
  | mul p q _ _ hp hq =>
    simp only [map_mul]
    convert hp.fun_mul hq using 1
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul]
    ring

/-! ## Holomorphic maps -/

/-- Iterated derivatives of a map holomorphic on an open set are holomorphic there. -/
theorem differentiableAt_iteratedDeriv {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (k : ℕ) {z : ℂ} (hz : z ∈ U) :
    DifferentiableAt ℂ (iteratedDeriv k g) z := by
  rw [iteratedDeriv_eq_iterate]
  exact ((hg.analyticOnNhd hU).iterated_deriv k z hz).differentiableAt

/-- Termwise iterated differentiation of a series of holomorphic maps on an open set whose terms
are bounded by a summable sequence. -/
theorem hasSum_iteratedDeriv_of_summable_norm {ι : Type*} {F : ι → ℂ → ℂ} {U : Set ℂ}
    {u : ι → ℝ} (hu : Summable u) (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hU : IsOpen U)
    (hF_le : ∀ i, ∀ z ∈ U, ‖F i z‖ ≤ u i) (k : ℕ) {z : ℂ} (hz : z ∈ U) :
    HasSum (fun i => iteratedDeriv k (F i) z) (iteratedDeriv k (fun w => ∑' i, F i w) z) := by
  have hG : ∀ s : Finset ι, DifferentiableOn ℂ (fun w => ∑ i ∈ s, F i w) U :=
    fun s => DifferentiableOn.fun_sum fun i _ => hF i
  have hlim : ∀ m, TendstoLocallyUniformlyOn
      (fun s : Finset ι => iteratedDeriv m fun w => ∑ i ∈ s, F i w)
      (iteratedDeriv m fun w => ∑' i, F i w) atTop U := by
    intro m
    induction m with
    | zero => simpa using (tendstoUniformlyOn_tsum hu hF_le).tendstoLocallyUniformlyOn
    | succ m ih =>
      simp only [iteratedDeriv_succ]
      exact ih.deriv (Eventually.of_forall fun s w hw =>
        (differentiableAt_iteratedDeriv hU (hG s) m hw).differentiableWithinAt) hU
  exact ((hlim k).tendsto_at hz).congr fun s => iteratedDeriv_fun_sum fun i _ =>
    ((hF i).analyticAt (hU.mem_nhds hz)).contDiffAt

/-- The `k`-th derivative of `(h ∘ f) · f'` is the Faà di Bruno sum for the `(k+1)`-th derivative
of `Ψ ∘ f`, where `Ψ` is a primitive of `h` near `f(z)`, so that `Ψ^{(m)} = h^{(m-1)}`. -/
theorem iteratedDeriv_comp_mul_deriv {h f : ℂ → ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hh : DifferentiableOn ℂ h (ball (f z) r)) (hf : AnalyticAt ℂ f z) (k : ℕ) :
    iteratedDeriv k (fun u => h (f u) * deriv f u) z =
      ∑ c : OrderedFinpartition (k + 1),
        iteratedDeriv (c.length - 1) h (f z) * ∏ j, iteratedDeriv (c.partSize j) f z := by
  obtain ⟨Ψ, hΨ⟩ := hh.isExactOn_ball
  have hball : ball (f z) r ∈ 𝓝 (f z) := ball_mem_nhds _ hr
  have heq : (fun u => h (f u) * deriv f u) =ᶠ[𝓝 z] deriv (Ψ ∘ f) := by
    filter_upwards [hf.continuousAt.preimage_mem_nhds hball, hf.eventually_analyticAt]
      with u hu hfu
    exact ((hΨ _ hu).comp u hfu.differentiableAt.hasDerivAt).deriv.symm
  have hΨd : deriv Ψ =ᶠ[𝓝 (f z)] h := by
    filter_upwards [hball] with v hv using (hΨ v hv).deriv
  have hΨa : AnalyticAt ℂ Ψ (f z) :=
    DifferentiableOn.analyticAt (fun v hv => (hΨ v hv).differentiableAt.differentiableWithinAt)
      hball
  have hΨm : ∀ m, 0 < m → iteratedDeriv m Ψ (f z) = iteratedDeriv (m - 1) h (f z) := by
    intro m hm
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    rw [iteratedDeriv_succ', hΨd.iteratedDeriv_eq m, Nat.succ_sub_one]
  rw [heq.iteratedDeriv_eq k, ← iteratedDeriv_succ',
    iteratedDeriv_comp_eq_sum_orderedFinpartition hΨa.contDiffAt hf.contDiffAt le_rfl]
  exact Finset.sum_congr rfl fun c _ => by rw [hΨm _ (c.length_pos k.succ_pos)]

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- The term with index `n` (from `0`) of the formula of Lemma 2.7 for `H_w^{(k)}`: with `v` the
first `n` letters of `w` and `i` the next one, the sum over partitions `π` of `{1, …, k+1}` of
`φ_i^{(|π|)}(f_{v^←}(z)) · (f_{v^←}'(z))^{|π|} · ∏_{B ∈ π} g_{|B|-1}(H_v^{(|B|-2)}(z), …, H_v(z))`,
where `φ_i^{(m)} = (f_i''/f_i')^{(m-1)}` for `m ≥ 1`. Zero if `|w| ≤ n`. -/
noncomputable def dualDerivTerm (w : Word N) (k n : ℕ) (z : ℂ) : ℂ :=
  match w.get? n with
  | none => 0
  | some i => ∑ c : OrderedFinpartition (k + 1),
      iteratedDeriv (c.length - 1) (Φ.nonlin i) (Φ.comp (w.take n).reverse z) *
        deriv (Φ.comp (w.take n).reverse) z ^ c.length *
        ∏ j, MvPolynomial.aeval (fun ℓ => iteratedDeriv ℓ (Φ.dualProj (.fin (w.take n))) z)
          (gPoly (c.partSize j - 1))

/-! ## The identity (2.10) -/

/-- `H_w^{(ℓ)}` has derivative `H_w^{(ℓ+1)}` on `B_ε`. -/
theorem hasDerivAt_iteratedDeriv_dualProj (w : Word N) (ℓ : ℕ) {z : ℂ} (hz : z ∈ nbhd ε) :
    HasDerivAt (iteratedDeriv ℓ (Φ.dualProj w)) (iteratedDeriv (ℓ + 1) (Φ.dualProj w) z) z := by
  rw [iteratedDeriv_succ]
  exact (differentiableAt_iteratedDeriv (isOpen_nbhd ε) (Φ.differentiableOn_dualProj w) ℓ
    hz).hasDerivAt

/-- (2.10) in product form on `B_ε`: `f_v^{(k+1)} = f_v' · g_k(H_{v^←}^{(k-1)}, …, H_{v^←})`,
where `f_v = Φ.comp w.reverse` and `H_{v^←} = Φ.dualProj (.fin w)`. -/
theorem iteratedDeriv_succ_comp_reverse (w : List (Fin N)) (k : ℕ) {z : ℂ} (hz : z ∈ nbhd ε) :
    iteratedDeriv (k + 1) (Φ.comp w.reverse) z = deriv (Φ.comp w.reverse) z *
      MvPolynomial.aeval (fun ℓ => iteratedDeriv ℓ (Φ.dualProj (.fin w)) z) (gPoly k) := by
  induction k generalizing z with
  | zero => simp [gPoly]
  | succ k ih =>
    have hU := isOpen_nbhd ε
    have heq : iteratedDeriv (k + 1) (Φ.comp w.reverse) =ᶠ[𝓝 z] fun u =>
        deriv (Φ.comp w.reverse) u *
          MvPolynomial.aeval (fun ℓ => iteratedDeriv ℓ (Φ.dualProj (.fin w)) u) (gPoly k) := by
      filter_upwards [hU.mem_nhds hz] with u hu using ih hu
    have hf' : HasDerivAt (deriv (Φ.comp w.reverse)) (deriv (deriv (Φ.comp w.reverse)) z) z :=
      ((((Φ.differentiableOn_comp _).deriv hU) z hz).differentiableAt
        (hU.mem_nhds hz)).hasDerivAt
    have hG := hasDerivAt_aeval_of_mem_supported (gPoly_mem_supported k)
      (y := fun ℓ => iteratedDeriv ℓ (Φ.dualProj (.fin w)))
      (fun ℓ _ => Φ.hasDerivAt_iteratedDeriv_dualProj (.fin w) ℓ hz)
    -- (2.7): `f_v'' = f_v' · H_{v^←}`
    have hH : deriv (deriv (Φ.comp w.reverse)) z =
        deriv (Φ.comp w.reverse) z * Φ.dualProj (.fin w) z := by
      have h := Φ.dualProj_fin_reverse w.reverse (subset_closure hz)
      rw [List.reverse_reverse] at h
      rw [h, mul_div_cancel₀ _ (Φ.deriv_comp_ne_zero _ (subset_closure hz))]
    rw [iteratedDeriv_succ, heq.deriv_eq, (hf'.fun_mul hG).deriv, hH]
    simp only [gPoly, map_add, map_sum, map_mul, MvPolynomial.aeval_X, iteratedDeriv_zero]
    ring

/-- (2.10): `f_v^{(k+1)}/f_v' = g_k(H_{v^←}^{(k-1)}, …, H_{v^←})` on `[0,1]`, where `v^←` is the
reversed word, so that `H_{v^←} = f_v''/f_v'` by (2.7). -/
theorem iteratedDeriv_comp_div_deriv (w : List (Fin N)) (k : ℕ) {x : ℝ} (hx : x ∈ I) :
    iteratedDeriv (k + 1) (Φ.comp w.reverse) x / deriv (Φ.comp w.reverse) x =
      MvPolynomial.aeval (fun ℓ => iteratedDeriv ℓ (Φ.dualProj (.fin w)) x) (gPoly k) := by
  have hx' := ofReal_mem_nbhd Φ.ε_pos hx
  rw [Φ.iteratedDeriv_succ_comp_reverse w k hx',
    mul_div_cancel_left₀ _ (Φ.deriv_comp_ne_zero _ (subset_closure hx'))]

/-! ## Lemma 2.7 -/

/-- Lemma 2.7 termwise, on `B_ε`: the `k`-th derivative of the term with index `n` of (1.4) is
`dualDerivTerm w k n`, by Faà di Bruno's formula and (2.10). A local primitive of `f_i''/f_i'`
takes the place of `φ_i = log|f_i'|` in (2.8). -/
theorem iteratedDeriv_dualTerm (w : Word N) (k n : ℕ) {z : ℂ} (hz : z ∈ nbhd ε) :
    iteratedDeriv k (Φ.dualTerm w n) z = Φ.dualDerivTerm w k n z := by
  cases h : w.get? n with
  | none =>
    have hT : Φ.dualTerm w n = fun _ => 0 := funext (Φ.dualTerm_of_get?_eq_none h)
    simp [hT, dualDerivTerm, h]
  | some i =>
    have hT : Φ.dualTerm w n = fun u => Φ.nonlin i (Φ.comp (w.take n).reverse u) *
        deriv (Φ.comp (w.take n).reverse) u := funext (Φ.dualTerm_of_get?_eq_some h)
    obtain ⟨U, hUo, hU, -, hnl⟩ := Φ.exists_differentiableOn_nonlin i
    obtain ⟨r, hr, hrU⟩ :=
      Metric.isOpen_iff.1 hUo _ (hU (subset_closure (Φ.mapsTo_comp (w.take n).reverse hz)))
    have hfa : AnalyticAt ℂ (Φ.comp (w.take n).reverse) z :=
      (Φ.differentiableOn_comp _).analyticAt ((isOpen_nbhd ε).mem_nhds hz)
    -- each block contributes `f_v' · g_{|B|-1}(…)`, by (2.10)
    have hpart : ∀ m, 0 < m → iteratedDeriv m (Φ.comp (w.take n).reverse) z =
        deriv (Φ.comp (w.take n).reverse) z * MvPolynomial.aeval
          (fun ℓ => iteratedDeriv ℓ (Φ.dualProj (.fin (w.take n))) z) (gPoly (m - 1)) := by
      intro m hm
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
      rw [Nat.succ_sub_one]
      exact Φ.iteratedDeriv_succ_comp_reverse _ m hz
    rw [hT, iteratedDeriv_comp_mul_deriv hr (hnl.mono hrU) hfa k]
    simp only [dualDerivTerm, h]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.prod_congr rfl fun j _ => hpart _ (c.partSize_pos j), Finset.prod_mul_distrib,
      Fin.prod_const, mul_assoc]

/-- Lemma 2.7: for every finite or infinite word `w` and `k ≥ 0`, the series of
`dualDerivTerm` converges and sums to `H_w^{(k)}` on `[0,1]`. -/
theorem lemma_2_7 (w : Word N) (k : ℕ) {x : ℝ} (hx : x ∈ I) :
    Summable (fun n => Φ.dualDerivTerm w k n x) ∧
      iteratedDeriv k (Φ.dualProj w) x = ∑' n, Φ.dualDerivTerm w k n x := by
  obtain ⟨C, -, hC⟩ := Φ.exists_dualTerm_bound
  have hx' := ofReal_mem_nbhd Φ.ε_pos hx
  have h := hasSum_iteratedDeriv_of_summable_norm
    ((summable_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left C)
    (Φ.differentiableOn_dualTerm w) (isOpen_nbhd ε)
    (fun n z hz => hC w n z (subset_closure hz)) k hx'
  simp only [Φ.iteratedDeriv_dualTerm w k _ hx'] at h
  exact ⟨h.summable, h.tsum_eq.symm⟩

end IFS

end AnalyticESC
