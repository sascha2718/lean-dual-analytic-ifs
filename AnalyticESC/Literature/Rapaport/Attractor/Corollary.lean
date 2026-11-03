module

public import AnalyticESC.Literature.Rapaport.Attractor.Iterate
public import AnalyticESC.Literature.Rapaport.Attractor.Gibbs
public import AnalyticESC.Literature.Rapaport.Attractor.Covering
public import AnalyticESC.Literature.Rapaport.Attractor.MassDistribution

@[expose] public section

/-!
# Rapaport's Corollary 1.3: the dimension of the attractor

A. Rapaport, *Dimension of self-conformal measures associated to an exponentially separated
analytic IFS on ℝ*, arXiv:2412.16753v2, Corollary 1.3: for an analytic IFS `Φ` on `I` with
`0 < |φ_i'| < 1`, no common fixed point and exponential separation, the attractor has Hausdorff
dimension `min{1, s(Φ)}`, where `s(Φ)` is the zero of the pressure.

We derive the statement `AnalyticESC.RapaportSetStatement` from Rapaport's Theorem 1.2
(`AnalyticESC.RapaportMeasureStatement`) and Bowen's theorem (`AnalyticESC.BowenGibbsStatement`),
following the proof in Section 1.3 of the paper. The upper bound comes from covers by cylinder
intervals (`dimH_le_of_tendsto_pressure`). For the lower bound, Bowen's theorem gives a measure
`ν` on `(Fin N)^ℕ` with `ν[u] ≍ ‖φ_u'‖_I^s` (`exists_gibbs_weights`); Theorem 1.2 applied to the
iterated system `Φ^n` (`rapaportHyp_iter`) with the weights `q_n(u) = ν[u]` gives a measure on `K`
of local dimension `min{1, H(q_n)/χ_n}` almost everywhere, so
`dim_H K ≥ min{1, H(q_n)/χ_n}` (`ofReal_le_dimH_of_ae_tendsto`), and
`|H(q_n) - s χ_n| = O(1)` while `χ_n ≥ n log(1/c_max)` (`entropy_lyapunov_bounds`), so
`H(q_n)/χ_n → s`. The basic facts on compositions, the coding map and the self-conformal measure
come from the toolkit `FractalGeometry.SelfConformal.Toolkit`.

Main declarations:

* `integral_bounds_of_mem_I`: integrals of functions bounded on `I`;
* `entropy_lyapunov_bounds`: the entropy and Lyapunov exponent of `(Φ^n, q_n)`;
* `rapaportSet_of_measure`: `RapaportMeasureStatement → BowenGibbsStatement →
  RapaportSetStatement`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Attractor.Corollary`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Attractor

open Set Filter Topology MeasureTheory AnalyticESC FractalGeometry.SelfConformal
open scoped ENNReal

variable {N : ℕ} {φ : Fin N → ℝ → ℝ}

/-- If `a ≤ f ≤ b` on `I` and `μ` is a probability measure carried by `I`, then
`a ≤ ∫ f dμ ≤ b`. -/
theorem integral_bounds_of_mem_I {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : μ Iᶜ = 0)
    {f : ℝ → ℝ} (hf : Measurable f) {a b : ℝ} (h : ∀ y ∈ I, a ≤ f y ∧ f y ≤ b) :
    a ≤ ∫ y, f y ∂μ ∧ ∫ y, f y ∂μ ≤ b := by
  have hae : ∀ᵐ y ∂μ, y ∈ I := ae_iff.2 hμ
  have hint : Integrable f μ := by
    refine Integrable.of_bound hf.aestronglyMeasurable (max |a| |b|) (hae.mono fun y hy => ?_)
    obtain ⟨h1, h2⟩ := h y hy
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le a, le_max_left |a| |b|]
    · linarith [le_abs_self b, le_max_right |a| |b|]
  constructor
  · have := integral_mono_ae (integrable_const a) hint (hae.mono fun y hy => (h y hy).1)
    simpa using this
  · have := integral_mono_ae hint (integrable_const b) (hae.mono fun y hy => (h y hy).2)
    simpa using this

/-- The entropy and the Lyapunov exponent of the iterated system `Φ^n` with weights `q` satisfying
`C⁻¹ ‖φ_u'‖_I^s ≤ q(u) ≤ C ‖φ_u'‖_I^s`: for the self-conformal measure `μ` of `(Φ^n, q)`,
`χ = -∑_u q(u) ∫ log |φ_u'| dμ ≥ n log(1/c_max)` and `|H(q) - s χ| ≤ log C + |s| log C_φ`,
where `C_φ = distConst φ` is the bounded distortion constant. -/
theorem entropy_lyapunov_bounds (hφ : RapaportHyp φ) (hN : 0 < N) {n : ℕ} (hn : 0 < n)
    {s C : ℝ} (hC0 : 0 < C) {q : Fin (N ^ n) → ℝ} (hq : IsProbVec q)
    (hqC : ∀ j, C⁻¹ * supDeriv φ (block n j) ^ s ≤ q j ∧ q j ≤ C * supDeriv φ (block n j) ^ s) :
    (n : ℝ) * -Real.log (cmax φ) ≤
        -∑ j, q j * ∫ y, Real.log |deriv (iter φ n j) y| ∂(selfConformal (iter φ n) q hq) ∧
      |-∑ j, q j * Real.log (q j) -
          s * -∑ j, q j * ∫ y, Real.log |deriv (iter φ n j) y| ∂(selfConformal (iter φ n) q hq)|
        ≤ Real.log C + |s| * Real.log (distConst φ) := by
  have hψ := rapaportHyp_iter hφ hN hn
  set μ := selfConformal (iter φ n) q hq with hμ_def
  set D := Real.log (distConst φ) with hD_def
  have hμI : μ Iᶜ = 0 := selfConformal_compl_I hψ hq
  have hS : ∀ j, 0 < supDeriv φ (block n j) := fun j => supDeriv_pos hφ _
  -- `log q(u) = s log ‖φ_u'‖ + O(1)`
  have hlogq : ∀ j, |Real.log (q j) - s * Real.log (supDeriv φ (block n j))| ≤ Real.log C := by
    intro j
    obtain ⟨h1, h2⟩ := hqC j
    have hSs := Real.rpow_pos_of_pos (hS j) s
    have hl1 := Real.log_le_log (mul_pos (inv_pos.2 hC0) hSs) h1
    have hl2 := Real.log_le_log (hq.1 j) h2
    rw [Real.log_mul (inv_pos.2 hC0).ne' hSs.ne', Real.log_inv, Real.log_rpow (hS j)] at hl1
    rw [Real.log_mul hC0.ne' hSs.ne', Real.log_rpow (hS j)] at hl2
    rw [abs_le]
    constructor <;> linarith
  -- `∫ log |φ_u'| dμ = log ‖φ_u'‖ + O(1)` and `log ‖φ_u'‖ ≤ n log c₁`
  have hint : ∀ j, Real.log (supDeriv φ (block n j)) - D ≤
      ∫ y, Real.log |deriv (iter φ n j) y| ∂μ ∧
      ∫ y, Real.log |deriv (iter φ n j) y| ∂μ ≤ Real.log (supDeriv φ (block n j)) := by
    intro j
    refine integral_bounds_of_mem_I hμI
      (Real.measurable_log.comp (continuous_abs.measurable.comp (measurable_deriv _)))
      fun y hy => ?_
    have h1 := abs_log_supDeriv_sub_le hφ (block n j) hy
    have h2 := (supDeriv_bounds hφ (block n j)).1 y hy
    have hpos : 0 < |deriv (realComp φ (block n j)) y| :=
      abs_pos.2 (deriv_realComp_ne_zero hφ _ hy)
    have h3 := Real.log_le_log hpos h2
    rw [abs_le] at h1
    show _ ≤ Real.log |deriv (realComp φ (block n j)) y| ∧
      Real.log |deriv (realComp φ (block n j)) y| ≤ _
    constructor <;> linarith
  have hlogS : ∀ j, Real.log (supDeriv φ (block n j)) ≤ n * Real.log (cmax φ) := by
    intro j
    have h := (supDeriv_bounds hφ (block n j)).2.2
    rw [length_block] at h
    calc Real.log (supDeriv φ (block n j)) ≤ Real.log (cmax φ ^ n) := Real.log_le_log (hS j) h
      _ = n * Real.log (cmax φ) := by rw [Real.log_pow]
  constructor
  · -- the Lyapunov exponent
    have hle : ∑ j, q j * ∫ y, Real.log |deriv (iter φ n j) y| ∂μ ≤
        ∑ j, q j * (n * Real.log (cmax φ)) :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left ((hint j).2.trans (hlogS j)) (hq.1 j).le
    rw [← Finset.sum_mul, hq.2, one_mul] at hle
    linarith
  · -- the entropy
    have e : -∑ j, q j * Real.log (q j) - s * -∑ j, q j * ∫ y, Real.log |deriv (iter φ n j) y| ∂μ
        = ∑ j, q j * (s * ∫ y, Real.log |deriv (iter φ n j) y| ∂μ - Real.log (q j)) := by
      rw [mul_neg, sub_neg_eq_add, Finset.mul_sum, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ j, |q j * (s * ∫ y, Real.log |deriv (iter φ n j) y| ∂μ - Real.log (q j))| ≤
        q j * (Real.log C + |s| * D) := by
      intro j
      rw [abs_mul, abs_of_pos (hq.1 j)]
      refine mul_le_mul_of_nonneg_left ?_ (hq.1 j).le
      have h1 : |∫ y, Real.log |deriv (iter φ n j) y| ∂μ - Real.log (supDeriv φ (block n j))| ≤
          D := by
        rw [abs_le]
        constructor <;> linarith [(hint j).1, (hint j).2]
      calc |s * ∫ y, Real.log |deriv (iter φ n j) y| ∂μ - Real.log (q j)|
          = |s * (∫ y, Real.log |deriv (iter φ n j) y| ∂μ - Real.log (supDeriv φ (block n j))) -
              (Real.log (q j) - s * Real.log (supDeriv φ (block n j)))| := by ring_nf
        _ ≤ |s * (∫ y, Real.log |deriv (iter φ n j) y| ∂μ -
              Real.log (supDeriv φ (block n j)))| +
            |Real.log (q j) - s * Real.log (supDeriv φ (block n j))| := abs_sub _ _
        _ ≤ |s| * D + Real.log C := by
            rw [abs_mul]
            exact add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg s)) (hlogq j)
        _ = Real.log C + |s| * D := add_comm _ _
    calc ∑ j, |q j * (s * ∫ y, Real.log |deriv (iter φ n j) y| ∂μ - Real.log (q j))|
        ≤ ∑ j, q j * (Real.log C + |s| * D) := Finset.sum_le_sum fun j _ => hterm j
      _ = Real.log C + |s| * D := by rw [← Finset.sum_mul, hq.2, one_mul]

/-- **Rapaport's Corollary 1.3** (arXiv:2412.16753v2), from Theorem 1.2 and Bowen's theorem: for an
analytic IFS `φ` on `I` satisfying `RapaportHyp φ`, the attractor `K` has Hausdorff dimension
`min{1, s}`, where `s` is the zero of the pressure. -/
theorem rapaportSet_of_measure (hM : RapaportMeasureStatement) (hB : BowenGibbsStatement) :
    RapaportSetStatement := by
  intro N φ hφ K hne hKc hKI hK s hs
  -- the alphabet is nonempty, since `K` is
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · obtain ⟨x, hx⟩ := hne
      rw [hK] at hx
      obtain ⟨i, -⟩ := mem_iUnion.1 hx
      exact i.elim0
    · exact h
  have hKinv : ∀ i, MapsTo (φ i) K K := fun i x hx => by
    rw [hK]
    exact mem_iUnion.2 ⟨i, x, hx, rfl⟩
  -- the pressure hypothesis, indexed by all `n`
  have hs' : Tendsto (fun n : ℕ => Real.log (pressureSum φ s n) / n) atTop (𝓝 0) :=
    (positive_length_tendsto_iff fun n => Real.log (pressureSum φ s n)).1 hs
  set c₁ := cmax φ with hc₁_def
  have hc1 : 0 < c₁ := cmax_pos hφ hN
  have hc1' : c₁ < 1 := cmax_lt_one hφ
  set D := Real.log (distConst φ) with hD_def
  have hD0 : 0 ≤ D := Real.log_nonneg (one_lt_distConst hφ).le
  have hSpos : ∀ l : List (Fin N), 0 < supDeriv φ l := supDeriv_pos hφ
  -- `s ≥ 0`: for `s < 0` the pressure sums grow at least like `c₁^{n s}`
  have hs0 : 0 ≤ s := by
    by_contra hneg
    rw [not_le] at hneg
    have hpos : 0 < s * Real.log c₁ := mul_pos_of_neg_of_neg hneg (Real.log_neg hc1 hc1')
    have hev : ∀ᶠ n : ℕ in atTop, s * Real.log c₁ ≤ Real.log (pressureSum φ s n) / n := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hS := supDeriv_bounds hφ (List.ofFn fun _ : Fin n => (⟨0, hN⟩ : Fin N))
      rw [List.length_ofFn] at hS
      have h1 := Real.rpow_le_rpow_of_nonpos (hSpos _) hS.2.2 hneg.le
      have h2 : supDeriv φ (List.ofFn fun _ : Fin n => (⟨0, hN⟩ : Fin N)) ^ s ≤
          pressureSum φ s n :=
        Finset.single_le_sum (f := fun u : Fin n → Fin N => supDeriv φ (List.ofFn u) ^ s)
          (fun u _ => Real.rpow_nonneg (hSpos _).le s) (Finset.mem_univ _)
      have h3 := Real.log_le_log (Real.rpow_pos_of_pos (pow_pos hc1 n) s) (h1.trans h2)
      rw [Real.log_rpow (pow_pos hc1 n), Real.log_pow] at h3
      rw [le_div_iff₀ hn']
      linarith
    have := ge_of_tendsto hs' hev
    linarith
  -- the upper bound
  have hupper : dimH K ≤ ENNReal.ofReal (min 1 s) := by
    rw [ENNReal.ofReal_min, ENNReal.ofReal_one]
    exact le_min (dimH_le_one K) (dimH_le_of_tendsto_pressure hφ hN hKI hK hs0 hs')
  refine le_antisymm hupper ?_
  -- the Gibbs weights `ν[u] ≍ ‖φ_u'‖^s`
  obtain ⟨ν, hν, C, hC1, hG⟩ := exists_gibbs_weights hB hφ hN hs'
  have hC0 : 0 < C := one_pos.trans_le hC1
  set q : (n : ℕ) → Fin (N ^ n) → ℝ := fun n j => ν.real (cylinder (finFunctionFinEquiv.symm j))
    with hq_def
  have hqC : ∀ n j, C⁻¹ * supDeriv φ (block n j) ^ s ≤ q n j ∧
      q n j ≤ C * supDeriv φ (block n j) ^ s := fun n j => hG n _
  have hq : ∀ n, IsProbVec (q n) := fun n =>
    ⟨fun j => (mul_pos (inv_pos.2 hC0) (Real.rpow_pos_of_pos (hSpos _) s)).trans_le (hqC n j).1,
      by
        rw [hq_def]
        simp only
        rw [Equiv.sum_comp finFunctionFinEquiv.symm fun u => ν.real (cylinder u)]
        exact sum_measureReal_cylinder ν n⟩
  set H : ℕ → ℝ := fun n => -∑ j, q n j * Real.log (q n j) with hH_def
  set χ : ℕ → ℝ := fun n => -∑ j, q n j *
    ∫ y, Real.log |deriv (iter φ n j) y| ∂(selfConformal (iter φ n) (q n) (hq n)) with hχ_def
  have hbounds : ∀ n : ℕ, 0 < n → (n : ℝ) * -Real.log c₁ ≤ χ n ∧
      |H n - s * χ n| ≤ Real.log C + |s| * D := fun n hn =>
    entropy_lyapunov_bounds hφ hN hn hC0 (hq n) (hqC n)
  have hlam : 0 < -Real.log c₁ := neg_pos.2 (Real.log_neg hc1 hc1')
  have hχpos : ∀ n : ℕ, 0 < n → 0 < χ n := fun n hn =>
    (mul_pos (by exact_mod_cast hn) hlam).trans_le (hbounds n hn).1
  -- for each `n ≥ 1`, Theorem 1.2 for `Φ^n` gives `dim_H K ≥ min{1, H(q_n)/χ_n}`
  have hdim : ∀ n : ℕ, 0 < n → ENNReal.ofReal (min 1 (H n / χ n)) ≤ dimH K := by
    intro n hn
    have hψ := rapaportHyp_iter hφ hN hn
    have hloc := hM (iter φ n) hψ (q n) (hq n).1 (hq n).2
      (selfConformal (iter φ n) (q n) (hq n)) inferInstance (selfConformal_compl_I hψ (hq n))
      (selfConformal_eq_sum hψ (hq n)) (hχpos n hn).ne'
    have hrange : range (coding (iter φ n)) ⊆ K := range_subset_iff.2
      (coding_mem_of_mapsTo hψ hKc.isClosed hne hKI fun j => mapsTo_realComp_of_mapsTo hKinv _)
    have hKμ : selfConformal (iter φ n) (q n) (hq n) Kᶜ = 0 :=
      measure_mono_null (compl_subset_compl.2 hrange) (selfConformal_compl_range hψ (hq n))
    exact ofReal_le_dimH_of_ae_tendsto hKμ hloc
  -- `H(q_n)/χ_n → s`
  set E := Real.log C + |s| * D with hE_def
  have hE : 0 ≤ E := add_nonneg (Real.log_nonneg hC1) (mul_nonneg (abs_nonneg s) hD0)
  have hratio : Tendsto (fun n : ℕ => H (n + 1) / χ (n + 1)) atTop (𝓝 s) := by
    have h0 : Tendsto (fun n : ℕ => E / -Real.log c₁ * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := E / -Real.log c₁)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rwa [mul_zero] at this
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) h0)
    have hn : 0 < n + 1 := n.succ_pos
    obtain ⟨hχn, hHn⟩ := hbounds (n + 1) hn
    have hχ0 := hχpos (n + 1) hn
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    push_cast at hχn
    rw [Real.dist_eq, show H (n + 1) / χ (n + 1) - s = (H (n + 1) - s * χ (n + 1)) / χ (n + 1) by
      field_simp, abs_div, abs_of_pos hχ0]
    calc |H (n + 1) - s * χ (n + 1)| / χ (n + 1) ≤ E / χ (n + 1) :=
          div_le_div_of_nonneg_right hHn hχ0.le
      _ ≤ E / (((n : ℝ) + 1) * -Real.log c₁) :=
          div_le_div_of_nonneg_left hE (mul_pos hn1 hlam) hχn
      _ = E / -Real.log c₁ * (1 / ((n : ℝ) + 1)) := by
          field_simp
  -- the lower bound
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (min 1 (H (n + 1) / χ (n + 1)))) atTop
      (𝓝 (ENNReal.ofReal (min 1 s))) :=
    ENNReal.tendsto_ofReal (tendsto_const_nhds.min hratio)
  exact le_of_tendsto' hlim fun n => hdim (n + 1) n.succ_pos

end FractalGeometry.Rapaport.Attractor
