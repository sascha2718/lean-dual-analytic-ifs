module

public import AnalyticESC.Literature.Rapaport.Attractor.Basic

@[expose] public section

/-!
# The covering upper bound

For a system `φ` satisfying `AnalyticESC.RapaportHyp φ` and a set `K ⊆ I` with
`K = ⋃_i φ_i(K)`, the covers of `K` by the cylinder intervals `φ_u(I)`, `|u| = n`, give
`dim_H K ≤ s` for every `s ≥ 0` with `(1/n) log ∑_{|u| = n} ‖φ_u'‖_I^s → 0`. This is the upper
bound `dim_H K_Φ ≤ min{1, s(Φ)}` quoted before Corollary 1.3 in A. Rapaport, *Dimension of
self-conformal measures associated to an exponentially separated analytic IFS on ℝ*,
arXiv:2412.16753v2, Section 1.3.

Main declarations:

* `pressureSum`: the sums `Z_n(t) = ∑_{|u| = n} ‖φ_u'‖_I^t`;
* `subset_iUnion_image`: `K ⊆ ⋃_{|u| = n} φ_u(K)`;
* `ediam_image_le`: `|φ_u(I)| ≤ ‖φ_u'‖_I`;
* `dimH_le_of_tendsto_pressure`: `dim_H K ≤ s`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Attractor.Covering`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Attractor

open Set Filter Topology MeasureTheory AnalyticESC FractalGeometry.SelfConformal
open scoped ENNReal

variable {N : ℕ} {φ : Fin N → ℝ → ℝ}

/-- The pressure sums `Z_n(t) = ∑_{|u| = n} ‖φ_u'‖_I^t`. -/
noncomputable def pressureSum (φ : Fin N → ℝ → ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  ∑ u : Fin n → Fin N, supDeriv φ (List.ofFn u) ^ t

/-- A set with `K = ⋃_i φ_i(K)` satisfies `K ⊆ ⋃_{|u| = n} φ_u(K)`. -/
theorem subset_iUnion_image {K : Set ℝ} (hK : K = ⋃ i, φ i '' K) (n : ℕ) :
    K ⊆ ⋃ u : Fin n → Fin N, realComp φ (List.ofFn u) '' K := by
  induction n with
  | zero =>
    intro x hx
    exact mem_iUnion.2 ⟨Fin.elim0, by simpa using hx⟩
  | succ n ih =>
    intro x hx
    rw [hK] at hx
    obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.1 hx
    obtain ⟨u, z, hz, rfl⟩ := mem_iUnion.1 (ih hy)
    exact mem_iUnion.2 ⟨Fin.cons i u, z, hz, by rw [List.ofFn_cons, realComp_cons]; rfl⟩

/-- The interval `φ_u(I)` has diameter at most `‖φ_u'‖_I`. -/
theorem ediam_image_le (hφ : RapaportHyp φ) (l : List (Fin N)) :
    Metric.ediam (realComp φ l '' I) ≤ ENNReal.ofReal (supDeriv φ l) := by
  refine Metric.ediam_le ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [edist_dist, Real.dist_eq]
  refine ENNReal.ofReal_le_ofReal ((abs_realComp_sub_le_supDeriv hφ l hx hy).trans ?_)
  simpa using mul_le_mul_of_nonneg_left (abs_sub_le_one_of_mem_I hx hy) (supDeriv_pos hφ l).le

/-- `(c^n)^a = (c^a)^n` for `c ≥ 0`. -/
theorem pow_rpow_eq_rpow_pow {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (a : ℝ) : (c ^ n) ^ a = (c ^ a) ^ n := by
  rw [← Real.rpow_natCast c n, ← Real.rpow_mul hc, mul_comm, Real.rpow_mul hc,
    Real.rpow_natCast]

/-- The upper bound: if `K ⊆ I`, `K = ⋃_i φ_i(K)`, `s ≥ 0` and
`(1/n) log ∑_{|u| = n} ‖φ_u'‖_I^s → 0`, then `dim_H K ≤ s`. -/
theorem dimH_le_of_tendsto_pressure (hφ : RapaportHyp φ) (hN : 0 < N) {K : Set ℝ} (hKI : K ⊆ I)
    (hK : K = ⋃ i, φ i '' K) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : Tendsto (fun n : ℕ => Real.log (pressureSum φ s n) / n) atTop (𝓝 0)) :
    dimH K ≤ ENNReal.ofReal s := by
  set c₁ := cmax φ with hc₁_def
  have hc1 : 0 < c₁ := cmax_pos hφ hN
  have hc1' : c₁ < 1 := cmax_lt_one hφ
  have hSpos : ∀ l : List (Fin N), 0 < supDeriv φ l := supDeriv_pos hφ
  have key : ∀ t, s < t → dimH K ≤ ENNReal.ofReal t := by
    intro t hst
    have ht0 : 0 < t := hs0.trans_lt hst
    set r := c₁ ^ (t - s) with hr_def
    have hr0 : 0 < r := Real.rpow_pos_of_pos hc1 _
    have hr1 : r < 1 := Real.rpow_lt_one hc1.le hc1' (sub_pos.2 hst)
    have hlogr : Real.log r < 0 := Real.log_neg hr0 hr1
    set ρ := Real.exp (Real.log r / 2) with hρ_def
    have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
    have hρ1 : ρ < 1 := (Real.exp_lt_exp.2 (by linarith)).trans_eq Real.exp_zero
    -- `Z_n(s) r^n ≤ ρ^n` for large `n`
    have hZ0 : ∀ n, 0 ≤ pressureSum φ s n := fun n =>
      Finset.sum_nonneg fun u _ => Real.rpow_nonneg (hSpos _).le s
    have hev : ∀ᶠ n : ℕ in atTop, pressureSum φ s n * r ^ n ≤ ρ ^ n := by
      have hε : ∀ᶠ n : ℕ in atTop, Real.log (pressureSum φ s n) / n < -Real.log r / 2 :=
        hs.eventually (gt_mem_nhds (by linarith))
      filter_upwards [hε, eventually_ge_atTop 1] with n hn hn1
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
      have hZ : pressureSum φ s n ≤ Real.exp (n * (-Real.log r / 2)) := by
        rcases (hZ0 n).eq_or_lt with h | h
        · rw [← h]
          exact (Real.exp_pos _).le
        · rw [div_lt_iff₀ hn'] at hn
          calc pressureSum φ s n = Real.exp (Real.log (pressureSum φ s n)) :=
                (Real.exp_log h).symm
            _ ≤ Real.exp (n * (-Real.log r / 2)) := Real.exp_le_exp.2 (by linarith)
      calc pressureSum φ s n * r ^ n ≤ Real.exp (n * (-Real.log r / 2)) * r ^ n :=
            mul_le_mul_of_nonneg_right hZ (pow_nonneg hr0.le n)
        _ = ρ ^ n := by
            rw [hρ_def, ← Real.exp_log hr0, ← Real.exp_nat_mul, ← Real.exp_nat_mul,
              ← Real.exp_add, Real.log_exp]
            congr 1
            ring
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (pressureSum φ s n * r ^ n)) atTop
        (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      refine ENNReal.tendsto_ofReal (squeeze_zero' (Eventually.of_forall fun n =>
        mul_nonneg (hZ0 n) (pow_nonneg hr0.le n)) hev
        (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1))
    -- the sums `∑_{|u| = n} |φ_u(I)|^t` are at most `Z_n(s) r^n`
    have hdiam : ∀ (n : ℕ) (u : Fin n → Fin N),
        Metric.ediam (realComp φ (List.ofFn u) '' I) ≤ ENNReal.ofReal (c₁ ^ n) := by
      intro n u
      refine (ediam_image_le hφ _).trans (ENNReal.ofReal_le_ofReal ?_)
      have := (supDeriv_bounds hφ (List.ofFn u)).2.2
      rwa [List.length_ofFn] at this
    have hsum : ∀ n : ℕ, ∑ u : Fin n → Fin N, Metric.ediam (realComp φ (List.ofFn u) '' I) ^ t ≤
        ENNReal.ofReal (pressureSum φ s n * r ^ n) := by
      intro n
      calc ∑ u : Fin n → Fin N, Metric.ediam (realComp φ (List.ofFn u) '' I) ^ t
          ≤ ∑ u : Fin n → Fin N, ENNReal.ofReal (supDeriv φ (List.ofFn u) ^ t) := by
            refine Finset.sum_le_sum fun u _ => ?_
            rw [← ENNReal.ofReal_rpow_of_nonneg (hSpos _).le ht0.le]
            exact ENNReal.rpow_le_rpow (ediam_image_le hφ _) ht0.le
        _ = ENNReal.ofReal (∑ u : Fin n → Fin N, supDeriv φ (List.ofFn u) ^ t) :=
            (ENNReal.ofReal_sum_of_nonneg fun u _ => Real.rpow_nonneg (hSpos _).le t).symm
        _ ≤ ENNReal.ofReal (pressureSum φ s n * r ^ n) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [pressureSum, Finset.sum_mul]
            refine Finset.sum_le_sum fun u _ => ?_
            have hS := hSpos (List.ofFn u)
            have hle := (supDeriv_bounds hφ (List.ofFn u)).2.2
            rw [List.length_ofFn] at hle
            calc supDeriv φ (List.ofFn u) ^ t
                = supDeriv φ (List.ofFn u) ^ s * supDeriv φ (List.ofFn u) ^ (t - s) := by
                  rw [← Real.rpow_add hS, add_sub_cancel]
              _ ≤ supDeriv φ (List.ofFn u) ^ s * (c₁ ^ n) ^ (t - s) :=
                  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hS.le hle (sub_pos.2 hst).le)
                    (Real.rpow_nonneg hS.le s)
              _ = supDeriv φ (List.ofFn u) ^ s * r ^ n := by
                  rw [pow_rpow_eq_rpow_pow hc1.le]
    -- hence `𝓗^t(K) = 0`
    have hH : μH[t] K ≤ liminf (fun n : ℕ => ∑ u : Fin n → Fin N,
        Metric.ediam (realComp φ (List.ofFn u) '' I) ^ t) atTop := by
      refine Measure.hausdorffMeasure_le_liminf_sum t K (fun n => ENNReal.ofReal (c₁ ^ n)) ?_
        (fun n u => realComp φ (List.ofFn u) '' I) (Eventually.of_forall hdiam)
        (Eventually.of_forall fun n => (subset_iUnion_image hK n).trans
          (iUnion_mono fun u => image_mono hKI))
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one hc1.le hc1')
    have hH0 : μH[t] K = 0 := by
      refine le_antisymm (hH.trans ?_) bot_le
      rw [← hlim.liminf_eq]
      exact liminf_le_liminf (Eventually.of_forall hsum)
    exact dimH_le_of_hausdorffMeasure_ne_top (d := t.toNNReal)
      (by rw [Real.coe_toNNReal t ht0.le, hH0]; exact ENNReal.zero_ne_top)
  -- let `t ↓ s`
  have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have htend : Tendsto (fun k : ℕ => ENNReal.ofReal (s + 1 / ((k : ℝ) + 1))) atTop
      (𝓝 (ENNReal.ofReal s)) :=
    ENNReal.tendsto_ofReal (by simpa using (tendsto_const_nhds (x := s)).add h0)
  exact ge_of_tendsto' htend fun k => key _ (lt_add_of_pos_right s (by positivity))

/-- A subset of the line has Hausdorff dimension at most `1`. -/
theorem dimH_le_one (K : Set ℝ) : dimH K ≤ 1 := by
  simpa only [Real.dimH_univ] using dimH_mono (subset_univ K)

end FractalGeometry.Rapaport.Attractor
