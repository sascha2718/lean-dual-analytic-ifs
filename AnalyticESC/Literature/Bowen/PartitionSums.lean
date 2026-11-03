module

public import Mathlib
public import AnalyticESC.Literature.Bowen.Basic

@[expose] public section

/-!
# Bowen's theorem on the one-sided full shift: partition sums and pressure

Partition sums and the topological pressure of a potential with bounded distortion on the
one-sided full shift `ℕ → Fin N`, as in the proof of

R. Bowen, *Equilibrium states and the ergodic theory of Anosov diffeomorphisms*, Lecture Notes in
Mathematics 470, Springer, 1975, Theorem 1.4 (Lemma 1.20 and its proof).

The partition sum `Z_n = ∑_{|u| = n} exp S_n φ(u 0 0 ⋯)` is almost multiplicative,
`e^{-D} Z_m Z_k ≤ Z_{m+k} ≤ e^D Z_m Z_k`, so by Fekete's lemma applied to `log Z_n ± D` the
pressure `P = lim (1/n) log Z_n` exists and `|log Z_n - n P| ≤ D` for every `n`.

The argument is adapted from `FractalGeometry.Pressure.ParityShift.HolderPotential`.

## Main declarations

* `FractalGeometry.Bowen.partitionSum φ n`: the partition sum `Z_n`.
* `FractalGeometry.Bowen.cylSum φ x m k`: the part of `Z_{m+k}` over the cylinder `[x₀ ⋯ x_{m-1}]`.
* `FractalGeometry.Bowen.cylSum_bounds`: `e^{S_m φ(x) ∓ D} Z_k` bound the cylinder sum.
* `FractalGeometry.Bowen.exists_tendsto_div_of_almost_additive`: Fekete's lemma for almost
  additive sequences, with the error bound `|a_n - n P| ≤ D`.
* `FractalGeometry.Bowen.pressure φ`: the pressure `lim (1/n) log Z_n`.
* `FractalGeometry.Bowen.HasBoundedDistortion.tendsto_pressure` and
  `FractalGeometry.Bowen.HasBoundedDistortion.abs_log_partitionSum_sub_le`.
* `FractalGeometry.Bowen.HasBoundedDistortion.tendsto_log_sum_exp_div`: the pressure is the limit
  of `(1/n) log ∑_{|u| = n} exp S_n φ(x_u)` for any choice of points `x_u ∈ [u]`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Bowen.PartitionSums`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Bowen

open Finset Filter Topology

section Fekete

/-- A sequence with `|a_n - n P| ≤ C` for all `n` satisfies `a_n / n → P`. -/
theorem tendsto_div_of_abs_sub_le {a : ℕ → ℝ} {P C : ℝ} (h : ∀ n, |a n - n * P| ≤ C) :
    Tendsto (fun n : ℕ => a n / n) atTop (𝓝 P) := by
  have hlow : Tendsto (fun n : ℕ => P - C / n) atTop (𝓝 P) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat C)
  have hupp : Tendsto (fun n : ℕ => P + C / n) atTop (𝓝 P) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat C)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hn', sub_mul, div_mul_cancel₀ _ hn'.ne']
    linarith [(abs_le.1 (h n)).1, mul_comm P (n : ℝ)]
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']
    linarith [(abs_le.1 (h n)).2, mul_comm P (n : ℝ)]

/-- A subadditive sequence satisfies `u_n ≤ n u_1` for `n ≥ 1`. -/
theorem subadditive_le_mul_one {u : ℕ → ℝ} (h : Subadditive u) :
    ∀ n : ℕ, 1 ≤ n → u n ≤ n * u 1 := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · have := h n 1
      push_cast
      nlinarith [ih hpos]

/-- The quotients `u_n / n` of a sequence with `v_n ≤ n v_1` for `v_n = c - u_n` and some
`c ≥ 0` are bounded below. -/
theorem bddBelow_div_of_le_mul {u v : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (huv : ∀ n, u n = c - v n)
    (hv : ∀ n : ℕ, 1 ≤ n → v n ≤ n * v 1) :
    BddBelow (Set.range fun n : ℕ => u n / n) := by
  refine ⟨min 0 (-v 1), ?_⟩
  rintro _ ⟨n, rfl⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine (min_le_right _ _).trans ?_
    rw [le_div_iff₀ hn', huv]
    nlinarith [hv n hn]

/-- Fekete's lemma for almost additive sequences: if
`a_m + a_n - D ≤ a_{m+n} ≤ a_m + a_n + D`, then `a_n / n` converges to some `P` and
`|a_n - n P| ≤ D` for every `n`. -/
theorem exists_tendsto_div_of_almost_additive {a : ℕ → ℝ} {D : ℝ}
    (h1 : ∀ m n, a (m + n) ≤ a m + a n + D) (h2 : ∀ m n, a m + a n - D ≤ a (m + n)) :
    ∃ P : ℝ, Tendsto (fun n : ℕ => a n / n) atTop (𝓝 P) ∧ ∀ n, |a n - n * P| ≤ D := by
  have h10 := h1 0 0
  have h20 := h2 0 0
  simp only [add_zero] at h10 h20
  have hD : 0 ≤ D := by linarith
  set u : ℕ → ℝ := fun n => a n + D with hu_def
  set v : ℕ → ℝ := fun n => D - a n with hv_def
  have hu : Subadditive u := fun m n => by simp only [u]; linarith [h1 m n]
  have hv : Subadditive v := fun m n => by simp only [v]; linarith [h2 m n]
  have hu_bdd : BddBelow (Set.range fun n : ℕ => u n / n) :=
    bddBelow_div_of_le_mul (by linarith : 0 ≤ 2 * D) (fun n => by simp only [u, v]; ring)
      (subadditive_le_mul_one hv)
  have hv_bdd : BddBelow (Set.range fun n : ℕ => v n / n) :=
    bddBelow_div_of_le_mul (by linarith : 0 ≤ 2 * D) (fun n => by simp only [u, v]; ring)
      (subadditive_le_mul_one hu)
  have hut := hu.tendsto_lim hu_bdd
  have hvt := hv.tendsto_lim hv_bdd
  have hsum : hu.lim + hv.lim = 0 := by
    have h := hut.add hvt
    have e : (fun n : ℕ => u n / n + v n / n) = fun n : ℕ => (2 * D) / n := by
      funext n
      rw [← add_div]
      congr 1
      simp only [u, v]
      ring
    rw [e] at h
    exact tendsto_nhds_unique h (tendsto_const_div_atTop_nhds_zero_nat _)
  have hbound : ∀ n, |a n - n * hu.lim| ≤ D := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [abs_le]
      constructor <;> simp <;> linarith
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hlu := hu.lim_le_div hu_bdd hn.ne'
      have hlv := hv.lim_le_div hv_bdd hn.ne'
      rw [le_div_iff₀ hn'] at hlu hlv
      simp only [u, v] at hlu hlv
      rw [abs_le]
      constructor <;> nlinarith
  exact ⟨hu.lim, tendsto_div_of_abs_sub_le hbound, hbound⟩

end Fekete

variable {N : ℕ} [NeZero N]

section Sums

variable (φ : (ℕ → Fin N) → ℝ)

/-- The partition sum `Z_n = ∑_{|u| = n} exp S_n φ(u 0 0 ⋯)`. -/
noncomputable def partitionSum (n : ℕ) : ℝ :=
  ∑ u : Fin n → Fin N, Real.exp (birkhoff φ n (ext0 u))

/-- The part of the partition sum `Z_{m+k}` over the words that start with `x₀ ⋯ x_{m-1}`. -/
noncomputable def cylSum (x : ℕ → Fin N) (m k : ℕ) : ℝ :=
  ∑ w : Fin k → Fin N,
    Real.exp (birkhoff φ (m + k) (ext0 (Fin.append (fun i : Fin m => x i) w)))

/-- Partition sums are positive. -/
theorem partitionSum_pos (n : ℕ) : 0 < partitionSum φ n :=
  sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty

/-- The partition sum of length `0` is `1`. -/
@[simp] theorem partitionSum_zero : partitionSum φ 0 = 1 := by
  simp [partitionSum]

/-- Splitting the words of length `m + k` according to their first `m` letters. -/
theorem partitionSum_add (m k : ℕ) :
    partitionSum φ (m + k) = ∑ v : Fin m → Fin N, cylSum φ (ext0 v) m k := by
  calc partitionSum φ (m + k)
      = ∑ p : (Fin m → Fin N) × (Fin k → Fin N),
          Real.exp (birkhoff φ (m + k) (ext0 (Fin.append p.1 p.2))) :=
        (Fintype.sum_equiv (Fin.appendEquiv m k) _ _ fun p => rfl).symm
    _ = ∑ v : Fin m → Fin N, ∑ w : Fin k → Fin N,
          Real.exp (birkhoff φ (m + k) (ext0 (Fin.append v w))) := Fintype.sum_prod_type _
    _ = ∑ v : Fin m → Fin N, cylSum φ (ext0 v) m k := by
        simp only [cylSum, restrict_ext0]

variable {φ} {D : ℝ}

/-- The cylinder sums are comparable to `e^{S_m φ(x)} Z_k`, with the factor `e^{±D}`. -/
theorem cylSum_bounds (hD : HasBoundedDistortion φ D) (x : ℕ → Fin N) (m k : ℕ) :
    Real.exp (birkhoff φ m x - D) * partitionSum φ k ≤ cylSum φ x m k ∧
      cylSum φ x m k ≤ Real.exp (birkhoff φ m x + D) * partitionSum φ k := by
  unfold cylSum partitionSum
  rw [mul_sum, mul_sum]
  have key : ∀ w : Fin k → Fin N,
      |birkhoff φ m (ext0 (Fin.append (fun i : Fin m => x i) w)) - birkhoff φ m x| ≤ D :=
    fun w => hD m _ _ fun i hi => ext0_append_of_lt _ w hi
  constructor <;> refine sum_le_sum fun w _ => ?_ <;> rw [← Real.exp_add] <;>
    refine Real.exp_le_exp.2 ?_ <;> rw [birkhoff_add, ext0_append_shift] <;>
    linarith [(abs_le.1 (key w)).1, (abs_le.1 (key w)).2]

/-- Upper almost multiplicativity of the partition sums. -/
theorem partitionSum_add_le (hD : HasBoundedDistortion φ D) (m k : ℕ) :
    partitionSum φ (m + k) ≤ Real.exp D * partitionSum φ m * partitionSum φ k := by
  rw [partitionSum_add]
  calc ∑ v : Fin m → Fin N, cylSum φ (ext0 v) m k
      ≤ ∑ v : Fin m → Fin N, Real.exp (birkhoff φ m (ext0 v) + D) * partitionSum φ k :=
        sum_le_sum fun v _ => (cylSum_bounds hD (ext0 v) m k).2
    _ = Real.exp D * partitionSum φ m * partitionSum φ k := by
        rw [show partitionSum φ m = ∑ v : Fin m → Fin N, Real.exp (birkhoff φ m (ext0 v)) from rfl,
          mul_sum, sum_mul]
        refine sum_congr rfl fun v _ => ?_
        rw [Real.exp_add]
        ring

/-- Lower almost multiplicativity of the partition sums. -/
theorem le_partitionSum_add (hD : HasBoundedDistortion φ D) (m k : ℕ) :
    Real.exp (-D) * partitionSum φ m * partitionSum φ k ≤ partitionSum φ (m + k) := by
  rw [partitionSum_add]
  calc Real.exp (-D) * partitionSum φ m * partitionSum φ k
      = ∑ v : Fin m → Fin N, Real.exp (birkhoff φ m (ext0 v) - D) * partitionSum φ k := by
        rw [show partitionSum φ m = ∑ v : Fin m → Fin N, Real.exp (birkhoff φ m (ext0 v)) from rfl,
          mul_sum, sum_mul]
        refine sum_congr rfl fun v _ => ?_
        rw [sub_eq_add_neg, Real.exp_add]
        ring
    _ ≤ ∑ v : Fin m → Fin N, cylSum φ (ext0 v) m k :=
        sum_le_sum fun v _ => (cylSum_bounds hD (ext0 v) m k).1

/-- Upper almost additivity of `log Z_n`. -/
theorem log_partitionSum_add_le (hD : HasBoundedDistortion φ D) (m k : ℕ) :
    Real.log (partitionSum φ (m + k)) ≤
      Real.log (partitionSum φ m) + Real.log (partitionSum φ k) + D := by
  have hm := partitionSum_pos φ m
  have hk := partitionSum_pos φ k
  have h := Real.log_le_log (partitionSum_pos φ _) (partitionSum_add_le hD m k)
  rw [Real.log_mul (by positivity) hk.ne', Real.log_mul (Real.exp_pos _).ne' hm.ne',
    Real.log_exp] at h
  linarith

/-- Lower almost additivity of `log Z_n`. -/
theorem le_log_partitionSum_add (hD : HasBoundedDistortion φ D) (m k : ℕ) :
    Real.log (partitionSum φ m) + Real.log (partitionSum φ k) - D ≤
      Real.log (partitionSum φ (m + k)) := by
  have hm := partitionSum_pos φ m
  have hk := partitionSum_pos φ k
  have h := Real.log_le_log (by positivity) (le_partitionSum_add hD m k)
  rw [Real.log_mul (by positivity) hk.ne', Real.log_mul (Real.exp_pos _).ne' hm.ne',
    Real.log_exp] at h
  linarith

end Sums

section Pressure

variable (φ : (ℕ → Fin N) → ℝ)

/-- The topological pressure `P(φ) = lim_n (1/n) log Z_n` (the limit exists for potentials with
bounded distortion, see `HasBoundedDistortion.tendsto_pressure`). -/
noncomputable def pressure : ℝ :=
  limUnder atTop fun n : ℕ => Real.log (partitionSum φ n) / n

variable {φ} {D : ℝ}

/-- The pressure is the limit of the normalised logarithmic partition sums, and the logarithmic
partition sums are within `D` of `n P(φ)`. -/
theorem HasBoundedDistortion.tendsto_pressure_and_abs_le (hD : HasBoundedDistortion φ D) :
    Tendsto (fun n : ℕ => Real.log (partitionSum φ n) / n) atTop (𝓝 (pressure φ)) ∧
      ∀ n : ℕ, |Real.log (partitionSum φ n) - n * pressure φ| ≤ D := by
  obtain ⟨P, hP, hb⟩ := exists_tendsto_div_of_almost_additive (log_partitionSum_add_le hD)
    (le_log_partitionSum_add hD)
  have e : pressure φ = P := hP.limUnder_eq
  rw [e]
  exact ⟨hP, hb⟩

/-- The pressure is the limit of `(1/n) log Z_n`. -/
theorem HasBoundedDistortion.tendsto_pressure (hD : HasBoundedDistortion φ D) :
    Tendsto (fun n : ℕ => Real.log (partitionSum φ n) / n) atTop (𝓝 (pressure φ)) :=
  hD.tendsto_pressure_and_abs_le.1

/-- `|log Z_n - n P(φ)| ≤ D` for every `n`. -/
theorem HasBoundedDistortion.abs_log_partitionSum_sub_le (hD : HasBoundedDistortion φ D)
    (n : ℕ) : |Real.log (partitionSum φ n) - n * pressure φ| ≤ D :=
  hD.tendsto_pressure_and_abs_le.2 n

/-- `e^{n P(φ) - D} ≤ Z_n ≤ e^{n P(φ) + D}` for every `n`. -/
theorem HasBoundedDistortion.partitionSum_bounds (hD : HasBoundedDistortion φ D) (n : ℕ) :
    Real.exp (n * pressure φ - D) ≤ partitionSum φ n ∧
      partitionSum φ n ≤ Real.exp (n * pressure φ + D) := by
  have h := abs_le.1 (hD.abs_log_partitionSum_sub_le n)
  have hZ := partitionSum_pos φ n
  constructor
  · rw [← Real.exp_log hZ]
    exact Real.exp_le_exp.2 (by linarith)
  · rw [← Real.exp_log hZ]
    exact Real.exp_le_exp.2 (by linarith)

/-- The pressure does not depend on the choice of points in the cylinders: if `x_u ∈ [u]` for
every word `u`, then `(1/n) log ∑_{|u| = n} exp S_n φ(x_u) → P(φ)`; more precisely
`|log ∑_{|u| = n} exp S_n φ(x_u) - n P(φ)| ≤ 2 D`. -/
theorem HasBoundedDistortion.abs_log_sum_exp_sub_le (hD : HasBoundedDistortion φ D)
    (pt : ∀ n : ℕ, (Fin n → Fin N) → ℕ → Fin N) (hpt : ∀ n u (i : Fin n), pt n u i = u i)
    (n : ℕ) :
    |Real.log (∑ u : Fin n → Fin N, Real.exp (birkhoff φ n (pt n u))) - n * pressure φ| ≤
      2 * D := by
  have key : ∀ u : Fin n → Fin N, |birkhoff φ n (pt n u) - birkhoff φ n (ext0 u)| ≤ D :=
    fun u => hD n _ _ fun i hi => (hpt n u ⟨i, hi⟩).trans (ext0_of_lt u hi).symm
  have hlow : Real.exp (-D) * partitionSum φ n ≤
      ∑ u : Fin n → Fin N, Real.exp (birkhoff φ n (pt n u)) := by
    rw [partitionSum, mul_sum]
    refine sum_le_sum fun u _ => ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [(abs_le.1 (key u)).1])
  have hupp : ∑ u : Fin n → Fin N, Real.exp (birkhoff φ n (pt n u)) ≤
      Real.exp D * partitionSum φ n := by
    rw [partitionSum, mul_sum]
    refine sum_le_sum fun u _ => ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [(abs_le.1 (key u)).2])
  have hZ := partitionSum_pos φ n
  have hS : 0 < ∑ u : Fin n → Fin N, Real.exp (birkhoff φ n (pt n u)) :=
    sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty
  have h1 := Real.log_le_log (by positivity) hlow
  have h2 := Real.log_le_log hS hupp
  rw [Real.log_mul (Real.exp_pos _).ne' hZ.ne', Real.log_exp] at h1 h2
  have h3 := abs_le.1 (hD.abs_log_partitionSum_sub_le n)
  rw [abs_le]
  constructor <;> linarith

/-- The pressure is the limit of `(1/n) log ∑_{|u| = n} exp S_n φ(x_u)` for any choice of points
`x_u ∈ [u]`. -/
theorem HasBoundedDistortion.tendsto_log_sum_exp_div (hD : HasBoundedDistortion φ D)
    (pt : ∀ n : ℕ, (Fin n → Fin N) → ℕ → Fin N) (hpt : ∀ n u (i : Fin n), pt n u i = u i) :
    Tendsto (fun n : ℕ => Real.log (∑ u : Fin n → Fin N, Real.exp (birkhoff φ n (pt n u))) / n)
      atTop (𝓝 (pressure φ)) :=
  tendsto_div_of_abs_sub_le (hD.abs_log_sum_exp_sub_le pt hpt)

end Pressure

end FractalGeometry.Bowen
