module

public import Mathlib
public import AnalyticESC.Literature.Bowen.PartitionSums

@[expose] public section

/-!
# Bowen's theorem on the one-sided full shift: finite-level approximants

For each level `M`, the probability measure

`ν_M = ∑_{|u| = M} (exp S_M φ(u 0 0 ⋯) / Z_M) δ_{u 0 0 ⋯}`

on the one-sided full shift `ℕ → Fin N` satisfies the Gibbs bounds of

R. Bowen, *Equilibrium states and the ergodic theory of Anosov diffeomorphisms*, Lecture Notes in
Mathematics 470, Springer, 1975, Theorem 1.4,

for every cylinder of length `m ≤ M`, with constants `e^{∓3D}` that do not depend on `M`. The
measures play the role of the periodic-point measures in the proof of Bowen's Theorem 1.4 (and of
`FractalGeometry.Pressure.ParityShift.PeriodicMeasures`).

## Main declarations

* `FractalGeometry.Bowen.approxMeasure φ M`: the measure `ν_M`.
* `FractalGeometry.Bowen.isProbabilityMeasure_approxMeasure`.
* `FractalGeometry.Bowen.approxMeasure_real_cyl`:
  `ν_{m+k}[x₀ ⋯ x_{m-1}] = cylSum φ x m k / Z_{m+k}`.
* `FractalGeometry.Bowen.HasBoundedDistortion.approxMeasure_gibbs`: the Gibbs bounds for `ν_M`
  on cylinders of length `m ≤ M`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Bowen.Approximants`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Bowen

open Finset MeasureTheory

variable {N : ℕ} [NeZero N]

section Measure

variable (φ : (ℕ → Fin N) → ℝ)

/-- The weight `exp S_M φ(u 0 0 ⋯) / Z_M` of a word `u` of length `M`. -/
noncomputable def weight (M : ℕ) (u : Fin M → Fin N) : ℝ :=
  Real.exp (birkhoff φ M (ext0 u)) / partitionSum φ M

/-- Weights are nonnegative. -/
theorem weight_nonneg (M : ℕ) (u : Fin M → Fin N) : 0 ≤ weight φ M u :=
  div_nonneg (Real.exp_pos _).le (partitionSum_pos φ M).le

/-- The weights of the words of length `M` sum to `1`. -/
theorem sum_weight (M : ℕ) : ∑ u : Fin M → Fin N, weight φ M u = 1 := by
  unfold weight
  rw [← sum_div]
  exact div_self (partitionSum_pos φ M).ne'

/-- The finite-level approximant `ν_M = ∑_{|u| = M} weight φ M u • δ_{u 0 0 ⋯}`. -/
noncomputable def approxMeasure (M : ℕ) : Measure (ℕ → Fin N) :=
  ∑ u : Fin M → Fin N, ENNReal.ofReal (weight φ M u) • Measure.dirac (ext0 u)

open Classical in
/-- The mass of a set under `ν_M`, as an extended real. -/
theorem approxMeasure_apply (M : ℕ) (s : Set (ℕ → Fin N)) :
    approxMeasure φ M s =
      ENNReal.ofReal (∑ u : Fin M → Fin N, if ext0 u ∈ s then weight φ M u else 0) := by
  rw [ENNReal.ofReal_sum_of_nonneg fun u _ => by
    split_ifs
    · exact weight_nonneg φ M u
    · exact le_rfl]
  simp only [approxMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply, smul_eq_mul]
  refine sum_congr rfl fun u _ => ?_
  by_cases hu : ext0 u ∈ s <;> simp [hu]

open Classical in
/-- The mass of a set under `ν_M`. -/
theorem approxMeasure_real (M : ℕ) (s : Set (ℕ → Fin N)) :
    (approxMeasure φ M).real s =
      ∑ u : Fin M → Fin N, if ext0 u ∈ s then weight φ M u else 0 := by
  rw [measureReal_def, approxMeasure_apply, ENNReal.toReal_ofReal]
  refine sum_nonneg fun u _ => ?_
  split_ifs
  · exact weight_nonneg φ M u
  · exact le_rfl

/-- `ν_M` is a probability measure. -/
theorem isProbabilityMeasure_approxMeasure (M : ℕ) : IsProbabilityMeasure (approxMeasure φ M) :=
  ⟨by simp [approxMeasure_apply, sum_weight]⟩

/-- The mass of a cylinder of length `m` under `ν_{m+k}` is the cylinder sum divided by the
partition sum. -/
theorem approxMeasure_real_cyl (x : ℕ → Fin N) (m k : ℕ) :
    (approxMeasure φ (m + k)).real (cyl x m) = cylSum φ x m k / partitionSum φ (m + k) := by
  classical
  rw [approxMeasure_real]
  calc ∑ u : Fin (m + k) → Fin N, (if ext0 u ∈ cyl x m then weight φ (m + k) u else 0)
      = ∑ p : (Fin m → Fin N) × (Fin k → Fin N),
          if ext0 (Fin.append p.1 p.2) ∈ cyl x m then weight φ (m + k) (Fin.append p.1 p.2)
            else 0 :=
        (Fintype.sum_equiv (Fin.appendEquiv m k) _ _ fun p => rfl).symm
    _ = ∑ v : Fin m → Fin N, ∑ w : Fin k → Fin N,
          if ext0 (Fin.append v w) ∈ cyl x m then weight φ (m + k) (Fin.append v w) else 0 :=
        Fintype.sum_prod_type _
    _ = ∑ w : Fin k → Fin N, weight φ (m + k) (Fin.append (fun i : Fin m => x i) w) := by
        simp only [ext0_append_mem_cyl_iff]
        rw [Fintype.sum_eq_single (fun i : Fin m => x i)]
        · simp
        · intro v hv
          simp [hv]
    _ = cylSum φ x m k / partitionSum φ (m + k) := by
        rw [cylSum, sum_div]
        rfl

end Measure

variable {φ : (ℕ → Fin N) → ℝ} {D : ℝ}

/-- The Gibbs bounds for the approximant `ν_M` on cylinders of length `m ≤ M`:
`e^{-3D} ≤ ν_M[x₀ ⋯ x_{m-1}] / exp(-P(φ) m + S_m φ(x)) ≤ e^{3D}`. -/
theorem HasBoundedDistortion.approxMeasure_gibbs (hD : HasBoundedDistortion φ D) {m M : ℕ}
    (hm : m ≤ M) (x : ℕ → Fin N) :
    Real.exp (-(3 * D)) * Real.exp (-pressure φ * m + birkhoff φ m x) ≤
        (approxMeasure φ M).real (cyl x m) ∧
      (approxMeasure φ M).real (cyl x m) ≤
        Real.exp (3 * D) * Real.exp (-pressure φ * m + birkhoff φ m x) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [approxMeasure_real_cyl]
  have hT := cylSum_bounds hD x m k
  have hk := abs_le.1 (hD.abs_log_partitionSum_sub_le k)
  have hmk := abs_le.1 (hD.abs_log_partitionSum_sub_le (m + k))
  have hZk := partitionSum_pos φ k
  have hZ := partitionSum_pos φ (m + k)
  have e1 : ((m + k : ℕ) : ℝ) * pressure φ = m * pressure φ + k * pressure φ := by
    push_cast
    ring
  have e2 : -pressure φ * m = -(m * pressure φ) := by ring
  rw [e1] at hmk
  constructor
  · rw [le_div_iff₀ hZ]
    calc Real.exp (-(3 * D)) * Real.exp (-pressure φ * m + birkhoff φ m x) *
          partitionSum φ (m + k)
        = Real.exp (-(3 * D) + (-pressure φ * m + birkhoff φ m x) +
            Real.log (partitionSum φ (m + k))) := by
          simp only [Real.exp_add, Real.exp_log hZ, mul_assoc]
      _ ≤ Real.exp (birkhoff φ m x - D + Real.log (partitionSum φ k)) :=
          Real.exp_le_exp.2 (by rw [e2]; linarith)
      _ = Real.exp (birkhoff φ m x - D) * partitionSum φ k := by
          rw [Real.exp_add, Real.exp_log hZk]
      _ ≤ cylSum φ x m k := hT.1
  · rw [div_le_iff₀ hZ]
    calc cylSum φ x m k ≤ Real.exp (birkhoff φ m x + D) * partitionSum φ k := hT.2
      _ = Real.exp (birkhoff φ m x + D + Real.log (partitionSum φ k)) := by
          simp only [Real.exp_add, Real.exp_log hZk, mul_assoc]
      _ ≤ Real.exp (3 * D + (-pressure φ * m + birkhoff φ m x) +
            Real.log (partitionSum φ (m + k))) :=
          Real.exp_le_exp.2 (by rw [e2]; linarith)
      _ = Real.exp (3 * D) * Real.exp (-pressure φ * m + birkhoff φ m x) *
            partitionSum φ (m + k) := by
          simp only [Real.exp_add, Real.exp_log hZ, mul_assoc]

end FractalGeometry.Bowen
