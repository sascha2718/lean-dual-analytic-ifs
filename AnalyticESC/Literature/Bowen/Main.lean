module

public import Mathlib
public import AnalyticESC.Dimension.Defs
public import AnalyticESC.Literature.Bowen.Approximants
public import AnalyticESC.Literature.Bowen.Limit

@[expose] public section

/-!
# Bowen's theorem on Gibbs measures for the one-sided full shift

R. Bowen, *Equilibrium states and the ergodic theory of Anosov diffeomorphisms*, Lecture Notes in
Mathematics 470, Springer, 1975, Theorem 1.4, for the one-sided full shift `ℕ → Fin N` with
`N ≥ 1`: a potential `φ` whose variation on cylinders of length `k` is at most `b α^k`, with
`b > 0` and `0 < α < 1`, has a Gibbs probability measure `ν`, that is,

`c₁ ≤ ν[x₀ ⋯ x_{m-1}] / exp(-P m + S_m φ(x)) ≤ c₂`

for all `x` and `m ≥ 0`. The constant `P` is the pressure `lim (1/n) log Z_n` of
`FractalGeometry.Bowen.pressure`, and every Gibbs probability measure has this constant.

Proof: the potential has bounded distortion (`FractalGeometry.Bowen.Basic`), the partition sums
are almost multiplicative and define the pressure (`FractalGeometry.Bowen.PartitionSums`), the
measures `ν_M` weighting the words of length `M` satisfy the Gibbs bounds on cylinders of length
`≤ M` (`FractalGeometry.Bowen.Approximants`), and a weak-* limit point satisfies them on all
cylinders (`FractalGeometry.Bowen.Limit`).

## Main declarations

* `FractalGeometry.Bowen.HasBoundedDistortion.exists_gibbs`: Gibbs bounds with the constants
  `e^{∓3D}` and the pressure, for a potential with bounded distortion `D`.
* `FractalGeometry.Bowen.HasBoundedDistortion.exists_isGibbsMeasure`: the same in the form
  `AnalyticESC.IsGibbsMeasure`.
* `FractalGeometry.Bowen.pressure_eq_of_gibbs` and
  `FractalGeometry.Bowen.IsGibbsMeasure.exists_constants_pressure`: the constant `P` of any Gibbs
  probability measure is the pressure.
* `FractalGeometry.Bowen.bowenGibbsStatement_holds`: `AnalyticESC.BowenGibbsStatement`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Bowen.Main`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Bowen

open MeasureTheory Finset Filter Topology

variable {N : ℕ} [NeZero N] {φ : (ℕ → Fin N) → ℝ} {D : ℝ}

/-- A potential with bounded distortion `D` has a probability measure with
`e^{-3D} ≤ ν[x₀ ⋯ x_{m-1}] / exp(-P(φ) m + S_m φ(x)) ≤ e^{3D}` for all `x` and `m`, where
`P(φ)` is the pressure. -/
theorem HasBoundedDistortion.exists_gibbs (hD : HasBoundedDistortion φ D) :
    ∃ ν : Measure (ℕ → Fin N), IsProbabilityMeasure ν ∧ ∀ (x : ℕ → Fin N) (m : ℕ),
      Real.exp (-(3 * D)) * Real.exp (-pressure φ * m + birkhoff φ m x) ≤ ν.real (cyl x m) ∧
        ν.real (cyl x m) ≤ Real.exp (3 * D) * Real.exp (-pressure φ * m + birkhoff φ m x) :=
  exists_gibbs_of_forall_gibbsUpTo fun M => ⟨approxMeasure φ M,
    isProbabilityMeasure_approxMeasure φ M, fun x _ hm => hD.approxMeasure_gibbs hm x⟩

/-- A potential with bounded distortion has a Gibbs probability measure in the sense of
`AnalyticESC.IsGibbsMeasure`. -/
theorem HasBoundedDistortion.exists_isGibbsMeasure (hD : HasBoundedDistortion φ D) :
    ∃ ν : Measure (ℕ → Fin N), IsProbabilityMeasure ν ∧ AnalyticESC.IsGibbsMeasure φ ν := by
  obtain ⟨ν, hν, hg⟩ := hD.exists_gibbs
  exact ⟨ν, hν, Real.exp (-(3 * D)), Real.exp_pos _, Real.exp (3 * D), Real.exp_pos _,
    pressure φ, hg⟩

/-- The cylinders of length `n` partition the space: their masses sum to `1`. -/
theorem sum_measureReal_cyl (ν : Measure (ℕ → Fin N)) [IsProbabilityMeasure ν] (n : ℕ) :
    ∑ u : Fin n → Fin N, ν.real (cyl (ext0 u) n) = 1 := by
  have e : ∀ u : Fin n → Fin N,
      cyl (ext0 u) n = (fun y : ℕ → Fin N => fun i : Fin n => y i) ⁻¹' {u} := by
    intro u
    ext y
    simp only [mem_cyl, Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
    exact ⟨fun h i => (h i i.2).trans (ext0_fin u i),
      fun h i hi => (h ⟨i, hi⟩).trans (ext0_of_lt u hi).symm⟩
  simp_rw [e]
  rw [sum_measureReal_preimage_singleton _ fun u _ => e u ▸ measurableSet_cyl _ _]
  simp

/-- The constant `P` of a Gibbs probability measure is the pressure: summing the Gibbs bounds over
the cylinders of length `n` gives `c₁ e^{-n P} Z_n ≤ 1 ≤ c₂ e^{-n P} Z_n`. -/
theorem pressure_eq_of_gibbs (ν : Measure (ℕ → Fin N)) [IsProbabilityMeasure ν] {c₁ c₂ P : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h : ∀ (x : ℕ → Fin N) (m : ℕ),
      c₁ * Real.exp (-P * m + birkhoff φ m x) ≤ ν.real (cyl x m) ∧
        ν.real (cyl x m) ≤ c₂ * Real.exp (-P * m + birkhoff φ m x)) :
    P = pressure φ := by
  have key : ∀ n : ℕ,
      |Real.log (partitionSum φ n) - n * P| ≤ |Real.log c₁| + |Real.log c₂| := by
    intro n
    have hZ := partitionSum_pos φ n
    have hsum := sum_measureReal_cyl ν n
    have hlow : c₁ * Real.exp (-P * n) * partitionSum φ n ≤ 1 := by
      rw [← hsum, partitionSum, mul_sum]
      refine sum_le_sum fun u _ => ?_
      rw [mul_assoc, ← Real.exp_add]
      exact (h (ext0 u) n).1
    have hupp : 1 ≤ c₂ * Real.exp (-P * n) * partitionSum φ n := by
      rw [← hsum, partitionSum, mul_sum]
      refine sum_le_sum fun u _ => ?_
      rw [mul_assoc, ← Real.exp_add]
      exact (h (ext0 u) n).2
    have h1 := Real.log_le_log (by positivity) hlow
    have h2 := Real.log_le_log one_pos hupp
    rw [Real.log_mul (by positivity) hZ.ne', Real.log_mul hc₁.ne' (Real.exp_pos _).ne',
      Real.log_exp, Real.log_one] at h1
    rw [Real.log_mul (by positivity) hZ.ne', Real.log_mul hc₂.ne' (Real.exp_pos _).ne',
      Real.log_exp, Real.log_one] at h2
    have e : -P * n = -(n * P) := by ring
    rw [e] at h1 h2
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (Real.log c₁), le_abs_self (Real.log c₁),
      neg_abs_le (Real.log c₂), le_abs_self (Real.log c₂)]
  exact (tendsto_div_of_abs_sub_le key).limUnder_eq.symm

/-- Every Gibbs probability measure in the sense of `AnalyticESC.IsGibbsMeasure` satisfies the
Gibbs bounds with the pressure as the constant `P`. -/
theorem IsGibbsMeasure.exists_constants_pressure {ν : Measure (ℕ → Fin N)}
    [IsProbabilityMeasure ν] (hν : AnalyticESC.IsGibbsMeasure φ ν) :
    ∃ c₁ > 0, ∃ c₂ > 0, ∀ (x : ℕ → Fin N) (m : ℕ),
      c₁ * Real.exp (-pressure φ * m + ∑ k ∈ Finset.range m, φ (fun i => x (i + k))) ≤
          ν.real {y | ∀ i < m, y i = x i} ∧
        ν.real {y | ∀ i < m, y i = x i} ≤
          c₂ * Real.exp (-pressure φ * m + ∑ k ∈ Finset.range m, φ (fun i => x (i + k))) := by
  obtain ⟨c₁, hc₁, c₂, hc₂, P, h⟩ := hν
  obtain rfl : P = pressure φ := pressure_eq_of_gibbs ν hc₁ hc₂ h
  exact ⟨c₁, hc₁, c₂, hc₂, h⟩

/-- Bowen's Theorem 1.4 (LNM 470, 1975) for the one-sided full shift on `N ≥ 1` symbols, in the
form `AnalyticESC.BowenGibbsStatement`: a potential with variations `≤ b α^k` on cylinders of
length `k` has a Gibbs probability measure. -/
theorem bowenGibbsStatement_holds : AnalyticESC.BowenGibbsStatement := by
  intro N hN φ b α hb hα0 hα1 hvar
  have : NeZero N := ⟨hN.ne'⟩
  exact (HasExpVariation.hasBoundedDistortion hvar hb.le hα0.le hα1).exists_isGibbsMeasure

end FractalGeometry.Bowen
