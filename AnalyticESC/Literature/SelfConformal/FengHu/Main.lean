module

public import AnalyticESC.Literature.SelfConformal.FengHu.Statement
public import AnalyticESC.Literature.SelfConformal.FengHu.FibreEntropy

@[expose] public section

/-!
# Feng–Hu for self-conformal measures on the line

D.-J. Feng and H. Hu, *Dimension theory of iterated function systems*, Comm. Pure Appl. Math. 62
(2009), Theorem 2.8 and Proposition 4.10, for self-conformal measures on the line, in the form
used in Section 4 of A. Rapaport, *Dimension of self-conformal measures associated to an
exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2 (`FengHuInterface`).

For a `C^{1+Lip}` conformal system on `I = [0, 1]` and a positive probability vector `p`, the
self-conformal measure `μ` is exact dimensional with dimension `d = (H(p) - Δ) / χ`, where `Δ` is
the conditional information of the first letter given the coding, and for `μ`-a.e. `x` the fibre
measure `β_x` has cylinder entropy rate `Δ = H(p) - χ d`. The range `0 ≤ d ≤ 1` holds for every
exact dimensional probability measure on the line.

## Main declarations

* `fengHuInterface_of_conformalIFS`: the interface under the hypotheses `ConformalIFS φ c L`
  (no separation, no condition on fixed points).
* `fengHuInterface_holds`: the interface under `AnalyticESC.RapaportHyp φ`.
* `isExactDim_unique`: the exact dimension of a probability measure is unique.
* `ae_tendsto_neg_log_fibre_cylinder`: the pointwise form of Proposition 4.10,
  `-log β_{Π ω}[ω|_l] / l → H(p) - χ d` for `β`-a.e. `ω`, for the exact dimension `d` of `μ`.

Copied from the library `FractalGeometry` (module `FractalGeometry.SelfConformal.FengHu.Main`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.SelfConformal.FengHu

open MeasureTheory Filter Topology
open AnalyticESC (IsProbVec)

/-- `FengHuInterface` for a `C^{1+Lip}` conformal system on `I`. -/
theorem fengHuInterface_of_conformalIFS {N : ℕ} [NeZero N] {φ : Fin N → ℝ → ℝ} {c L : ℝ}
    (hφ : ConformalIFS φ c L) {p : Fin N → ℝ} (hp : IsProbVec p) : FengHuInterface φ p hp := by
  set Δ := ∫ ω, condInfo φ p hp ω ∂bernoulli p hp
  set χ := lyapunov φ p hp with hχ
  have hχ0 : χ ≠ 0 := (hφ.lyapunov_pos' hp).ne'
  have hd := hφ.isExactDim_selfConformal hp
  refine ⟨(AnalyticESC.entropy p - Δ) / χ, isExactDim_nonneg hd, isExactDim_le_one hd, hd, ?_⟩
  have heq : AnalyticESC.entropy p -
      (-∑ i, p i * ∫ y, Real.log |deriv (φ i) y| ∂selfConformal φ p hp) *
        ((AnalyticESC.entropy p - Δ) / χ) = Δ := by
    change AnalyticESC.entropy p - χ * ((AnalyticESC.entropy p - Δ) / χ) = Δ
    rw [mul_div_cancel₀ _ hχ0]
    ring
  rw [heq]
  exact hφ.ae_tendsto_cylEntropy_fibre hp

/-- **Feng–Hu, Theorem 2.8 and Proposition 4.10**, for the self-conformal measures of a system
satisfying Rapaport's hypotheses. -/
theorem fengHuInterface_holds {N : ℕ} [NeZero N] {φ : Fin N → ℝ → ℝ}
    (hφ : AnalyticESC.RapaportHyp φ) {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p) :
    FengHuInterface φ p hp := by
  obtain ⟨c, L, h⟩ := exists_conformalIFS_of_rapaportHyp hφ
  exact fengHuInterface_of_conformalIFS h hp

/-- The exact dimension of a probability measure is unique. -/
theorem isExactDim_unique {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {d d' : ℝ} (hd : FractalGeometry.IsExactDim μ d)
    (hd' : FractalGeometry.IsExactDim μ d') : d = d' := by
  obtain ⟨x, hx, hx'⟩ := (hd.and hd').exists
  exact tendsto_nhds_unique hx hx'

/-- **Feng–Hu, Proposition 4.10, pointwise form**: for a system satisfying Rapaport's hypotheses
and the exact dimension `d` of `μ`, `-log β_{Π ω}[ω|_l] / l → H(p) - χ d` for `β`-a.e. `ω`. -/
theorem ae_tendsto_neg_log_fibre_cylinder {N : ℕ} [NeZero N] {φ : Fin N → ℝ → ℝ}
    (hφ : AnalyticESC.RapaportHyp φ) {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p) {d : ℝ}
    (hd : FractalGeometry.IsExactDim (selfConformal φ p hp) d) :
    ∀ᵐ ω ∂bernoulli p hp, Tendsto (fun l : ℕ =>
      -Real.log ((fibre φ p hp (coding φ ω)).real (cylinder fun k : Fin l => ω k)) / l) atTop
        (𝓝 (AnalyticESC.entropy p -
          (-∑ i, p i * ∫ y, Real.log |deriv (φ i) y| ∂(selfConformal φ p hp)) * d)) := by
  obtain ⟨c, L, h⟩ := exists_conformalIFS_of_rapaportHyp hφ
  have hd0 := h.isExactDim_selfConformal hp
  have hχ0 : lyapunov φ p hp ≠ 0 := (h.lyapunov_pos' hp).ne'
  rw [isExactDim_unique hd hd0]
  have heq : AnalyticESC.entropy p -
      (-∑ i, p i * ∫ y, Real.log |deriv (φ i) y| ∂selfConformal φ p hp) *
        ((AnalyticESC.entropy p - ∫ ω, condInfo φ p hp ω ∂bernoulli p hp) / lyapunov φ p hp) =
      ∫ ω, condInfo φ p hp ω ∂bernoulli p hp := by
    change AnalyticESC.entropy p - lyapunov φ p hp * ((AnalyticESC.entropy p -
      ∫ ω, condInfo φ p hp ω ∂bernoulli p hp) / lyapunov φ p hp) = _
    rw [mul_div_cancel₀ _ hχ0]
    ring
  rw [heq]
  exact h.ae_tendsto_cylInfo_fibre hp

end FractalGeometry.SelfConformal.FengHu
