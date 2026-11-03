module

public import AnalyticESC.Literature.Rapaport.Analytic.Main.Statements

@[expose] public section

/-!
# Assembly of Rapaport's Theorem 1.2

The deduction of Theorem 1.2 of A. Rapaport, *Dimension of self-conformal measures associated to
an exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2, in the form
`AnalyticESC.RapaportMeasureStatement`, from the results of D.-J. Feng and H. Hu, *Dimension
theory of iterated function systems*, Comm. Pure Appl. Math. 62 (2009), Theorem 2.8 and
Proposition 4.10 (`FengHuInterface`), and from the vanishing of the fibre entropy below dimension
`1` proved in Section 4 of Rapaport (`FibreEntropyVanishes`).

## Main declarations

* `fibreRate_nonneg`: the cylinder entropy rate of the fibres is nonnegative, so `χ dim μ ≤ H(p)`.
* `dim_eq_min_of_vanishes`: `dim μ = min {1, H(p)/χ}`.
* `rapaportMeasure_of_vanishes`: `AnalyticESC.RapaportMeasureStatement` from `FengHuInterface`
  and `FibreEntropyVanishes`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Main.Assembly`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic

open MeasureTheory Set Filter Topology FractalGeometry.SelfConformal

variable {N : ℕ}

/-- The cylinder entropy of a probability measure on `(Fin N)^ℕ` is nonnegative. -/
theorem cylEntropy_nonneg (ν : Measure (ℕ → Fin N)) [IsProbabilityMeasure ν] (l : ℕ) :
    0 ≤ cylEntropy ν l :=
  Finset.sum_nonneg fun _ _ =>
    Real.negMulLog_nonneg measureReal_nonneg (measureReal_le_one)

/-- The cylinder entropy rate of the fibres is nonnegative. -/
theorem fibreRate_nonneg [NeZero N] {φ : Fin N → ℝ → ℝ} {p : Fin N → ℝ}
    (hp : AnalyticESC.IsProbVec p) {Δ' : ℝ}
    (h : ∀ᵐ x ∂(selfConformal φ p hp),
      Tendsto (fun l : ℕ => cylEntropy (fibre φ p hp x) l / l) atTop (𝓝 Δ')) :
    0 ≤ Δ' := by
  obtain ⟨x, hx⟩ := h.exists
  exact ge_of_tendsto' hx fun l => div_nonneg (cylEntropy_nonneg _ l) (Nat.cast_nonneg l)

/-- Theorem 1.2 of Rapaport (arXiv:2412.16753v2) for the self-conformal measure `μ`:
`dim μ = min {1, H(p)/χ}`, from `FengHuInterface` and `FibreEntropyVanishes`. -/
theorem dim_eq_min_of_vanishes [NeZero N] {φ : Fin N → ℝ → ℝ} (hφ : AnalyticESC.RapaportHyp φ)
    {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p) (hFH : FengHuInterface φ p hp)
    (hV : FibreEntropyVanishes φ p hp) :
    FractalGeometry.IsExactDim (selfConformal φ p hp)
      (min 1 (AnalyticESC.entropy p / lyapunov φ p hp)) := by
  obtain ⟨d, _hd0, hd1, hdim, hfib⟩ := hFH
  have hχpos := lyapunov_pos hφ hp
  have hfib' : ∀ᵐ x ∂(selfConformal φ p hp),
      Tendsto (fun l : ℕ => cylEntropy (fibre φ p hp x) l / l) atTop
        (𝓝 (AnalyticESC.entropy p - lyapunov φ p hp * d)) := hfib
  have hnn := fibreRate_nonneg hp hfib'
  have hle : d ≤ AnalyticESC.entropy p / lyapunov φ p hp := by
    rw [le_div_iff₀ hχpos]
    linarith
  have heq : d = min 1 (AnalyticESC.entropy p / lyapunov φ p hp) := by
    rcases hd1.lt_or_eq with hlt | heq
    · have h0 := hV d _ hdim hlt hfib'
      have hge : AnalyticESC.entropy p / lyapunov φ p hp ≤ d := by
        rw [div_le_iff₀ hχpos]
        linarith
      have hde : d = AnalyticESC.entropy p / lyapunov φ p hp := le_antisymm hle hge
      rw [min_eq_right (hde ▸ hlt.le), hde]
    · rw [heq] at hle ⊢
      rw [min_eq_left hle]
  rwa [← heq]

/-- `AnalyticESC.RapaportMeasureStatement` (Theorem 1.2 of Rapaport, arXiv:2412.16753v2, with the
exact dimensionality of Feng and Hu), from `FengHuInterface` and `FibreEntropyVanishes` for every
system satisfying `AnalyticESC.RapaportHyp`. The measure of the statement is identified with
`selfConformal φ p hp` by uniqueness (`eq_selfConformal`). -/
theorem rapaportMeasure_of_vanishes
    (hFH : ∀ {N : ℕ} [NeZero N] (φ : Fin N → ℝ → ℝ), AnalyticESC.RapaportHyp φ →
      ∀ (p : Fin N → ℝ) (hp : AnalyticESC.IsProbVec p), FengHuInterface φ p hp)
    (hV : ∀ {N : ℕ} [NeZero N] (φ : Fin N → ℝ → ℝ), AnalyticESC.RapaportHyp φ →
      ∀ (p : Fin N → ℝ) (hp : AnalyticESC.IsProbVec p), FibreEntropyVanishes φ p hp) :
    AnalyticESC.RapaportMeasureStatement := by
  intro N φ hφ p hp0 hp1 μ hμ hμI hμfix hχ
  have hp : AnalyticESC.IsProbVec p := ⟨hp0, hp1⟩
  have : NeZero N := neZero_of_isProbVec hp
  obtain rfl : μ = selfConformal φ p hp := eq_selfConformal hφ hp hμI hμfix
  have hdim := dim_eq_min_of_vanishes hφ hp (hFH φ hφ p hp) (hV φ hφ p hp)
  filter_upwards [hdim] with x hx
  have hval : AnalyticESC.divide (-∑ i, p i * Real.log (p i))
      (-∑ i, p i * ∫ y, Real.log |deriv (φ i) y| ∂(selfConformal φ p hp)) hχ =
      AnalyticESC.entropy p / lyapunov φ p hp := rfl
  rw [hval]
  exact (AnalyticESC.scale_tendsto_iff
    (fun r : ℝ => Real.log ((selfConformal φ p hp).real (Metric.closedBall x r)) / Real.log r)
    _).2 hx

end FractalGeometry.Rapaport.Analytic
