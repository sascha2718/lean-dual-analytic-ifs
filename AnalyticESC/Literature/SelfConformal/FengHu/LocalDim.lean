module

public import AnalyticESC.Literature.Dimension.Exact
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.BranchBalls

@[expose] public section

/-!
# Bounds for local dimensions of measures on the line

General facts about the local dimension `lim_{r → 0} log μ(B(x, r)) / log r` of a finite Borel
measure on `ℝ`, used for the range `0 ≤ dim μ ≤ 1` in D.-J. Feng and H. Hu, *Dimension theory of
iterated function systems*, Comm. Pure Appl. Math. 62 (2009), Theorem 2.8, on the line.

## Main declarations

* `hasLocalDim_nonneg`: a local dimension of a probability measure is nonnegative.
* `ae_hasLocalDim_le_one`: for a finite measure `μ` on `ℝ`, at `μ`-a.e. point every local
  dimension is at most `1`. The proof differentiates Lebesgue measure with respect to `μ`
  (Besicovitch): `2r / μ(B(x, r))` has a finite limit at `μ`-a.e. `x`.
* `isExactDim_nonneg`, `isExactDim_le_one`: the exact dimension of a probability measure on `ℝ`
  lies in `[0, 1]`.

Copied from the library `FractalGeometry` (module `FractalGeometry.SelfConformal.FengHu.LocalDim`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.SelfConformal.FengHu

open MeasureTheory Filter Topology Metric Set

/-- A local dimension of a probability measure is nonnegative. -/
theorem hasLocalDim_nonneg {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {x : X} {d : ℝ}
    (h : FractalGeometry.HasLocalDim μ x d) : 0 ≤ d := by
  apply ge_of_tendsto h
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with r hr
  exact div_nonneg_of_nonpos (Real.log_nonpos measureReal_nonneg measureReal_le_one)
    (Real.log_neg hr.1 hr.2).le

/-- For a finite measure on `ℝ`, at almost every point every local dimension is at most `1`. -/
theorem ae_hasLocalDim_le_one (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ᵐ x ∂μ, ∀ d : ℝ, FractalGeometry.HasLocalDim μ x d → d ≤ 1 := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv volume μ, Measure.rnDeriv_lt_top volume μ,
    ExactOverlaps.ae_closedBall_measure_pos μ] with x hx hfin hpos d hd
  set L : ℝ := (volume.rnDeriv μ x).toReal with hL
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  have hlt : volume.rnDeriv μ x < ENNReal.ofReal (L + 1) := by
    rw [← ENNReal.ofReal_toReal hfin.ne]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have hev := hx.eventually (gt_mem_nhds hlt)
  set c : ℝ := Real.log (2 / (L + 1)) with hc
  have hlim : Tendsto (fun r => 1 + c / Real.log r) (𝓝[>] 0) (𝓝 1) := by
    have h0 : Tendsto (fun r => c / Real.log r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_const_nhds.div_atBot Real.tendsto_log_nhdsGT_zero
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add h0
  apply le_of_tendsto_of_tendsto hd hlim
  filter_upwards [hev, Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with r hr hr1
  have hr0 : 0 < r := hr1.1
  have hB0 : 0 < μ (closedBall x r) := hpos r hr0
  have hBt : μ (closedBall x r) ≠ ⊤ := measure_ne_top _ _
  have h2r : ENNReal.ofReal (2 * r) < ENNReal.ofReal (L + 1) * μ (closedBall x r) := by
    rw [← Real.volume_closedBall]
    exact (ENNReal.div_lt_iff (Or.inl hB0.ne') (Or.inl hBt)).1 hr
  have hreal : 2 * r < (L + 1) * μ.real (closedBall x r) := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBt)).2 h2r
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
      ENNReal.toReal_ofReal (by linarith), ← measureReal_def] at h
  have hmpos : 0 < μ.real (closedBall x r) := ENNReal.toReal_pos hB0.ne' hBt
  have hlog : Real.log r + c ≤ Real.log (μ.real (closedBall x r)) := by
    rw [hc, ← Real.log_mul hr0.ne' (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    linarith
  have hlr : Real.log r < 0 := Real.log_neg hr0 hr1.2
  calc Real.log (μ.real (closedBall x r)) / Real.log r ≤ (Real.log r + c) / Real.log r :=
        div_le_div_of_nonpos_of_le hlr.le hlog
    _ = 1 + c / Real.log r := by rw [add_div, div_self hlr.ne]

/-- The exact dimension of a probability measure is nonnegative. -/
theorem isExactDim_nonneg {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {d : ℝ} (h : FractalGeometry.IsExactDim μ d) :
    0 ≤ d := by
  obtain ⟨x, hx⟩ := h.exists
  exact hasLocalDim_nonneg hx

/-- The exact dimension of a probability measure on `ℝ` is at most `1`. -/
theorem isExactDim_le_one {μ : Measure ℝ} [IsProbabilityMeasure μ] {d : ℝ}
    (h : FractalGeometry.IsExactDim μ d) : d ≤ 1 := by
  obtain ⟨x, hx, hx'⟩ := (h.and (ae_hasLocalDim_le_one μ)).exists
  exact hx' d hx

end FractalGeometry.SelfConformal.FengHu
