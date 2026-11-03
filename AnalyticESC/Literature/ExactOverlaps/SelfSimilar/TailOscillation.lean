module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

set_option maxSynthPendingDepth 3

/-!
Measurable tail oscillations for an almost-surely convergent sequence
dominated by an integrable function. Their integrals tend to zero, the
quantitative input for triangular orbit averaging.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.TailOscillation`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ExactOverlaps.Ergodic

noncomputable def tailOscillation {Ω : Type*} (F : ℕ → Ω → ℝ) (f : Ω → ℝ)
    (m : ℕ) (x : Ω) : ℝ := ⨆ k : ℕ, |F (m + k) x - f x|

theorem tailOscillation_bounds {Ω : Type*} {F : ℕ → Ω → ℝ} {f G : Ω → ℝ}
    {x : Ω} (hF : ∀ n, |F n x| ≤ G x) (hf : |f x| ≤ G x) (m : ℕ) :
    0 ≤ tailOscillation F f m x ∧ tailOscillation F f m x ≤ 2 * G x := by
  have hb : BddAbove (Set.range (fun k : ℕ ↦ |F (m + k) x - f x|)) := by
    refine ⟨2 * G x, ?_⟩
    rintro _ ⟨k, rfl⟩
    have hh := abs_sub_le (F (m + k) x) 0 (f x)
    simp only [sub_zero, zero_sub, abs_neg] at hh
    exact hh.trans (by linarith [hF (m + k)])
  constructor
  · exact (abs_nonneg (F (m + 0) x - f x)).trans (le_ciSup hb 0)
  · apply ciSup_le
    intro k
    have hh := abs_sub_le (F (m + k) x) 0 (f x)
    simp only [sub_zero, zero_sub, abs_neg] at hh
    exact hh.trans (by linarith [hF (m + k)])

theorem le_tailOscillation {Ω : Type*} {F : ℕ → Ω → ℝ} {f G : Ω → ℝ}
    {x : Ω} (hF : ∀ n, |F n x| ≤ G x) (hf : |f x| ≤ G x)
    {m n : ℕ} (hmn : m ≤ n) : |F n x - f x| ≤ tailOscillation F f m x := by
  have hb : BddAbove (Set.range (fun k : ℕ ↦ |F (m + k) x - f x|)) := by
    refine ⟨2 * G x, ?_⟩
    rintro _ ⟨k, rfl⟩
    have hh := abs_sub_le (F (m + k) x) 0 (f x)
    simp only [sub_zero, zero_sub, abs_neg] at hh
    exact hh.trans (by linarith [hF (m + k)])
  change |F n x - f x| ≤ ⨆ k : ℕ, |F (m + k) x - f x|
  simpa only [Nat.add_sub_cancel' hmn] using le_ciSup hb (n - m)

theorem tailOscillation_tendsto_zero {Ω : Type*} {F : ℕ → Ω → ℝ} {f G : Ω → ℝ}
    {x : Ω} (hF : ∀ n, |F n x| ≤ G x) (hf : |f x| ≤ G x)
    (hlim : Tendsto (fun n ↦ F n x) atTop (𝓝 (f x))) :
    Tendsto (fun m ↦ tailOscillation F f m x) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (by positivity)
  refine ⟨M, fun m hm ↦ ?_⟩
  have hb := tailOscillation_bounds hF hf m
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hb.1]
  apply lt_of_le_of_lt (show tailOscillation F f m x ≤ ε / 2 from ?_) (by linarith)
  apply ciSup_le
  intro k
  have hh := hM (m + k) (by omega)
  rw [Real.dist_eq] at hh
  exact hh.le

theorem measurable_tailOscillation {Ω : Type*} [MeasurableSpace Ω]
    {F : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (hF : ∀ n, Measurable (F n)) (hf : Measurable f) (m : ℕ) :
    Measurable (tailOscillation F f m) := by
  apply Measurable.iSup
  intro k
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using ((hF (m + k)).sub hf).norm

theorem integral_tailOscillation_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F : ℕ → Ω → ℝ} {f G : Ω → ℝ}
    (hF : ∀ n, Measurable (F n)) (hf : Measurable f) (hG : Integrable G μ)
    (hbound : ∀ᵐ x ∂μ, (∀ n, |F n x| ≤ G x) ∧ |f x| ≤ G x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ F n x) atTop (𝓝 (f x))) :
    Tendsto (fun m ↦ ∫ x, tailOscillation F f m x ∂μ) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (fun x ↦ 2 * G x)
    (fun m ↦ (measurable_tailOscillation hF hf m).aestronglyMeasurable)
    (hG.const_mul 2) (fun m ↦ ?_) (show ∀ᵐ x ∂μ,
      Tendsto (fun m ↦ tailOscillation F f m x) atTop (𝓝 (0 : ℝ)) from ?_)
  · simpa only [integral_zero] using h
  · filter_upwards [hbound] with x hx
    have hb := tailOscillation_bounds hx.1 hx.2 m
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2
  · filter_upwards [hbound, hlim] with x hx hxl
    exact tailOscillation_tendsto_zero hx.1 hx.2 hxl

end ExactOverlaps.Ergodic
