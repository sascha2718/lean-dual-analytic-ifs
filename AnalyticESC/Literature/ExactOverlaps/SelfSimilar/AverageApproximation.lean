module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.MaximalBound
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

set_option maxSynthPendingDepth 3

/-!
Pointwise convergence of orbit averages is stable under sufficiently fast
L1 approximation. The estimate is proved from the maximal inequality and
Borel--Cantelli, rather than assumed as a pointwise ergodic theorem.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.AverageApproximation`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace ExactOverlaps.Ergodic

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {T : Ω → Ω} {f : Ω → ℝ}

omit [MeasurableSpace Ω] in
theorem abs_birkhoffAverage_sub_le (T : Ω → Ω) (f g : Ω → ℝ) (n : ℕ) (x : Ω) :
    |birkhoffAverage ℝ T f n x - birkhoffAverage ℝ T g n x| ≤
      birkhoffAverage ℝ T (fun y ↦ |f y - g y|) n x := by
  have hn : 0 ≤ (n : ℝ)⁻¹ := by positivity
  simp only [birkhoffAverage, smul_eq_mul, ← mul_sub, abs_mul, abs_of_nonneg hn]
  apply mul_le_mul_of_nonneg_left _ hn
  simpa only [birkhoffSum, ← Finset.sum_sub_distrib] using
    Finset.abs_sum_le_sum_abs (fun k ↦ f (T^[k] x) - g (T^[k] x)) (Finset.range n)

theorem ae_eventually_average_error_le (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) (g : ℕ → Ω → ℝ)
    (hgm : ∀ m, Measurable (g m)) (hg : ∀ m, Integrable (g m) μ)
    (η : ℕ → ℝ) (hη : ∀ m, 0 < η m)
    (hηsum : (∑' m, ENNReal.ofReal (η m)) ≠ ⊤)
    (happrox : ∀ m, (∫ x, |f x - g m x| ∂μ) ≤ (η m) ^ 2) :
    ∀ᵐ x ∂μ, ∀ᶠ m in atTop, ∀ n,
      |birkhoffAverage ℝ T f n x - birkhoffAverage ℝ T (g m) n x| ≤ η m := by
  let E : ℕ → Set Ω := fun m ↦
    {x | ∃ n, η m < birkhoffAverage ℝ T (fun y ↦ |f y - g m y|) n x}
  have hE : ∀ m, μ (E m) ≤ ENNReal.ofReal (η m) := by
    intro m
    have hem : Measurable (fun x ↦ |f x - g m x|) := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using (hfm.sub (hgm m)).norm
    have hei : Integrable (fun x ↦ |f x - g m x|) μ := by
      simpa only [Pi.sub_apply] using (hf.sub (hg m)).abs
    apply (measure_exists_birkhoffAverage_gt_le hT hem hei
      (ae_of_all _ (fun x ↦ abs_nonneg _)) (hη m)).trans
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ (hη m)).2
    simpa only [pow_two] using happrox m
  have hs : (∑' m, μ (E m)) ≠ ⊤ :=
    ne_top_of_le_ne_top hηsum (ENNReal.tsum_le_tsum hE)
  filter_upwards [ae_eventually_notMem hs] with x hx
  filter_upwards [hx] with m hm
  intro n
  exact (abs_birkhoffAverage_sub_le T f (g m) n x).trans
    (le_of_not_gt (fun h ↦ hm ⟨n, h⟩))

/-- A proved dense-class transfer principle for almost-sure orbit averages. -/
theorem ae_tendsto_birkhoffAverage_of_fast_approximation
    (hT : MeasurePreserving T μ μ) (hfm : Measurable f) (hf : Integrable f μ)
    (g : ℕ → Ω → ℝ) (hgm : ∀ m, Measurable (g m)) (hg : ∀ m, Integrable (g m) μ)
    (η : ℕ → ℝ) (hη : ∀ m, 0 < η m)
    (hηsum : (∑' m, ENNReal.ofReal (η m)) ≠ ⊤)
    (hηlim : Tendsto η atTop (𝓝 0))
    (happrox : ∀ m, (∫ x, |f x - g m x| ∂μ) ≤ (η m) ^ 2)
    (hconv : ∀ m, ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ T (g m) n x)
      atTop (𝓝 (∫ y, g m y ∂μ))) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ T f n x)
      atTop (𝓝 (∫ y, f y ∂μ)) := by
  have hint : ∀ m, |(∫ y, f y ∂μ) - ∫ y, g m y ∂μ| ≤ (η m) ^ 2 := by
    intro m
    rw [← integral_sub hf (hg m)]
    exact abs_integral_le_integral_abs.trans (happrox m)
  filter_upwards [ae_eventually_average_error_le hT hfm hf g hgm hg η hη hηsum happrox,
    ae_all_iff.2 hconv] with x hx hxconv
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hsmall : ∀ᶠ m in atTop, η m < min 1 (ε / 4) :=
    hηlim.eventually (gt_mem_nhds (lt_min (by norm_num) (by positivity)))
  obtain ⟨m, hm, hmsmall⟩ := (hx.and hsmall).exists
  have hm1 : η m < 1 := lt_of_lt_of_le hmsmall (min_le_left _ _)
  have hmε : η m < ε / 4 := lt_of_lt_of_le hmsmall (min_le_right _ _)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hxconv m) (ε / 2) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  have htri := abs_add_three
    (birkhoffAverage ℝ T f n x - birkhoffAverage ℝ T (g m) n x)
    (birkhoffAverage ℝ T (g m) n x - ∫ y, g m y ∂μ)
    ((∫ y, g m y ∂μ) - ∫ y, f y ∂μ)
  have hn' := hN n hn
  rw [Real.dist_eq] at hn' ⊢
  have hi := hint m
  rw [abs_sub_comm] at hi
  have hηsq : (η m) ^ 2 ≤ η m := by nlinarith [hη m]
  have heq : (birkhoffAverage ℝ T f n x - birkhoffAverage ℝ T (g m) n x) +
      (birkhoffAverage ℝ T (g m) n x - ∫ y, g m y ∂μ) +
      ((∫ y, g m y ∂μ) - ∫ y, f y ∂μ) =
      birkhoffAverage ℝ T f n x - ∫ y, f y ∂μ := by ring
  rw [heq] at htri
  linarith [hm n]

end ExactOverlaps.Ergodic
