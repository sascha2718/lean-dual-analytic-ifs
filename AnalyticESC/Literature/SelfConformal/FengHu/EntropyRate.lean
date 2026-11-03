module

public import AnalyticESC.Literature.SelfConformal.Vocabulary

@[expose] public section

/-!
# Cylinder entropy rates from pointwise information rates

For a probability measure `ν` on `(Fin N)^ℕ`, the cylinder entropy `H(ν, 𝒞_l)` is the integral of
the information function `I_l(ω) = -log ν[ω|_l]`. If `I_l / l → Δ` at `ν`-a.e. point, then
`H(ν, 𝒞_l) / l → Δ`. This is the step from the pointwise conditional Shannon–McMillan–Breiman
theorem along fibres to the entropy of the conditional measures in D.-J. Feng and H. Hu,
*Dimension theory of iterated function systems*, Comm. Pure Appl. Math. 62 (2009),
Proposition 4.10.

The proof truncates `I_l / l` at a level `M > 2 log N + |Δ|`: the truncated averages converge by
dominated convergence, and the cylinders on which `I_l / l > M` have total entropy contribution at
most `2 (N e^{-M/2})^l`.

## Main declarations

* `pre l ω = ω|_l`, `cylInfo ν l ω = -log ν[ω|_l]`.
* `integral_comp_pre`, `cylEntropy_eq_sum`: cylinder entropies as finite sums and integrals.
* `tendsto_cylEntropy_div_of_ae`: the entropy rate from the pointwise information rate.

Copied from the library `FractalGeometry` (module `FractalGeometry.SelfConformal.FengHu.EntropyRate`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.SelfConformal.FengHu

open MeasureTheory Filter Topology Set

variable {N : ℕ}

/-- The prefix `ω|_l` of `ω`, as a function on `Fin l`. -/
def pre (l : ℕ) (ω : ℕ → Fin N) : Fin l → Fin N := fun k => ω k

/-- The prefix map is measurable. -/
theorem measurable_pre (l : ℕ) : Measurable (pre (N := N) l) :=
  Measurable.of_eval fun k => measurable_pi_apply (k : ℕ)

/-- The fibres of the prefix map are the cylinders. -/
theorem pre_preimage_singleton {l : ℕ} (u : Fin l → Fin N) : pre l ⁻¹' {u} = cylinder u := by
  ext ω
  simp only [mem_preimage, mem_singleton_iff, cylinder, mem_ofPred_eq, funext_iff, pre]

/-- `ω ∈ [ω|_l]`. -/
theorem mem_cylinder_pre (l : ℕ) (ω : ℕ → Fin N) : ω ∈ cylinder (pre l ω) := fun _ => rfl

/-- The information function `I_l(ω) = -log ν[ω|_l]` of the level-`l` cylinder partition. -/
noncomputable def cylInfo (ν : Measure (ℕ → Fin N)) (l : ℕ) (ω : ℕ → Fin N) : ℝ :=
  -Real.log (ν.real (cylinder (pre l ω)))

/-- The information function is measurable. -/
theorem measurable_cylInfo (ν : Measure (ℕ → Fin N)) (l : ℕ) : Measurable (cylInfo ν l) :=
  (measurable_of_countable fun u : Fin l → Fin N => -Real.log (ν.real (cylinder u))).comp
    (measurable_pre l)

/-- The information function of a probability measure is nonnegative. -/
theorem cylInfo_nonneg (ν : Measure (ℕ → Fin N)) [IsProbabilityMeasure ν] (l : ℕ)
    (ω : ℕ → Fin N) : 0 ≤ cylInfo ν l ω :=
  neg_nonneg.2 (Real.log_nonpos measureReal_nonneg measureReal_le_one)

/-- Integrals of functions of `ω|_l` are finite sums over the level-`l` cylinders. -/
theorem integral_comp_pre (ν : Measure (ℕ → Fin N)) [IsFiniteMeasure ν] (l : ℕ)
    (g : (Fin l → Fin N) → ℝ) :
    ∫ ω, g (pre l ω) ∂ν = ∑ u, ν.real (cylinder u) * g u := by
  rw [← integral_map (measurable_pre l).aemeasurable
    (measurable_of_countable g).aestronglyMeasurable, integral_fintype (Integrable.of_finite)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_measureReal_apply (measurable_pre l) (measurableSet_singleton u),
    pre_preimage_singleton, smul_eq_mul]

/-- The cylinder entropy as the sum of `ν[u] I(u)`. -/
theorem cylEntropy_eq_sum (ν : Measure (ℕ → Fin N)) (l : ℕ) :
    cylEntropy ν l = ∑ u : Fin l → Fin N, ν.real (cylinder u) * -Real.log (ν.real (cylinder u)) :=
  Finset.sum_congr rfl fun u _ => by rw [Real.negMulLog]; ring

/-- The cylinder entropy is the integral of the information function. -/
theorem cylEntropy_eq_integral (ν : Measure (ℕ → Fin N)) [IsFiniteMeasure ν] (l : ℕ) :
    cylEntropy ν l = ∫ ω, cylInfo ν l ω ∂ν := by
  rw [cylEntropy_eq_sum]
  exact (integral_comp_pre ν l fun u => -Real.log (ν.real (cylinder u))).symm

/-- `t (-log t) ≤ 2 e^{-s/2}` when `-log t ≥ s ≥ 0` and `0 < t`. -/
private theorem mul_neg_log_le {t s : ℝ} (ht : 0 < t) (hs : s ≤ -Real.log t) :
    t * -Real.log t ≤ 2 * Real.exp (-s / 2) := by
  set a := -Real.log t with ha
  have hta : t = Real.exp (-a) := by rw [ha, neg_neg, Real.exp_log ht]
  have h1 : a ≤ 2 * Real.exp (a / 2) := by
    have := Real.add_one_le_exp (a / 2)
    nlinarith [Real.exp_pos (a / 2)]
  calc t * a = a * Real.exp (-a) := by rw [hta]; ring
    _ ≤ 2 * Real.exp (a / 2) * Real.exp (-a) := by gcongr
    _ = 2 * Real.exp (-a / 2) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ 2 * Real.exp (-s / 2) := by gcongr

/-- If the information rates `I_l / l` converge to `Δ` almost everywhere, then the cylinder
entropy rates `H(ν, 𝒞_l) / l` converge to `Δ`. -/
theorem tendsto_cylEntropy_div_of_ae (ν : Measure (ℕ → Fin N)) [IsProbabilityMeasure ν]
    {Δ : ℝ} (h : ∀ᵐ ω ∂ν, Tendsto (fun l : ℕ => cylInfo ν l ω / l) atTop (𝓝 Δ)) :
    Tendsto (fun l : ℕ => cylEntropy ν l / l) atTop (𝓝 Δ) := by
  set M : ℝ := |Δ| + 2 * Real.log N + 2 with hM
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hΔM : Δ ≤ M := by rw [hM]; linarith [le_abs_self Δ]
  have hM0 : 0 < M := by rw [hM]; linarith [abs_nonneg Δ]
  set g : (l : ℕ) → (Fin l → Fin N) → ℝ := fun l u => -Real.log (ν.real (cylinder u)) / l
    with hg
  have hg0 : ∀ l u, 0 ≤ g l u := fun l u =>
    div_nonneg (neg_nonneg.2 (Real.log_nonpos measureReal_nonneg measureReal_le_one))
      (Nat.cast_nonneg l)
  have hsplit : ∀ l : ℕ, cylEntropy ν l / l =
      ∫ ω, min (g l (pre l ω)) M ∂ν +
        ∑ u, ν.real (cylinder u) * (g l u - min (g l u) M) := by
    intro l
    rw [integral_comp_pre ν l fun u => min (g l u) M, cylEntropy_eq_sum, Finset.sum_div,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [hg]
    ring
  have h1 : Tendsto (fun l : ℕ => ∫ ω, min (g l (pre l ω)) M ∂ν) atTop (𝓝 Δ) := by
    have hmin : min Δ M = Δ := min_eq_left hΔM
    have hconst : ∫ _ω, min Δ M ∂ν = Δ := by simp [hmin]
    rw [← hconst]
    refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun l => ?_)
      (integrable_const M) (fun l => Eventually.of_forall fun ω => ?_) ?_
    · exact ((measurable_of_countable fun u => min (g l u) M).comp
        (measurable_pre l)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hg0 l _) hM0.le)]
      exact min_le_right _ _
    · filter_upwards [h] with ω hω
      exact hω.min tendsto_const_nhds
  have h2 : Tendsto (fun l : ℕ => ∑ u, ν.real (cylinder u) * (g l u - min (g l u) M)) atTop
      (𝓝 0) := by
    set q : ℝ := N * Real.exp (-M / 2) with hq
    have hq0 : 0 ≤ q := by positivity
    have hq1 : q < 1 := by
      rcases Nat.eq_zero_or_pos N with hN | hN
      · simp [hq, hN]
      · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
        rw [hq, ← Real.exp_log hNpos, ← Real.exp_add, Real.exp_lt_one_iff]
        rw [hM]
        linarith [abs_nonneg Δ]
    have hlim : Tendsto (fun l : ℕ => 2 * q ^ l) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul 2
    refine squeeze_zero (fun l => Finset.sum_nonneg fun u _ =>
      mul_nonneg measureReal_nonneg (sub_nonneg.2 (min_le_left _ _))) (fun l => ?_) hlim
    have hterm : ∀ u : Fin l → Fin N, ν.real (cylinder u) * (g l u - min (g l u) M) ≤
        2 * Real.exp (-M / 2) ^ l := by
      intro u
      by_cases hgu : g l u ≤ M
      · rw [min_eq_left hgu, sub_self, mul_zero]
        positivity
      push Not at hgu
      rw [min_eq_right hgu.le]
      have hl : 1 ≤ l := by
        rcases Nat.eq_zero_or_pos l with hl | hl
        · simp [hg, hl] at hgu
          linarith
        · exact hl
      have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
      have hlM : (l : ℝ) * M ≤ -Real.log (ν.real (cylinder u)) := by
        have := hgu.le
        simp only [hg] at this
        rw [le_div_iff₀ (by linarith)] at this
        linarith
      have hpos : 0 < ν.real (cylinder u) := by
        rcases measureReal_nonneg.lt_or_eq with hp | hp
        · exact hp
        · exfalso
          rw [← hp, Real.log_zero, neg_zero] at hlM
          have : (0 : ℝ) < l * M := by positivity
          linarith
      calc ν.real (cylinder u) * (g l u - M) ≤ ν.real (cylinder u) * g l u := by
            gcongr
            linarith
        _ ≤ ν.real (cylinder u) * -Real.log (ν.real (cylinder u)) := by
            gcongr
            simp only [hg]
            rw [div_le_iff₀ (by linarith)]
            have := neg_nonneg.2 (Real.log_nonpos measureReal_nonneg
              (measureReal_le_one (μ := ν) (s := cylinder u)))
            nlinarith
        _ ≤ 2 * Real.exp (-(l * M) / 2) := mul_neg_log_le hpos hlM
        _ = 2 * Real.exp (-M / 2) ^ l := by
            rw [← Real.exp_nat_mul]
            ring_nf
    calc ∑ u, ν.real (cylinder u) * (g l u - min (g l u) M) ≤
          ∑ _u : Fin l → Fin N, 2 * Real.exp (-M / 2) ^ l := Finset.sum_le_sum fun u _ => hterm u
      _ = 2 * q ^ l := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul, hq, mul_pow]
          push_cast
          ring
  have := h1.add h2
  rw [add_zero] at this
  exact this.congr fun l => (hsplit l).symm

end FractalGeometry.SelfConformal.FengHu
