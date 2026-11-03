module

public import AnalyticESC.Literature.Rapaport.Analytic.Main.Core
public import AnalyticESC.Literature.Rapaport.Analytic.Main.Eventually
public import AnalyticESC.Literature.Rapaport.Analytic.Main.Numeric

@[expose] public section

/-!
# The main argument of Section 4 of Rapaport

The proof of Theorem 1.2 of A. Rapaport, *Dimension of self-conformal measures associated to an
exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2, Section 4: if `μ` has dimension
`d < 1`, the fibres `β_x` have cylinder entropy rate `0` (`FibreEntropyVanishes`).

Assume the rate `Δ'` is positive. With the parameters chosen in the order
`Δ⁻¹, c⁻¹, C ≪ M ≪ k ≪ ρ⁻¹ ≪ δ⁻¹ ≪ m`, and an exponentially separated length `m = n + n'`:

* the integral of `g(x) = H((Π_m β_x).μ, 𝒟_{Mn+L})` over `μ` is at most `Mn (d log 2 + 2δ)`, by
  concavity of conditional entropy (`integral_ent_sub_le`), Young's identity and Lemma 4.1
  (Rapaport's (4.3));
* on the good set `E`, of measure `≥ 1 - δ`, `g ≥ Mn (d log 2 - 6δ + G)` with
  `G = ρ log 2 · Δ / (6 log N)` (`ent_wordAct_fibre_ge`, Rapaport's (4.14)).

Since `δ ≪ G`, this is a contradiction.

## Main declarations

* `fibreEntropyVanishes`: `FibreEntropyVanishes φ p hp` from `EntropyIncreasePoly φ p hp`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Main.Main`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic.SectionFour

/-- The arithmetic of the conditional entropy bound in the main argument. -/
theorem arith_udiff {l L K D δ δ₁ e₁ e₂ : ℝ} (hδ₁ : 0 ≤ δ₁) (hL : L ≤ K * l)
    (hδ : δ₁ * (1 + 2 * K) = δ) (a1 : e₁ - (l + L) * D ≤ δ₁ * (l + L))
    (a2 : -(δ₁ * L) ≤ e₂ - L * D) : e₁ - e₂ ≤ l * (D + δ) := by
  have h1 : δ₁ * L ≤ δ₁ * (K * l) := mul_le_mul_of_nonneg_left hL hδ₁
  have h2 : l * δ = l * (δ₁ * (1 + 2 * K)) := by rw [hδ]
  linarith only [h1, h2, a1, a2]

/-- The final contradiction of the main argument. -/
theorem final_contra {D δ G X : ℝ} (hX : X = D - 6 * δ + G) (hX2 : X ≤ 2) (hδ : 0 ≤ δ)
    (hδG : δ ≤ G / 40) (hG : 0 < G) (h : (1 - δ) * X ≤ D + 2 * δ) : False := by
  have h1 : δ * X ≤ δ * 2 := mul_le_mul_of_nonneg_left hX2 hδ
  linarith only [h1, hX, hδG, hG, h]

end FractalGeometry.Rapaport.Analytic.SectionFour

namespace FractalGeometry.Rapaport.Analytic

open MeasureTheory ProbabilityTheory Set Filter Topology FractalGeometry.SelfConformal
open FractalGeometry.Rapaport.Analytic.SectionFour
open AnalyticESC (I realComp RapaportHyp)
open scoped ENNReal

variable {N : ℕ} {φ : Fin N → ℝ → ℝ}

/-- The argument of Section 4 of Rapaport (arXiv:2412.16753v2): under `AnalyticESC.RapaportHyp`
and the entropy increase theorem (Theorem 3.1), if the self-conformal measure `μ` has dimension
`d < 1`, then the fibres of the coding map have cylinder entropy rate `0`. -/
theorem fibreEntropyVanishes [NeZero N] (hφ : RapaportHyp φ) {p : Fin N → ℝ}
    (hp : AnalyticESC.IsProbVec p) (hEI : EntropyIncreasePoly φ p hp) :
    FibreEntropyVanishes φ p hp := by
  intro d Δ' hdim hd1 hfib
  by_contra hΔ'0
  push Not at hΔ'0
  -- the measure, the Lyapunov exponent and the dimension
  set μ := selfConformal φ p hp with hμ
  set χ := lyapunov φ p hp with hχ
  have hμI : μ Iᶜ = 0 := selfConformal_compl_I hφ hp
  have hμprob : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hχ0 : 0 < χ := lyapunov_pos hφ hp
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hYoung := tendsto_ent_div_of_isExactDim hμI hdim
  have hd0 : 0 ≤ d := by
    have : 0 ≤ d * Real.log 2 := ge_of_tendsto' hYoung fun n =>
      div_nonneg (ent_nonneg _) (Nat.cast_nonneg n)
    exact nonneg_of_mul_nonneg_left this hlog2
  -- `Δ' ≤ log N`
  set Λ := Real.log N with hΛ
  have hΔΛ : Δ' ≤ Λ := by
    obtain ⟨x, hx⟩ := hfib.exists
    refine le_of_tendsto hx ((eventually_gt_atTop 0).mono fun l h0 => ?_)
    rw [div_le_iff₀ (by exact_mod_cast h0), cylEntropy_eq_ent, mul_comm]
    exact ent_pre_le _ l
  have hΛ0 : 0 < Λ := hΔ'0.trans_le hΔΛ
  -- the parameters `Δ`, `C`, `c`, `κ`, `M`, `k`
  set Δ := min Δ' 1 / 2 with hΔ_def
  have hΔ0 : 0 < Δ := by positivity
  have hΔΔ' : Δ < Δ' := by
    have := min_le_left Δ' 1
    rw [hΔ_def]
    linarith
  have hΔ1 : Δ ≤ 1 / 2 := by
    have := min_le_right Δ' 1
    rw [hΔ_def]
    linarith
  obtain ⟨C₁, hC₁, hHD₁⟩ := exists_iteratedDeriv_realComp_le hφ
  set C := max (distConst φ) C₁ with hC_def
  have hCd : distConst φ ≤ C := le_max_left _ _
  have hC1 : 1 ≤ C := (one_lt_distConst hφ).le.trans hCd
  have hC0 : 0 < C := zero_lt_one.trans_le hC1
  have hHD : ∀ (u : List (Fin N)) (l : ℕ), 1 ≤ l → ∀ x ∈ I,
      |iteratedDeriv l (realComp φ u) x| ≤ l.factorial * C ^ l * |deriv (realComp φ u) 0| := by
    intro u l hl x hx
    refine (hHD₁ u l hl x hx).trans ?_
    have : C₁ ^ l ≤ C ^ l := pow_le_pow_left₀ (zero_lt_one.trans hC₁).le (le_max_right _ _) l
    gcongr
  obtain ⟨c₀, hc₀, hfreq⟩ := hφ.exp_separated
  set c := min c₀ (1 / 2) with hc_def
  have hc0 : 0 < c := lt_min hc₀ (by norm_num)
  have hc1 : c ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hcc₀ : c ≤ c₀ := min_le_left _ _
  set κ := Δ / (4 * Λ) with hκ_def
  have hκ0 : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 / 8 := by
    have : Δ ≤ Δ' / 2 := by
      have := min_le_left Δ' 1
      rw [hΔ_def]
      linarith
    rw [hκ_def, div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨M₀, hM₀⟩ := pow_unbounded_of_one_lt (2 / c ^ 2) (by norm_num : (1 : ℝ) < 2)
  set M := max M₀ 1 with hM_def
  have hM1 : 1 ≤ M := le_max_right _ _
  have hMc : 2 ≤ 2 ^ M * c ^ 2 := by
    have h1 : (2 : ℝ) ^ M₀ ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
    have h3 : 2 / c ^ 2 < 2 ^ M := hM₀.trans_le h1
    exact ((div_lt_iff₀ (pow_pos hc0 2)).1 h3).le
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt ((M * Real.log 2 + 1) * 2 / (κ * χ))
  set k := max k₀ 1 with hk_def
  have hk1 : 1 ≤ k := le_max_right _ _
  have hkM : M * Real.log 2 + 1 ≤ κ * k * χ / 2 := by
    have h1 : (k₀ : ℝ) ≤ k := by exact_mod_cast le_max_left k₀ 1
    rw [div_lt_iff₀ (by positivity)] at hk₀
    have h2 : (k₀ : ℝ) * (κ * χ) ≤ k * (κ * χ) := mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : κ * k * χ / 2 = k * (κ * χ) / 2 := by ring
    rw [h3]
    linarith
  -- the constant `ε` of the entropy increase theorem, and `ρ`
  set ε := min (1 / ((k + 1) * (2 * C ^ (k + 3)))) (min (4 * C)⁻¹
    (min (Δ / (6 * M * Real.log 2)) (1 / C ^ 2))) with hε_def
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have hε0 : 0 < ε := by
    refine lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hεder : ε ≤ (4 * C)⁻¹ := (min_le_right _ _).trans (min_le_left _ _)
  have hε1 : ε < 1 := by
    refine hεder.trans_lt ?_
    rw [inv_lt_one_iff₀]
    right
    linarith
  have hεnorm : ε * ((k + 1) * (2 * C ^ (k + 3))) ≤ 1 := by
    have h := min_le_left (1 / ((k + 1) * (2 * C ^ (k + 3)))) (min (4 * C)⁻¹
      (min (Δ / (6 * M * Real.log 2)) (1 / C ^ 2)))
    rw [← hε_def, le_div_iff₀ (by positivity)] at h
    exact h
  have hεψ : ε * C ^ 2 ≤ 1 := by
    have h : ε ≤ 1 / C ^ 2 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h
    exact h
  have hεΔ : ε ≤ Δ / (6 * M * Real.log 2) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεent : ∀ n : ℕ, ε * ((M * n : ℕ) : ℝ) * Real.log 2 ≤ Δ / 6 * n := by
    intro n
    rw [le_div_iff₀ (by positivity)] at hεΔ
    push_cast
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  obtain ⟨ρ, hρ0, N₀, hEIn⟩ := hEI d hdim hd1 k hk1 ε hε0 hε1
  set ρ' := min ρ 1 with hρ'_def
  have hρ'0 : 0 < ρ' := lt_min hρ0 zero_lt_one
  have hρ'ρ : ρ' ≤ ρ := min_le_left _ _
  have hρ'1 : ρ' ≤ 1 := min_le_right _ _
  set G := ρ' * Real.log 2 * (Δ / (6 * Λ)) with hG_def
  have hG0 : 0 < G := by positivity
  have hG1 : G ≤ 1 := by
    have h1 : Δ / (6 * Λ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : Δ ≤ Λ := by
        have := min_le_left Δ' 1
        rw [hΔ_def]
        linarith
      linarith
    have h2 : ρ' * Real.log 2 ≤ 1 := by nlinarith
    calc G = ρ' * Real.log 2 * (Δ / (6 * Λ)) := rfl
      _ ≤ 1 * 1 := mul_le_mul h2 h1 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  -- the parameter `δ`
  set δ := min (χ / 4) (min (1 / 4) (min (Δ * Real.log 2 / 40) (min (Δ / (24 * Λ)) (G / 40))))
    with hδ_def
  have hδ0 : 0 < δ := lt_min (by positivity) (lt_min (by norm_num) (lt_min (by positivity)
    (lt_min (by positivity) (by positivity))))
  have hδχ : δ ≤ χ / 4 := min_le_left _ _
  have hδ1 : δ ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδΔ1 : δ ≤ Δ * Real.log 2 / 40 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδΔ2 : δ ≤ Δ / (24 * Λ) := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hδG : δ ≤ G / 40 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  -- the lengths
  set nf' : ℕ → ℕ := fun m => ⌊κ * m⌋₊ with hnf'
  set nf : ℕ → ℕ := fun m => m - nf' m with hnf
  set Lf : ℕ → ℕ := fun m => ⌊χ * m / Real.log 2⌋₊ with hLf
  have hn'T : Tendsto nf' atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hκ0)
  have hnT : Tendsto nf atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b => ⟨2 * b, fun m hm => ?_⟩
    have h := (lengths_basic hκ0.le hκ1 m).2.2.2
    have h2 : (2 * b : ℝ) ≤ m := by exact_mod_cast hm
    have : (b : ℝ) ≤ nf m := by simp only [hnf, hnf']; linarith
    exact_mod_cast this
  have hLT : Tendsto Lf atTop atTop := by
    refine tendsto_nat_floor_atTop.comp ?_
    have := tendsto_natCast_atTop_atTop.const_mul_atTop (div_pos hχ0 hlog2)
    refine this.congr fun m => ?_
    ring
  have hℓT : Tendsto (fun m => M * nf m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left _ hM1) hnT
  have hℓLT : Tendsto (fun m => M * nf m + Lf m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_add_right _ _) hℓT
  -- the eventual properties
  set δ₁ := δ / (1 + 4 * χ / Real.log 2) with hδ₁
  have hδ₁0 : 0 < δ₁ := by positivity
  have ev1 := eventually_numeric (N := N) hχ0 hδ0 hδχ hδ1 hδΔ1 hδΔ2 hΔ0 hΛ0 hΛ hκ_def hκ1
    hC1 hCd distConst_pos hM1 hk1 hkM hc0 hc1 hMc
  have ev2 := eventually_abs_ent_sub_le hμI hdim hℓT hδ0
  have ev3 := eventually_abs_ent_sub_le hμI hdim hℓLT hδ₁0
  have ev3' := eventually_abs_ent_sub_le hμI hdim hLT hδ₁0
  have ev4 := eventually_integral_ent_le hφ hp (half_pos hδ0) (L := Lf)
    (fun m => two_pow_floor_le hχ0.le m)
  have ev5 := eventually_measure_goodSet_ge hφ hp hΔΔ' hfib hδ0 hnT hn'T
  have ev6 := hℓT.eventually_ge_atTop N₀
  obtain ⟨m, hsep, hnum, hY, hU1, hU2, h41, hE, hN₀⟩ :=
    (hfreq.and_eventually (ev1.and (ev2.and (ev3.and (ev3'.and (ev4.and (ev5.and ev6))))))).exists
  -- the chosen lengths
  obtain ⟨hlen1, hlen2, hsum, hlen4⟩ := lengths_basic hκ0.le hκ1 m
  have hsum' : nf m + nf' m = m := hsum
  have hlen4' : (m : ℝ) ≤ 2 * (nf m : ℝ) := hlen4
  dsimp only at hnum
  obtain ⟨hn0, hcount, herr₁, herr₂, hTay, hRb, hAe, hsepnum⟩ := hnum
  have hn0' : 0 < nf m := hn0
  have hℓ0 : 0 < M * nf m := Nat.mul_pos (by omega) hn0'
  have hℓ0' : (0 : ℝ) < ((M * nf m : ℕ) : ℝ) := by exact_mod_cast hℓ0
  have hnℓ : (nf m : ℝ) ≤ ((M * nf m : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_left _ hM1
  -- the entropy increase theorem at the level `M n`
  have hEIℓ : ∀ ν : Measure (Poly k), IsProbabilityMeasure ν →
      (∀ᵐ q ∂ν, ‖q‖ ≤ ε⁻¹ ∧ ∀ x ∈ I, ε ≤ |Poly.derivEval q x|) →
      ε ≤ dyadicEntropyVec ν (M * nf m) / ((M * nf m : ℕ) : ℝ) →
      ∀ ψ : ℝ → ℝ, Set.MapsTo ψ I I → (∀ x ∈ I, HasDerivWithinAt ψ (deriv ψ x) I x) →
        (∀ x ∈ I, ε ≤ |deriv ψ x| ∧ |deriv ψ x| ≤ ε⁻¹) →
        d + ρ' ≤ dyadicEntropy (act ν ((selfConformal φ p hp).map ψ)) (M * nf m) /
          ((M * nf m : ℕ) : ℝ) := fun ν h1 h2 h3 ψ h4 h5 h6 =>
    le_trans (by linarith) (hEIn _ hN₀ ν h1 h2 h3 ψ h4 h5 h6)
  have hYℓ : ((M * nf m : ℕ) : ℝ) * (d * Real.log 2 - δ) ≤
      ent (selfConformal φ p hp) (cellIdx (M * nf m)) := by
    have := (abs_le.1 hY).1
    linarith
  have hsepCore : ∀ w₁ w₂ : Fin (nf m + nf' m) → Fin N, w₁ ≠ w₂ →
      (k + 3) / 2 ^ (M * nf m) < ⨆ y : I, |wordMap φ w₁ y - wordMap φ w₂ y| := by
    rw [hsum']
    intro w₁ w₂ hw
    refine lt_of_lt_of_le hsepnum (le_trans ?_ (hsep w₁ w₂ hw))
    exact pow_le_pow_left₀ hc0.le hcc₀ m
  -- the lower bound on the good set
  set X := d * Real.log 2 - 6 * δ + G with hX
  have hX0 : 0 ≤ X := by
    have : 0 ≤ d * Real.log 2 := mul_nonneg hd0 hlog2.le
    linarith
  set E : Set ℝ := {x | Δ * nf m < ent (fibre φ p hp x) (pre (nf m)) ∧
    (fibre φ p hp x).real {η | ¬ (GoodWord φ χ δ (pre (nf m) η) ∧
      GoodWord φ χ δ (pre (nf' m) (shift^[nf m] η)))} ≤ 2 * δ} with hE_def
  have hlow : ∀ᵐ x ∂μ, x ∈ E → ((M * nf m : ℕ) : ℝ) * X ≤
      ent (wordAct φ μ (fibre φ p hp x) m) (cellIdx (M * nf m + Lf m)) := by
    filter_upwards [ae_mem_image_of_fibre hφ hp] with x hx hxE
    have h := ent_wordAct_fibre_ge hφ hp hC1 hCd hHD (n := nf m) (n' := nf' m)
      (S := ⌊2 * nf m * δ / Real.log 2⌋₊) (L := Lf m) hk1 hℓ0 (χ := χ) (Δ := Δ)
      (ρ := ρ') (A := 2 * C * Real.exp (δ * m)) hEIℓ hε0 hεnorm hεder hεψ (hεent (nf m)) le_rfl
      hΛ0 hΔ0 hcount hδ0.le hd0 hd1.le hρ'0.le hYℓ herr₁ herr₂ hTay hRb hAe hsepCore
      (fibre φ p hp x) x (hx _) hxE.1 hxE.2
    rw [hsum'] at h
    refine le_trans (le_of_eq ?_) h
    rw [hX, hG_def]
    ring
  -- measurability and integrability
  set θ : ℝ → Measure ℝ := fun x => wordAct φ μ (fibre φ p hp x) m with hθ_def
  have hθprob : ∀ x, IsProbabilityMeasure (θ x) := fun x =>
    isProbabilityMeasure_wordAct (φ := φ) (θ := μ) _ m
  have hθI : ∀ x, θ x Iᶜ = 0 := fun x => wordAct_compl_I hφ hμI _ m
  have hθm : ∀ s : Set ℝ, MeasurableSet s → Measurable fun x => θ x s := fun s _ =>
    measurable_wordAct_fibre hp μ m s
  have hint : ∀ j : ℕ, Integrable (fun x => ent (θ x) (cellIdx j)) μ := fun j =>
    Integrable.of_mem_Icc 0 (Real.log (2 ^ j + 2))
      (measurable_ent_of_kernel hθI hθm j).aemeasurable
      (Eventually.of_forall fun x => ⟨ent_nonneg _, ent_cellIdx_le_of_compl_I (hθI x) j⟩)
  -- the upper bound (4.3)
  have hJ := integral_ent_sub_le (μ := μ) (θ := θ) (ρ := μ) hθI hθm
    (fun s _ => selfConformal_eq_lintegral_wordAct_fibre hφ hp m s) (Lf m) (M * nf m)
  rw [integral_sub (hint _) (hint _), add_comm (Lf m)] at hJ
  have hm2ℓ : (m : ℝ) ≤ 2 * ((M * nf m : ℕ) : ℝ) := by linarith only [hlen4', hnℓ]
  have hL : (Lf m : ℝ) ≤ 2 * χ / Real.log 2 * ((M * nf m : ℕ) : ℝ) := by
    have h1 : (Lf m : ℝ) ≤ χ * m / Real.log 2 := Nat.floor_le (by positivity)
    have h2 : χ * m / Real.log 2 ≤ χ * (2 * ((M * nf m : ℕ) : ℝ)) / Real.log 2 := by
      gcongr
    have h3 : χ * (2 * ((M * nf m : ℕ) : ℝ)) / Real.log 2 =
        2 * χ / Real.log 2 * ((M * nf m : ℕ) : ℝ) := by ring
    linarith only [h1, h2, h3]
  have hδ₁' : δ₁ * (1 + 2 * (2 * χ / Real.log 2)) = δ := by
    rw [hδ₁, show (1 + 2 * (2 * χ / Real.log 2)) = 1 + 4 * χ / Real.log 2 by ring,
      div_mul_cancel₀ _ (by positivity : (1 + 4 * χ / Real.log 2) ≠ 0)]
  have hUdiff : ent μ (cellIdx (M * nf m + Lf m)) - ent μ (cellIdx (Lf m)) ≤
      ((M * nf m : ℕ) : ℝ) * (d * Real.log 2 + δ) := by
    have a1 := (abs_le.1 hU1).2
    have a2 := (abs_le.1 hU2).1
    rw [Nat.cast_add] at a1
    exact arith_udiff hδ₁0.le hL hδ₁' a1 a2
  have hI41 : ∫ x, ent (θ x) (cellIdx (Lf m)) ∂μ ≤ δ * ((M * nf m : ℕ) : ℝ) := by
    have h1 : δ / 2 * m ≤ δ / 2 * (2 * ((M * nf m : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hm2ℓ (by positivity)
    have h2 : δ / 2 * (2 * ((M * nf m : ℕ) : ℝ)) = δ * ((M * nf m : ℕ) : ℝ) := by ring
    exact h41.trans (h1.trans_eq h2)
  have hupper : ∫ x, ent (θ x) (cellIdx (M * nf m + Lf m)) ∂μ ≤
      ((M * nf m : ℕ) : ℝ) * (d * Real.log 2 + 2 * δ) := by
    linarith only [hJ, hUdiff, hI41]
  -- the lower bound by integration over the good set
  have hEm : MeasurableSet E := by
    have hmeasEnt : Measurable fun x => ent (fibre φ p hp x) (pre (nf m)) := by
      simp_rw [← cylEntropy_eq_ent]
      exact measurable_cylEntropy_fibre hp (nf m)
    have hbadm : MeasurableSet {η : ℕ → Fin N | ¬ (GoodWord φ χ δ (pre (nf m) η) ∧
        GoodWord φ χ δ (pre (nf' m) (shift^[nf m] η)))} :=
      ((measurable_pre (nf m)).prodMk ((measurable_pre (nf' m)).comp
        (measurable_shift.iterate (nf m)))) (MeasurableSet.of_discrete
          (s := {z : (Fin (nf m) → Fin N) × (Fin (nf' m) → Fin N) |
            ¬ (GoodWord φ χ δ z.1 ∧ GoodWord φ χ δ z.2)}))
    exact (measurableSet_lt measurable_const hmeasEnt).inter (measurableSet_le
      (ENNReal.measurable_toReal.comp ((graphMeasure φ p hp).condKernel.measurable_coe hbadm))
      measurable_const)
  have hind : ∫ x, E.indicator (fun _ => ((M * nf m : ℕ) : ℝ) * X) x ∂μ ≤
      ∫ x, ent (θ x) (cellIdx (M * nf m + Lf m)) ∂μ := by
    refine integral_mono_ae ((integrable_const _).indicator hEm) (hint _) ?_
    filter_upwards [hlow] with x hx
    by_cases hxE : x ∈ E
    · rw [Set.indicator_of_mem hxE]
      exact hx hxE
    · rw [Set.indicator_of_notMem hxE]
      exact ent_nonneg _
  rw [integral_indicator_const _ hEm, smul_eq_mul] at hind
  -- the contradiction
  have hlowE : (1 - δ) * (((M * nf m : ℕ) : ℝ) * X) ≤ μ.real E * (((M * nf m : ℕ) : ℝ) * X) :=
    mul_le_mul_of_nonneg_right hE (by positivity)
  have hfin : (1 - δ) * X ≤ d * Real.log 2 + 2 * δ := by
    have h := hlowE.trans (hind.trans hupper)
    have h' : ((M * nf m : ℕ) : ℝ) * ((1 - δ) * X) ≤
        ((M * nf m : ℕ) : ℝ) * (d * Real.log 2 + 2 * δ) := by linarith only [h]
    exact le_of_mul_le_mul_left h' hℓ0'
  have hX2 : X ≤ 2 := by
    have h1 : d * Real.log 2 ≤ 1 * 1 :=
      mul_le_mul hd1.le hlog2'.le hlog2.le zero_le_one
    linarith only [h1, hG1, hδ0, hX]
  exact final_contra hX hX2 hδ0.le hδG hG0 hfin

end FractalGeometry.Rapaport.Analytic
