module

public import AnalyticESC.Literature.Rapaport.Analytic.Main.QPiece

@[expose] public section

/-!
# The lower bound for the entropy of a typical fibre

For a measure `ξ` on `(Fin N)^ℕ` (in the application, a fibre `β_x` of a good point `x`) the proof
of Theorem 1.2 of A. Rapaport, *Dimension of self-conformal measures associated to an
exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2, Section 4, bounds the entropy of
`(Π_{n+n'} ξ).μ` from below: by concavity over the pieces `F_{j,u}` (Rapaport's (4.3)), the
simple bound (4.5) on every piece, and the entropy increase (4.13) on the high-entropy pieces,
whose mass is `> Δ / (6 log N)` by (4.4).

## Main declarations

* `piece_facts`: the pieces are carried by `σ^{-n}[u]`, by good words of one shell, and by
  cylinders of positive `ξ`-mass.
* `ent_wordAct_fibre_ge`: the lower bound for a typical fibre (Rapaport's (4.14)).

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Main.Core`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic.SectionFour

open MeasureTheory ProbabilityTheory Set Filter Topology FractalGeometry.SelfConformal
open FractalGeometry.Rapaport.Analytic
open AnalyticESC (I realComp RapaportHyp)
open scoped ENNReal

variable {N : ℕ} {φ : Fin N → ℝ → ℝ}

/-- The pieces of `ξ`: the conditioned measure `ξ_{F_b}` on a good piece `b = (j, u)` is carried
by `σ^{-n}[u]`, and a word `v` of positive `ξ_{F_b}`-mass is good, lies in the shell `j`, and
`ξ[vu] > 0`. -/
theorem piece_facts (ξ : Measure (ℕ → Fin N)) {χ δ : ℝ} {n n' S : ℕ}
    (hS : ⌊2 * n * δ / Real.log 2⌋₊ ≤ S) (b : Fin (S + 2) × (Fin n' → Fin N))
    (hb : b.1 ≠ Fin.last (S + 1)) :
    ξ[|pieceLabel φ χ δ n n' S ⁻¹' {b}] (shift^[n] ⁻¹' cylinder b.2)ᶜ = 0 ∧
      ∀ v : Fin n → Fin N, ξ[|pieceLabel φ χ δ n n' S ⁻¹' {b}] (cylinder v) ≠ 0 →
        GoodWord φ χ δ v ∧ GoodWord φ χ δ b.2 ∧ shellIdx φ χ δ v = b.1 ∧
          ξ (cylinder (Fin.append v b.2)) ≠ 0 := by
  set g := pieceLabel φ χ δ n n' S with hg_def
  have hgm : MeasurableSet (g ⁻¹' {b}) :=
    measurable_pieceLabel χ δ n n' S (measurableSet_singleton b)
  have hsub : g ⁻¹' {b} ⊆ shift^[n] ⁻¹' cylinder b.2 := by
    intro η hη
    rw [mem_preimage, mem_singleton_iff] at hη
    have h2 : pre n' (shift^[n] η) = b.2 := by rw [← hη]; rfl
    rw [mem_preimage, ← h2]
    exact mem_cylinder_pre n' _
  constructor
  · rw [cond_apply hgm]
    have : g ⁻¹' {b} ∩ (shift^[n] ⁻¹' cylinder b.2)ᶜ = ∅ := by
      ext η
      simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and,
        not_not]
      exact fun h => hsub h
    rw [this, measure_empty, mul_zero]
  · intro v hv
    rw [cond_apply hgm] at hv
    have hne : ξ (g ⁻¹' {b} ∩ cylinder v) ≠ 0 := fun h => hv (by rw [h, mul_zero])
    obtain ⟨η, hηb, hηv⟩ := nonempty_of_measure_ne_zero hne
    rw [mem_preimage, mem_singleton_iff] at hηb
    have hpre : pre n η = v := funext fun k => hηv k
    have hlast : (g η).1 ≠ Fin.last (S + 1) := by rw [hηb]; exact hb
    have hgood := good_of_pieceLabel hlast
    have hsh := shellIdx_of_pieceLabel hS hlast
    have h2 : pre n' (shift^[n] η) = b.2 := by rw [← hηb]; rfl
    rw [hpre, h2] at hgood
    rw [hpre, show pieceLabel φ χ δ n n' S η = b from hηb] at hsh
    refine ⟨hgood.1, hgood.2, hsh.symm, ?_⟩
    refine fun h0 => hne (measure_mono_null (fun η' hη' => ?_) h0)
    rw [cylinder_append]
    exact ⟨hη'.2, hsub hη'.1⟩

/-- The arithmetic of the final combination in `ent_wordAct_fibre_ge`. -/
theorem final_arith {ℓ d δ ρ L₂ b₀ q G : ℝ} (hℓ : 0 < ℓ) (hδ : 0 ≤ δ) (hρl : 0 ≤ ℓ * ρ * L₂)
    (hd2 : d * L₂ ≤ 1) (hb0 : 0 ≤ b₀) (hb2 : b₀ ≤ 2 * δ) (hq : G ≤ q) :
    ℓ * (d * L₂ - 6 * δ) + ℓ * ρ * L₂ * G ≤
      ℓ * (d * L₂ - 4 * δ) * (1 - b₀) + ℓ * ρ * L₂ * q := by
  have h1 : ℓ * ρ * L₂ * G ≤ ℓ * ρ * L₂ * q := mul_le_mul_of_nonneg_left hq hρl
  have hfirst : ℓ * (d * L₂ - 6 * δ) ≤ ℓ * (d * L₂ - 4 * δ) * (1 - b₀) := by
    rcases le_or_gt 0 (d * L₂ - 4 * δ) with hpos | hneg
    · have hℓX : 0 ≤ ℓ * (d * L₂ - 4 * δ) := mul_nonneg hℓ.le hpos
      have s1 : ℓ * (d * L₂ - 4 * δ) * (1 - 2 * δ) ≤ ℓ * (d * L₂ - 4 * δ) * (1 - b₀) :=
        mul_le_mul_of_nonneg_left (by linarith) hℓX
      have s2 : ℓ * (d * L₂ - 4 * δ) ≤ ℓ * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) hℓ.le
      have s3 : 2 * δ * (ℓ * (d * L₂ - 4 * δ)) ≤ 2 * δ * (ℓ * 1) :=
        mul_le_mul_of_nonneg_left s2 (by positivity)
      nlinarith
    · have hℓX : ℓ * (d * L₂ - 4 * δ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hℓ.le hneg.le
      have s1 : ℓ * (d * L₂ - 4 * δ) * 1 ≤ ℓ * (d * L₂ - 4 * δ) * (1 - b₀) :=
        mul_le_mul_of_nonpos_left (by linarith) hℓX
      have s3 : ℓ * (d * L₂ - 6 * δ) ≤ ℓ * (d * L₂ - 4 * δ) :=
        mul_le_mul_of_nonneg_left (by linarith) hℓ.le
      linarith
  linarith

/-- The lower bound for a typical fibre, Rapaport's (4.14), in nats: if the parameters satisfy
the stated relations and `ξ` has entropy `> Δ n` on the first `n` letters, a remainder of mass
`≤ 2δ`, and is carried by cylinders `[w]` with `x ∈ φ_w(I)`, then
`H((Π_{n+n'} ξ).μ, 𝒟_{ℓ+L}) ≥ ℓ (d log 2 - 6 δ) + ℓ ρ log 2 · Δ / (6 log N)`. -/
theorem ent_wordAct_fibre_ge [NeZero N] (hφ : RapaportHyp φ) {p : Fin N → ℝ}
    (hp : AnalyticESC.IsProbVec p) {C : ℝ} (hC1 : 1 ≤ C) (hCd : distConst φ ≤ C)
    (hHD : ∀ (u : List (Fin N)) (l : ℕ), 1 ≤ l → ∀ x ∈ I,
      |iteratedDeriv l (realComp φ u) x| ≤ l.factorial * C ^ l * |deriv (realComp φ u) 0|)
    {n n' S k ℓ L : ℕ} (hk : 1 ≤ k) (hℓ : 0 < ℓ) {χ δ Δ ε d ρ A : ℝ}
    (hEI : ∀ ν : Measure (Poly k), IsProbabilityMeasure ν →
      (∀ᵐ q ∂ν, ‖q‖ ≤ ε⁻¹ ∧ ∀ x ∈ I, ε ≤ |Poly.derivEval q x|) →
      ε ≤ dyadicEntropyVec ν ℓ / ℓ →
      ∀ ψ : ℝ → ℝ, Set.MapsTo ψ I I → (∀ x ∈ I, HasDerivWithinAt ψ (deriv ψ x) I x) →
        (∀ x ∈ I, ε ≤ |deriv ψ x| ∧ |deriv ψ x| ≤ ε⁻¹) →
        d + ρ ≤ dyadicEntropy (act ν ((selfConformal φ p hp).map ψ)) ℓ / ℓ)
    (hε0 : 0 < ε) (hεnorm : ε * ((k + 1) * (2 * C ^ (k + 3))) ≤ 1) (hεder : ε ≤ (4 * C)⁻¹)
    (hεψ : ε * C ^ 2 ≤ 1) (hεent : ε * ℓ * Real.log 2 ≤ Δ / 6 * n)
    (hS : ⌊2 * n * δ / Real.log 2⌋₊ ≤ S) (hN : 0 < Real.log N) (hΔ : 0 < Δ)
    (hcount : Real.log ((S + 2) * N ^ n') + 2 * δ * (n * Real.log N) ≤ 2 / 3 * (Δ * n))
    (hδ : 0 ≤ δ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hρ : 0 ≤ ρ)
    (hY : ℓ * (d * Real.log 2 - δ) ≤ ent (selfConformal φ p hp) (cellIdx ℓ))
    (herr₁ : Real.log (2 * distConst φ /
      (2 ^ L * (C⁻¹ * Real.exp (-(n * (χ + δ))) * Real.exp (-(n' * (χ + δ))))) + 2) ≤ 3 * δ * ℓ)
    (herr₂ : Real.log 8 + Real.log (2 * A + 2) ≤ 3 * δ * ℓ)
    (hTay : C ^ (k + 1) * Real.exp (-(n * (χ - δ))) *
      (C * Real.exp (-(n' * (χ - δ)))) ^ (k + 1) ≤ 1 / 2 ^ (ℓ + L))
    (hRb : 8 * k * (k + 1) * C ^ (k + 1) * (C * Real.exp (-(n' * (χ - δ)))) ≤ 1)
    (hAe : C * Real.exp (n * (χ + δ)) * Real.exp (n' * (χ + δ)) ≤ 2 ^ L * A)
    (hsep : ∀ w₁ w₂ : Fin (n + n') → Fin N, w₁ ≠ w₂ → (k + 3) / 2 ^ ℓ <
      ⨆ y : I, |wordMap φ w₁ y - wordMap φ w₂ y|)
    (ξ : Measure (ℕ → Fin N)) [IsProbabilityMeasure ξ] (x : ℝ)
    (hE1 : ∀ w : Fin (n + n') → Fin N, ξ (cylinder w) ≠ 0 → x ∈ wordMap φ w '' I)
    (hE2 : Δ * n < ent ξ (pre n))
    (hbad : ξ.real {η | ¬ (GoodWord φ χ δ (pre n η) ∧ GoodWord φ χ δ (pre n' (shift^[n] η)))} ≤
      2 * δ) :
    ℓ * (d * Real.log 2 - 6 * δ) + ℓ * ρ * Real.log 2 * (Δ / (6 * Real.log N)) ≤
      ent (wordAct φ (selfConformal φ p hp) ξ (n + n')) (cellIdx (ℓ + L)) := by
  classical
  set μ := selfConformal φ p hp with hμ
  have hμI : μ Iᶜ = 0 := selfConformal_compl_I hφ hp
  have hμprob : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hWprob := isProbabilityMeasure_wordAct (φ := φ) (θ := μ) ξ (n + n')
  set g := pieceLabel φ χ δ n n' S with hg_def
  have hg : Measurable g := measurable_pieceLabel χ δ n n' S
  set w : Fin (S + 2) × (Fin n' → Fin N) → ℝ := fun b => ξ.real (g ⁻¹' {b}) with hw_def
  set Z : Fin (S + 2) × (Fin n' → Fin N) → Measure (ℕ → Fin N) :=
    fun b => ξ[|g ⁻¹' {b}] with hZ_def
  have hw0 : ∀ b, 0 ≤ w b := fun b => measureReal_nonneg
  have hw1 : ∑ b, w b = 1 :=
    sum_measureReal_fiber hg Finset.univ fun b _ => Finset.mem_univ b
  have hZprob : ∀ b, w b ≠ 0 → IsProbabilityMeasure (Z b) := fun b hb =>
    cond_isProbabilityMeasure (fun h => hb (by simp [hw_def, measureReal_def, h]))
  have hmix : wordAct φ μ ξ (n + n') =
      ∑ b, ENNReal.ofReal (w b) • wordAct φ μ (Z b) (n + n') := by
    conv_lhs => rw [← sum_meas_smul_cond_fiber hg ξ]
    rw [wordAct_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hw_def, hZ_def, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hconc := sum_ent_le_ent_of_ne_zero (θs := fun b => wordAct φ μ (Z b) (n + n')) hw0 hw1
    (fun b hb => by
      have := hZprob b hb
      exact isProbabilityMeasure_wordAct (θ := μ) _ _) hmix (measurable_cellIdx (ℓ + L))
    (finiteLabels_cellIdx (wordAct_compl_I hφ hμI ξ _) _)
  -- lower bounds on the pieces
  set Q := highLabels ξ φ χ δ Δ n n' S with hQ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgoodlb : ∀ b, w b ≠ 0 → b.1 ≠ Fin.last (S + 1) →
      ℓ * (d * Real.log 2 - 4 * δ) ≤ ent (wordAct φ μ (Z b) (n + n')) (cellIdx (ℓ + L)) := by
    intro b hb hlast
    have := hZprob b hb
    obtain ⟨hcarr, hfacts⟩ := piece_facts ξ hS b hlast
    have hβ : 0 < 2 ^ L * (C⁻¹ * Real.exp (-(n * (χ + δ))) * Real.exp (-(n' * (χ + δ)))) := by
      have : 0 < C := zero_lt_one.trans_le hC1
      positivity
    have h := ent_wordAct_ge_of_shift hφ hμI b.2 (Z b) hcarr ℓ L hβ (fun v hv => by
      obtain ⟨hv1, hu1, -, -⟩ := hfacts v hv
      have h1 := abs_deriv_append_ge hφ v b.2
      have h2 : C⁻¹ * |deriv (wordMap φ v) 0| * |deriv (wordMap φ b.2) 0| ≤
          (distConst φ)⁻¹ * |deriv (wordMap φ v) 0| * |deriv (wordMap φ b.2) 0| := by
        gcongr
        exact distConst_pos
      have h3 : C⁻¹ * Real.exp (-(n * (χ + δ))) * Real.exp (-(n' * (χ + δ))) ≤
          C⁻¹ * |deriv (wordMap φ v) 0| * |deriv (wordMap φ b.2) 0| := by
        have : 0 < C := zero_lt_one.trans_le hC1
        gcongr
        · exact hv1.1
        · exact hu1.1
      gcongr
      linarith)
    linarith
  have hhighlb : ∀ b ∈ Q, w b ≠ 0 →
      ℓ * (d * Real.log 2 - 4 * δ) + ℓ * ρ * Real.log 2 ≤
        ent (wordAct φ μ (Z b) (n + n')) (cellIdx (ℓ + L)) := by
    intro b hbQ hb
    have := hZprob b hb
    simp only [hQ, highLabels, Finset.mem_filter, Finset.mem_univ, true_and] at hbQ
    obtain ⟨hlast, hentb⟩ := hbQ
    obtain ⟨hcarr, hfacts⟩ := piece_facts ξ hS b hlast
    have hu1 : ∀ v : Fin n → Fin N, Z b (cylinder v) ≠ 0 → GoodWord φ χ δ b.2 := fun v hv =>
      (hfacts v hv).2.1
    have h := ent_wordAct_ge_of_highPiece hφ hp hC1 hCd hHD hk hℓ (L := L) (A := A) hEI hε0
      hεnorm hεder hεψ b.2 (Z b) hcarr
      (fun v₁ v₂ h₁ h₂ => by
        obtain ⟨g₁, -, s₁, -⟩ := hfacts v₁ h₁
        obtain ⟨g₂, -, s₂, -⟩ := hfacts v₂ h₂
        exact shell_ratio_le g₁ g₂ (s₁.trans s₂.symm))
      (by
        have : Δ / 6 * n ≤ ent (Z b) (pre n) := hentb
        linarith)
      x (fun v hv => hE1 _ (hfacts v hv).2.2.2)
      (by
        obtain ⟨v₀, hv₀⟩ : ∃ v₀ : Fin n → Fin N, Z b (cylinder v₀) ≠ 0 := by
          by_contra h
          push Not at h
          have h1 := sum_measure_cylinder (Z b) n
          simp [h] at h1
        have hu := hu1 v₀ hv₀
        refine le_trans ?_ hRb
        gcongr
        exact hu.2)
      (fun v hv => by
        obtain ⟨hv1, hu1', -, -⟩ := hfacts v hv
        refine le_trans ?_ hTay
        have : 0 < C := zero_lt_one.trans_le hC1
        gcongr
        · exact hv1.2
        · exact hu1'.2)
      (fun v₁ v₂ hne => hsep _ _ (fun h => hne (by
        have := congrArg (fun w : Fin (n + n') → Fin N => fun i : Fin n => w (Fin.castAdd n' i)) h
        simpa using this)))
      (fun v hv => by
        obtain ⟨hv1, hu1', -, -⟩ := hfacts v hv
        refine le_trans ?_ hAe
        have hv0 : 0 < |deriv (wordMap φ v) 0| := (Real.exp_pos _).trans_le hv1.1
        have hu0 : 0 < |deriv (wordMap φ b.2) 0| := (Real.exp_pos _).trans_le hu1'.1
        rw [div_le_iff₀ (by positivity)]
        have e1 : Real.exp (n * (χ + δ)) * |deriv (wordMap φ v) 0| ≥ 1 := by
          have := hv1.1
          rw [Real.exp_neg] at this
          have hpos := Real.exp_pos (n * (χ + δ))
          rw [inv_le_iff_one_le_mul₀ hpos] at this
          linarith
        have e2 : Real.exp (n' * (χ + δ)) * |deriv (wordMap φ b.2) 0| ≥ 1 := by
          have := hu1'.1
          rw [Real.exp_neg] at this
          have hpos := Real.exp_pos (n' * (χ + δ))
          rw [inv_le_iff_one_le_mul₀ hpos] at this
          linarith
        have hC0 : 0 ≤ C := zero_le_one.trans hC1
        calc C = C * 1 * 1 := by ring
          _ ≤ C * (Real.exp (n * (χ + δ)) * |deriv (wordMap φ v) 0|) *
              (Real.exp (n' * (χ + δ)) * |deriv (wordMap φ b.2) 0|) := by gcongr
          _ = C * Real.exp (n * (χ + δ)) * Real.exp (n' * (χ + δ)) *
              (|deriv (wordMap φ v) 0| * |deriv (wordMap φ b.2) 0|) := by ring)
    have hd2 : d * Real.log 2 ≤ 1 := by
      have : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9
        linarith
      nlinarith
    nlinarith
  -- summation
  set lb : Fin (S + 2) × (Fin n' → Fin N) → ℝ := fun b =>
    (if b.1 ≠ Fin.last (S + 1) then ℓ * (d * Real.log 2 - 4 * δ) else 0) +
      (if b ∈ Q then ℓ * ρ * Real.log 2 else 0) with hlb
  have hpiece : ∀ b, w b * lb b ≤ w b * ent (wordAct φ μ (Z b) (n + n')) (cellIdx (ℓ + L)) := by
    intro b
    by_cases hb : w b = 0
    · simp [hb]
    refine mul_le_mul_of_nonneg_left ?_ (hw0 b)
    have := hZprob b hb
    by_cases hbQ : b ∈ Q
    · have hlast : b.1 ≠ Fin.last (S + 1) := by
        simp only [hQ, highLabels, Finset.mem_filter] at hbQ
        exact hbQ.2.1
      simp only [hlb, hlast, hbQ, ne_eq, not_false_eq_true, ite_true]
      exact hhighlb b hbQ hb
    · by_cases hlast : b.1 = Fin.last (S + 1)
      · simp only [hlb, hlast, hbQ, ne_eq, not_true_eq_false, ite_false, add_zero]
        have := isProbabilityMeasure_wordAct (φ := φ) (θ := μ) (Z b) (n + n')
        exact ent_nonneg _
      · simp only [hlb, hlast, hbQ, ne_eq, not_false_eq_true, ite_true, ite_false, add_zero]
        exact hgoodlb b hb hlast
  have hsumQ := mass_highLabels_gt ξ hN hΔ hE2 hbad hcount (φ := φ) (S := S)
  -- the mass of the good labels
  set B : Finset (Fin (S + 2) × (Fin n' → Fin N)) :=
    Finset.univ.filter fun b => b.1 = Fin.last (S + 1) with hB
  have hBmass : ∑ b ∈ B, w b ≤ 2 * δ := by
    rw [sum_measureReal_preimage hg B]
    refine (measureReal_mono ?_).trans hbad
    intro η hη
    simp only [mem_preimage, Finset.coe_filter, Finset.mem_univ, true_and, mem_ofPred_eq,
      hB] at hη ⊢
    intro hgood
    simp only [hg_def, pieceLabel, pairLabel, hgood, and_self, ite_true] at hη
    exact Fin.castSucc_ne_last _ hη
  have hsplit : ∑ b, w b * lb b = ℓ * (d * Real.log 2 - 4 * δ) * (1 - ∑ b ∈ B, w b) +
      ℓ * ρ * Real.log 2 * ∑ b ∈ Q, w b := by
    have hc : ∑ b ∈ Bᶜ, w b = 1 - ∑ b ∈ B, w b := by
      have := Finset.sum_compl_add_sum B w
      rw [hw1] at this
      linarith
    have e1 : ∑ b, w b * (if b.1 ≠ Fin.last (S + 1) then ℓ * (d * Real.log 2 - 4 * δ) else 0) =
        ℓ * (d * Real.log 2 - 4 * δ) * ∑ b ∈ Bᶜ, w b := by
      rw [hB, Finset.compl_filter, Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> ring
    have e2 : ∑ b, w b * (if b ∈ Q then ℓ * ρ * Real.log 2 else 0) =
        ℓ * ρ * Real.log 2 * ∑ b ∈ Q, w b := by
      rw [← Finset.sum_subset (Finset.subset_univ Q) (fun b _ hb => by simp [hb]),
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun b hb => by simp [hb, mul_comm]
    simp only [hlb, mul_add, Finset.sum_add_distrib]
    rw [e1, e2, hc]
  have hfinal : ℓ * (d * Real.log 2 - 6 * δ) + ℓ * ρ * Real.log 2 * (Δ / (6 * Real.log N)) ≤
      ∑ b, w b * lb b := by
    rw [hsplit]
    have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    have hd2 : d * Real.log 2 ≤ 1 := by
      have : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9
        linarith
      nlinarith
    exact final_arith hℓ' hδ (by positivity) hd2 (Finset.sum_nonneg fun b _ => hw0 b) hBmass
      hsumQ.le
  calc _ ≤ ∑ b, w b * lb b := hfinal
    _ ≤ ∑ b, w b * ent (wordAct φ μ (Z b) (n + n')) (cellIdx (ℓ + L)) :=
        Finset.sum_le_sum fun b _ => hpiece b
    _ ≤ _ := hconc

end FractalGeometry.Rapaport.Analytic.SectionFour
