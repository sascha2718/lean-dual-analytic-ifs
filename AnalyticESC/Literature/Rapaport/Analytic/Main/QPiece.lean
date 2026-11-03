module

public import AnalyticESC.Literature.Rapaport.Analytic.Main.PieceBounds
public import AnalyticESC.Literature.Rapaport.Analytic.Main.Taylor
public import AnalyticESC.Literature.Rapaport.Analytic.Main.Polys

@[expose] public section

/-!
# Entropy increase for the high-entropy pieces

The central step of the proof of Theorem 1.2 of A. Rapaport, *Dimension of self-conformal
measures associated to an exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2,
Section 4 (from (4.6) to (4.13)): for a piece `ζ = (β_ω)_{F_{j,u}}` of large entropy, the
measure `(Π_{n+n'} ζ).μ` is compared with `ν.(ψ φ_u μ)` for a measure `ν` on polynomials of
degree `≤ k` (the renormalised Taylor polynomials of the maps `φ_v`), and the entropy increase
theorem (Theorem 3.1) applies to `ν`.

Rapaport normalises by the affine map `ψ` with `ψ(φ_u(0)) = 0` and `ψ(φ_u(1)) = 1`; here
`ψ(y) = r (y - a)` with `a = inf φ_u(I)` and `r = 1 / diam φ_u(I)`, so that `r > 0` and
`ψ(φ_u(I)) = I`, and the Taylor polynomials are centred at `a ∈ φ_u(I)`.

## Main declarations

* `exists_normalisation`: the interval `φ_u(I) = [a, a + D]` with `D` comparable to `|φ_u'(0)|`.
* `abs_deriv_append_le`, `abs_deriv_append_ge`: `|φ_{vu}'(0)|` is comparable to
  `|φ_v'(0)| |φ_u'(0)|`.
* `abs_polyOf_le_of_ne_zero`, `abs_wordMap_sub_le`, `polyOf_bounds`: the bounds (4.10) on the
  norm and on the derivative of the renormalised Taylor polynomials.
* `ent_comparison`: Lemmas 2.2 and 2.3 combined, for images of a common measure.
* `ae_map_map_pre`, `ent_pre_le_ent_map`: the measure `ν` on polynomials and its entropy.
* `cellIdxVec_polyOf_injective`: exponential separation separates the polynomials (4.12).
* `ent_wordAct_ge_of_highPiece`: the entropy increase (4.13) for a high-entropy piece.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Main.QPiece`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic.SectionFour

open MeasureTheory ProbabilityTheory Set Filter Topology FractalGeometry.SelfConformal
open FractalGeometry.Rapaport.Analytic
open AnalyticESC (I realComp RapaportHyp)
open scoped ENNReal

variable {N : ℕ} {φ : Fin N → ℝ → ℝ}

/-! ### The normalisation of `φ_u(I)` -/

/-- `φ_u(I)` is an interval `[a, a + D]` with `C⁻¹ |φ_u'(0)| ≤ D ≤ C |φ_u'(0)|` and `D ≤ 1`. -/
theorem exists_normalisation (hφ : RapaportHyp φ) {n' : ℕ} (u : Fin n' → Fin N) {C : ℝ}
    (hC : distConst φ ≤ C) :
    ∃ a D : ℝ, a ∈ wordMap φ u '' I ∧ 0 < D ∧ C⁻¹ * |deriv (wordMap φ u) 0| ≤ D ∧
      D ≤ C * |deriv (wordMap φ u) 0| ∧ D ≤ 1 ∧
      ∀ y ∈ I, a ≤ wordMap φ u y ∧ wordMap φ u y ≤ a + D := by
  set J := wordMap φ u '' I with hJ
  have hJc : IsCompact J := isCompact_I.image_of_continuousOn (continuousOn_realComp hφ _)
  have hJne : J.Nonempty := ⟨_, mem_image_of_mem _ zero_mem_I⟩
  have hC0 : 0 < distConst φ := distConst_pos
  have hCpos : 0 < C := hC0.trans_le hC
  have hdiam : Metric.diam J = sSup J - sInf J := Real.diam_eq hJc.isBounded
  have hlow := distConst_inv_mul_le_diam_image_realComp hφ (List.ofFn u) zero_mem_I
  have hup := diam_image_realComp_le hφ (List.ofFn u) zero_mem_I
  rw [← wordMap_def, ← hJ, hdiam] at hlow hup
  have hd0 : 0 < |deriv (wordMap φ u) 0| :=
    abs_pos.2 (deriv_realComp_ne_zero hφ (List.ofFn u) zero_mem_I)
  refine ⟨sInf J, sSup J - sInf J, hJc.sInf_mem hJne, ?_, ?_, ?_, ?_, ?_⟩
  · refine lt_of_lt_of_le ?_ hlow
    positivity
  · refine le_trans ?_ hlow
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hC0 hC) (abs_nonneg _)
  · exact hup.trans (mul_le_mul_of_nonneg_right hC (abs_nonneg _))
  · rw [← hdiam]
    calc Metric.diam J ≤ Metric.diam I := Metric.diam_mono (by
          rintro _ ⟨y, hy, rfl⟩
          exact mapsTo_realComp hφ _ hy) isCompact_Icc.isBounded
      _ = 1 := by rw [Real.diam_Icc zero_le_one]; norm_num
  · intro y hy
    have hmem : wordMap φ u y ∈ J := mem_image_of_mem _ hy
    exact ⟨csInf_le hJc.bddBelow hmem, by linarith [le_csSup hJc.bddAbove hmem]⟩

/-! ### Derivatives of concatenated words -/

/-- `|φ_{vu}'(0)| ≤ C |φ_v'(0)| |φ_u'(0)|` with the distortion constant. -/
theorem abs_deriv_append_le (hφ : RapaportHyp φ) {n n' : ℕ} (v : Fin n → Fin N)
    (u : Fin n' → Fin N) :
    |deriv (wordMap φ (Fin.append v u)) 0| ≤
      distConst φ * |deriv (wordMap φ v) 0| * |deriv (wordMap φ u) 0| := by
  rw [wordMap_def (Fin.append v u), List.ofFn_fin_append,
    deriv_realComp_append hφ _ _ zero_mem_I, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  exact abs_deriv_realComp_le hφ _ (mapsTo_realComp hφ _ zero_mem_I) zero_mem_I

/-- `|φ_{vu}'(0)| ≥ C⁻¹ |φ_v'(0)| |φ_u'(0)|` with the distortion constant. -/
theorem abs_deriv_append_ge (hφ : RapaportHyp φ) {n n' : ℕ} (v : Fin n → Fin N)
    (u : Fin n' → Fin N) :
    (distConst φ)⁻¹ * |deriv (wordMap φ v) 0| * |deriv (wordMap φ u) 0| ≤
      |deriv (wordMap φ (Fin.append v u)) 0| := by
  rw [wordMap_def (Fin.append v u), List.ofFn_fin_append,
    deriv_realComp_append hφ _ _ zero_mem_I, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have h := abs_deriv_realComp_le hφ (List.ofFn v) zero_mem_I
    (mapsTo_realComp hφ (List.ofFn u) zero_mem_I)
  rw [inv_mul_le_iff₀ distConst_pos]
  exact h

/-! ### Coefficient bounds for the renormalised Taylor polynomials -/

section Coefficients

variable {k : ℕ} {C α r a x : ℝ}

/-- The coefficients of positive degree: `|q_j| ≤ 2 C^j (r⁻¹)^{j-1}`. -/
theorem abs_polyOf_le_of_ne_zero {n : ℕ} (v : Fin n → Fin N)
    (hHD : ∀ (u : List (Fin N)) (l : ℕ), 1 ≤ l → ∀ x ∈ I,
      |iteratedDeriv l (realComp φ u) x| ≤ l.factorial * C ^ l * |deriv (realComp φ u) 0|)
    (hC0 : 0 ≤ C) (hα0 : 0 < α) (hα : α * |deriv (wordMap φ v) 0| ≤ 2) (hr : 0 < r)
    (haI : a ∈ I)
    {j : Fin (k + 1)} (hj : (j : ℕ) ≠ 0) :
    |polyOf k α r a x (wordMap φ v) j| ≤ 2 * C ^ (j : ℕ) * (r⁻¹) ^ ((j : ℕ) - 1) := by
  rw [polyOf_of_ne_zero _ _ _ _ _ hj]
  have hfac : (0 : ℝ) < ((j : ℕ).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hb := hHD (List.ofFn v) j (Nat.pos_of_ne_zero hj) a haI
  rw [← wordMap_def] at hb
  have hrj : r * (r⁻¹) ^ (j : ℕ) = (r⁻¹) ^ ((j : ℕ) - 1) := by
    obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [hi, pow_succ, Nat.succ_sub_one]
    field_simp
  calc |α * r * ((r⁻¹) ^ (j : ℕ) * (iteratedDeriv j (wordMap φ v) a /
        ((j : ℕ).factorial : ℝ)))|
      = α * (r * (r⁻¹) ^ (j : ℕ)) * (|iteratedDeriv j (wordMap φ v) a| /
          ((j : ℕ).factorial : ℝ)) := by
        rw [abs_mul, abs_mul, abs_mul, abs_div, abs_of_pos hα0, abs_of_pos hr,
          abs_of_pos (pow_pos (inv_pos.2 hr) _), abs_of_pos hfac]
        ring
    _ ≤ α * (r * (r⁻¹) ^ (j : ℕ)) * (C ^ (j : ℕ) * |deriv (wordMap φ v) 0|) := by
        gcongr
        rw [div_le_iff₀ hfac]
        linarith [hb]
    _ = (α * |deriv (wordMap φ v) 0|) * (C ^ (j : ℕ) * (r⁻¹) ^ ((j : ℕ) - 1)) := by
        rw [hrj]
        ring
    _ ≤ 2 * (C ^ (j : ℕ) * (r⁻¹) ^ ((j : ℕ) - 1)) :=
        mul_le_mul_of_nonneg_right hα (by positivity)
    _ = 2 * C ^ (j : ℕ) * (r⁻¹) ^ ((j : ℕ) - 1) := by ring

/-- `|φ_v(a) - x| ≤ C² |φ_v'(0)| |φ_u'(0)|` for `a ∈ φ_u(I)` and `x ∈ φ_{vu}(I)`. -/
theorem abs_wordMap_sub_le (hφ : RapaportHyp φ) (hCd : distConst φ ≤ C) {n n' : ℕ}
    (v : Fin n → Fin N) (u : Fin n' → Fin N) (ha : a ∈ wordMap φ u '' I)
    (hx : x ∈ wordMap φ (Fin.append v u) '' I) :
    |wordMap φ v a - x| ≤ C ^ 2 * |deriv (wordMap φ v) 0| * |deriv (wordMap φ u) 0| := by
  obtain ⟨y₀, hy₀, rfl⟩ := ha
  obtain ⟨y₁, hy₁, rfl⟩ := hx
  have hcomp : wordMap φ v (wordMap φ u y₀) = wordMap φ (Fin.append v u) y₀ := by
    rw [wordMap_append]
    rfl
  rw [hcomp]
  have h1 := abs_realComp_sub_le_distConst hφ (List.ofFn (Fin.append v u)) hy₀ hy₁ zero_mem_I
  rw [← wordMap_def] at h1
  have h2 : |y₀ - y₁| ≤ 1 := abs_sub_le_one_of_mem_I hy₀ hy₁
  have h3 := abs_deriv_append_le hφ v u
  have hC0 : 0 ≤ distConst φ := distConst_pos.le
  have hC0' : 0 ≤ C := hC0.trans hCd
  calc |wordMap φ (Fin.append v u) y₀ - wordMap φ (Fin.append v u) y₁|
      ≤ distConst φ * |deriv (wordMap φ (Fin.append v u)) 0| * |y₀ - y₁| := h1
    _ ≤ distConst φ * (distConst φ * |deriv (wordMap φ v) 0| * |deriv (wordMap φ u) 0|) * 1 := by
        gcongr
    _ ≤ C * (C * |deriv (wordMap φ v) 0| * |deriv (wordMap φ u) 0|) * 1 := by gcongr
    _ = C ^ 2 * |deriv (wordMap φ v) 0| * |deriv (wordMap φ u) 0| := by ring

/-- The renormalised Taylor polynomial of `φ_v` satisfies the hypotheses of the entropy increase
theorem (Rapaport's (4.10)): `‖q‖ ≤ (k + 1) 2 C^{k+3}` and `|q'| ≥ (4 C)⁻¹` on `I`. -/
theorem polyOf_bounds (hφ : RapaportHyp φ) (hC1 : 1 ≤ C) (hCd : distConst φ ≤ C)
    (hHD : ∀ (u : List (Fin N)) (l : ℕ), 1 ≤ l → ∀ x ∈ I,
      |iteratedDeriv l (realComp φ u) x| ≤ l.factorial * C ^ l * |deriv (realComp φ u) 0|)
    {n n' : ℕ} (v : Fin n → Fin N) (u : Fin n' → Fin N) (hk : 1 ≤ k) (hα0 : 0 < α)
    (hα1 : 1 / 2 ≤ α * |deriv (wordMap φ v) 0|) (hα2 : α * |deriv (wordMap φ v) 0| ≤ 2)
    (hr1 : 1 ≤ r) (hru : r * |deriv (wordMap φ u) 0| ≤ C)
    (hrbig : 8 * k * (k + 1) * C ^ (k + 1) ≤ r) (ha : a ∈ wordMap φ u '' I)
    (hx : x ∈ wordMap φ (Fin.append v u) '' I) :
    ‖polyOf k α r a x (wordMap φ v)‖ ≤ (k + 1) * (2 * C ^ (k + 3)) ∧
      ∀ z ∈ I, (4 * C)⁻¹ ≤ |Poly.derivEval (polyOf k α r a x (wordMap φ v)) z| := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC1
  have hr0 : 0 < r := zero_lt_one.trans_le hr1
  have haI : a ∈ I := by
    obtain ⟨y, hy, rfl⟩ := ha
    exact mapsTo_realComp hφ _ hy
  have hrinv : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
  have hrinv0 : 0 ≤ r⁻¹ := inv_nonneg.2 hr0.le
  constructor
  · refine norm_le_of_forall_abs_le _ fun j => ?_
    by_cases hj : (j : ℕ) = 0
    · have hj0 : j = 0 := Fin.ext hj
      rw [hj0, polyOf_zero, abs_mul, abs_mul, abs_of_pos hα0, abs_of_pos hr0]
      have h1 := abs_wordMap_sub_le hφ hCd v u ha hx
      calc α * r * |wordMap φ v a - x|
          ≤ α * r * (C ^ 2 * |deriv (wordMap φ v) 0| * |deriv (wordMap φ u) 0|) := by gcongr
        _ = C ^ 2 * (α * |deriv (wordMap φ v) 0|) * (r * |deriv (wordMap φ u) 0|) := by ring
        _ ≤ C ^ 2 * 2 * C := by gcongr
        _ = 2 * C ^ 3 := by ring
        _ ≤ 2 * C ^ (k + 3) := by
            have : C ^ 3 ≤ C ^ (k + 3) := pow_le_pow_right₀ hC1 (by omega)
            linarith
    · refine (abs_polyOf_le_of_ne_zero v hHD hC0.le hα0 hα2 hr0 haI hj).trans ?_
      have hjk : (j : ℕ) ≤ k + 3 := by omega
      calc 2 * C ^ (j : ℕ) * (r⁻¹) ^ ((j : ℕ) - 1) ≤ 2 * C ^ (j : ℕ) * 1 := by
            gcongr
            exact pow_le_one₀ hrinv0 hrinv
        _ ≤ 2 * C ^ (k + 3) := by
            have : C ^ (j : ℕ) ≤ C ^ (k + 3) := pow_le_pow_right₀ hC1 hjk
            linarith
  · intro z hz
    have hz1 : |z| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hz.1, hz.2]
    have hB0 : 0 ≤ 2 * C ^ k / r := by positivity
    have hA : (2 * C)⁻¹ ≤ |polyOf k α r a x (wordMap φ v) ⟨1, by omega⟩| := by
      rw [polyOf_of_ne_zero _ _ _ _ _ (by simp)]
      simp only [pow_one, iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, div_one]
      have hd := abs_deriv_realComp_le hφ (List.ofFn v) zero_mem_I haI
      rw [← wordMap_def] at hd
      have : α * r * (r⁻¹ * deriv (wordMap φ v) a) = α * deriv (wordMap φ v) a := by
        field_simp
      rw [this, abs_mul, abs_of_pos hα0]
      have h3 : |deriv (wordMap φ v) 0| ≤ C * |deriv (wordMap φ v) a| :=
        hd.trans (mul_le_mul_of_nonneg_right hCd (abs_nonneg _))
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      nlinarith
    have hB : ∀ j : Fin (k + 1), 2 ≤ (j : ℕ) →
        |polyOf k α r a x (wordMap φ v) j| ≤ 2 * C ^ k / r := by
      intro j hj
      refine (abs_polyOf_le_of_ne_zero v hHD hC0.le hα0 hα2 hr0 haI (by omega)).trans ?_
      have hjk : (j : ℕ) ≤ k := Nat.lt_succ_iff.1 j.2
      calc 2 * C ^ (j : ℕ) * (r⁻¹) ^ ((j : ℕ) - 1) ≤ 2 * C ^ k * r⁻¹ := by
            have hp1 : (r⁻¹) ^ ((j : ℕ) - 1) ≤ r⁻¹ := by
              calc (r⁻¹) ^ ((j : ℕ) - 1) ≤ (r⁻¹) ^ 1 :=
                    pow_le_pow_of_le_one hrinv0 hrinv (by omega)
                _ = r⁻¹ := pow_one _
            have hp2 : C ^ (j : ℕ) ≤ C ^ k := pow_le_pow_right₀ hC1 hjk
            gcongr
        _ = 2 * C ^ k / r := by ring
    have key := le_abs_derivEval_of_coeff hk _ hB0 hA hB hz1
    refine le_trans ?_ key
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have h4 : (k : ℝ) * (k + 1) * (2 * C ^ k / r) ≤ (4 * C)⁻¹ := by
      rw [show (k : ℝ) * (k + 1) * (2 * C ^ k / r) = 2 * k * (k + 1) * C ^ k / r by ring,
        div_le_iff₀ hr0]
      rw [pow_succ] at hrbig
      have : (4 * C)⁻¹ * r ≥ (4 * C)⁻¹ * (8 * k * (k + 1) * (C ^ k * C)) := by gcongr
      have h5 : (4 * C)⁻¹ * (8 * k * (k + 1) * (C ^ k * C)) = 2 * k * (k + 1) * C ^ k := by
        field_simp
        ring
      linarith
    have h6 : (2 * C)⁻¹ - (4 * C)⁻¹ = (4 * C)⁻¹ := by
      field_simp
      ring
    linarith

end Coefficients

/-! ### Comparison of entropies of images -/

/-- Lemmas 2.2 and 2.3 of Rapaport combined: if `H = s (G - x₀)` and `|F - G| ≤ 2^{-(ℓ+L)}` on a
set of full measure on which `F` takes values in `I`, then
`H(θ, H⁻¹𝒟_ℓ) ≤ H(θ, F⁻¹𝒟_{ℓ+L}) + log 8 + log (2 s / 2^L + 2)`. -/
theorem ent_comparison {X : Type*} [MeasurableSpace X] {Ω : Measure X} [IsProbabilityMeasure Ω]
    {F G H : X → ℝ} (hF : Measurable F) (hG : Measurable G) (hH : Measurable H) {S : Set X}
    (hS : MeasurableSet S) (hSΩ : Ω Sᶜ = 0) {ℓ L : ℕ} {s x₀ : ℝ} (hs : 0 ≤ s)
    (hHG : ∀ z ∈ S, H z = s * (G z - x₀)) (hFG : ∀ z ∈ S, |F z - G z| ≤ 1 / 2 ^ (ℓ + L))
    (hFI : ∀ z ∈ S, F z ∈ I) :
    ent Ω (cellIdx ℓ ∘ H) ≤
      ent Ω (cellIdx (ℓ + L) ∘ F) + Real.log 8 + Real.log (2 * s / 2 ^ L + 2) := by
  have hSae : ∀ᵐ z ∂Ω, z ∈ S := mem_ae_iff.2 hSΩ
  have hsmall : (1 : ℝ) / 2 ^ (ℓ + L) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have hGbd : ∀ z ∈ S, G z ∈ Icc (-1 : ℝ) 2 := by
    intro z hz
    have h1 := hFG z hz
    have h2 := hFI z hz
    rw [abs_le] at h1
    constructor <;> linarith [h2.1, h2.2]
  have hfinF : FiniteLabels Ω (cellIdx (ℓ + L) ∘ F) :=
    finiteLabels_cellIdx_comp (a := 0) (b := 1) _ (by
      filter_upwards [hSae] with z hz using hFI z hz)
  have hfinG : FiniteLabels Ω (cellIdx (ℓ + L) ∘ G) :=
    finiteLabels_cellIdx_comp (a := -1) (b := 2) _ (by
      filter_upwards [hSae] with z hz using hGbd z hz)
  have hfinH : FiniteLabels Ω (cellIdx ℓ ∘ H) :=
    finiteLabels_cellIdx_comp (a := s * (-1 - x₀)) (b := s * (2 - x₀)) _ (by
      filter_upwards [hSae] with z hz
      rw [hHG z hz]
      have := hGbd z hz
      exact ⟨mul_le_mul_of_nonneg_left (by linarith [this.1]) hs,
        mul_le_mul_of_nonneg_left (by linarith [this.2]) hs⟩)
  have h1 := ent_cellIdx_comp_le (θ := Ω) (F := H) (g := cellIdx (ℓ + L) ∘ G) hH
    ((measurable_cellIdx _).comp hG) ℓ hfinH hfinG hS hSΩ (r := s / 2 ^ (ℓ + L))
    (by positivity) (fun z hz z' hz' h => by
      have hlt := abs_sub_lt_of_cellIdx_eq h
      rw [hHG z hz, hHG z' hz', ← mul_sub, abs_mul, abs_of_nonneg hs,
        show G z - x₀ - (G z' - x₀) = G z - G z' by ring]
      calc s * |G z - G z'| ≤ s * (1 / 2 ^ (ℓ + L)) := mul_le_mul_of_nonneg_left hlt.le hs
        _ = s / 2 ^ (ℓ + L) := by ring)
  have h2 := ent_cellIdx_comp_le (θ := Ω) (F := G) (g := cellIdx (ℓ + L) ∘ F) hG
    ((measurable_cellIdx _).comp hF) (ℓ + L) hfinG hfinF hS hSΩ (r := 3 / 2 ^ (ℓ + L))
    (by positivity) (fun z hz z' hz' h => by
      have hlt := abs_sub_lt_of_cellIdx_eq h
      have a1 := hFG z hz
      have a2 := hFG z' hz'
      calc |G z - G z'| ≤ |F z - G z| + |F z - F z'| + |F z' - G z'| := by
            have := abs_sub_le (G z) (F z) (G z')
            have := abs_sub_le (F z) (F z') (G z')
            rw [abs_sub_comm (G z) (F z)] at *
            linarith
        _ ≤ 1 / 2 ^ (ℓ + L) + 1 / 2 ^ (ℓ + L) + 1 / 2 ^ (ℓ + L) := by linarith
        _ = 3 / 2 ^ (ℓ + L) := by ring)
  have he1 : (2 : ℝ) ^ ℓ * (2 * (s / 2 ^ (ℓ + L))) + 2 = 2 * s / 2 ^ L + 2 := by
    rw [pow_add]
    field_simp
  have he2 : (2 : ℝ) ^ (ℓ + L) * (2 * (3 / 2 ^ (ℓ + L))) + 2 = 8 := by
    field_simp
    norm_num
  rw [he1] at h1
  rw [he2] at h2
  linarith

/-! ### The measure on polynomials -/

/-- The labels of positive mass of `ζ.map (pre n)` carry almost all of its mass. -/
theorem compl_cylinder_null (ζ : Measure (ℕ → Fin N)) (n : ℕ) :
    ζ {η | ζ (cylinder (pre n η)) = 0} = 0 := by
  have he : {η | ζ (cylinder (pre n η)) = 0} =
      ⋃ v ∈ {v : Fin n → Fin N | ζ (cylinder v) = 0}, cylinder v := by
    ext η
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
    constructor
    · intro h
      exact ⟨pre n η, h, mem_cylinder_pre n η⟩
    · rintro ⟨v, hv, hη⟩
      have : pre n η = v := funext fun k => hη k
      rwa [this]
  rw [he, measure_biUnion_null_iff (Set.to_countable _)]
  exact fun v hv => hv

/-- Almost every point of `ζ.map (pre n)` has positive mass. -/
theorem ae_map_pre_ne_zero (ζ : Measure (ℕ → Fin N)) (n : ℕ) :
    ∀ᵐ v ∂(ζ.map (pre n)), ζ (cylinder v) ≠ 0 := by
  rw [ae_map_iff (measurable_pre n).aemeasurable (MeasurableSet.of_discrete)]
  rw [ae_iff]
  simpa using compl_cylinder_null ζ n

/-- The masses of `ζ.map (pre n)` are the cylinder masses. -/
theorem map_pre_singleton (ζ : Measure (ℕ → Fin N)) {n : ℕ} (v : Fin n → Fin N) :
    ζ.map (pre n) {v} = ζ (cylinder v) := by
  rw [Measure.map_apply (measurable_pre n) (measurableSet_singleton v), pre_preimage_singleton]

/-- A property of the polynomials `q v`, `ζ[v] > 0`, holds almost everywhere for the image of
`ζ.map (pre n)` under `q`. -/
theorem ae_map_map_pre {k : ℕ} (ζ : Measure (ℕ → Fin N)) (n : ℕ) (q : (Fin n → Fin N) → Poly k)
    {P : Poly k → Prop} (hP : ∀ v, ζ (cylinder v) ≠ 0 → P (q v)) :
    ∀ᵐ q' ∂((ζ.map (pre n)).map q), P q' := by
  have hT : MeasurableSet (q '' {v | ζ (cylinder v) ≠ 0}) :=
    (Set.toFinite _ |>.image q).measurableSet
  have h : ∀ᵐ q' ∂((ζ.map (pre n)).map q), q' ∈ q '' {v | ζ (cylinder v) ≠ 0} := by
    rw [ae_map_iff (measurable_of_countable q).aemeasurable
      (p := fun q' => q' ∈ q '' {v | ζ (cylinder v) ≠ 0}) hT]
    filter_upwards [ae_map_pre_ne_zero ζ n] with v hv
    exact mem_image_of_mem q hv
  filter_upwards [h] with q' hq'
  obtain ⟨v, hv, rfl⟩ := hq'
  exact hP v hv

/-- If `v ↦ 𝒟_ℓ(q v)` is injective on the words of positive mass, then the entropy of the image
measure on polynomials is at least the entropy of the first `n` letters. -/
theorem ent_pre_le_ent_map {k : ℕ} (ζ : Measure (ℕ → Fin N)) [IsProbabilityMeasure ζ]
    (n ℓ : ℕ) (q : (Fin n → Fin N) → Poly k)
    (hinj : ∀ v₁ v₂, ζ (cylinder v₁) ≠ 0 → ζ (cylinder v₂) ≠ 0 →
      cellIdxVec ℓ (q v₁) = cellIdxVec ℓ (q v₂) → v₁ = v₂) :
    ent ζ (pre n) ≤ ent ((ζ.map (pre n)).map q) (cellIdxVec ℓ) := by
  classical
  have hq : Measurable q := measurable_of_countable q
  rw [Measure.map_map hq (measurable_pre n), ent_map (hq.comp (measurable_pre n))
    (measurable_cellIdxVec' ℓ)]
  set g := cellIdxVec ℓ ∘ (q ∘ pre n) with hg_def
  have hgm : Measurable g := (measurable_cellIdxVec' ℓ).comp (hq.comp (measurable_pre n))
  have hfinf : FiniteLabels ζ (pre (N := N) n) := Set.toFinite _
  have hfing : FiniteLabels ζ g := by
    refine (Set.finite_range (cellIdxVec ℓ ∘ q)).subset fun c hc => ?_
    by_contra hcr
    apply hc
    refine measure_mono_null (fun η hη => ?_) measure_empty
    exact hcr ⟨pre n η, hη⟩
  set S : Set (ℕ → Fin N) := {η | ζ (cylinder (pre n η)) ≠ 0} with hS_def
  have hS : MeasurableSet S :=
    measurable_pre n (MeasurableSet.of_discrete (s := {v : Fin n → Fin N | ζ (cylinder v) ≠ 0}))
  have hSc : ζ Sᶜ = 0 := by
    have : Sᶜ = {η | ζ (cylinder (pre n η)) = 0} := by
      ext η
      simp [hS_def]
    rw [this]
    exact compl_cylinder_null ζ n
  have key := ent_le_ent_add_log_of_fiber_card_on (measurable_pre n) hgm hfinf hfing hS hSc
    (N := 1) fun c => ⟨Finset.univ.filter fun v => ζ (cylinder v) ≠ 0 ∧ cellIdxVec ℓ (q v) = c,
      Finset.card_le_one.2 fun v₁ h₁ v₂ h₂ => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
        exact hinj v₁ v₂ h₁.1 h₂.1 (h₁.2.trans h₂.2.symm),
      fun η hη hgc => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hη, hgc⟩⟩
  simpa using key

/-! ### Separation of the polynomials -/

/-- Exponential separation forces distinct words of positive mass to give polynomials in distinct
dyadic cells of `𝒫_k` (Rapaport's (4.11) and (4.12)). -/
theorem cellIdxVec_polyOf_injective {n n' k ℓ : ℕ} (u : Fin n' → Fin N)
    (ζ : Measure (ℕ → Fin N)) {α r a x : ℝ} (hr : 0 < r) (hαr : 1 ≤ α * r)
    (hnorm : ∀ y ∈ I, a ≤ wordMap φ u y ∧ wordMap φ u y ≤ a + r⁻¹)
    (htaylor : ∀ v : Fin n → Fin N, ζ (cylinder v) ≠ 0 → ∀ y ∈ I, |wordMap φ v (wordMap φ u y) -
      Poly.eval (Poly.taylor k a (wordMap φ v)) (wordMap φ u y)| ≤ 1 / 2 ^ ℓ)
    (hsep : ∀ v₁ v₂ : Fin n → Fin N, v₁ ≠ v₂ → (k + 3) / 2 ^ ℓ <
      ⨆ y : I, |wordMap φ (Fin.append v₁ u) y - wordMap φ (Fin.append v₂ u) y|) :
    ∀ v₁ v₂ : Fin n → Fin N, ζ (cylinder v₁) ≠ 0 → ζ (cylinder v₂) ≠ 0 →
      cellIdxVec ℓ (polyOf k α r a x (wordMap φ v₁)) =
        cellIdxVec ℓ (polyOf k α r a x (wordMap φ v₂)) → v₁ = v₂ := by
  intro v₁ v₂ h₁ h₂ heq
  by_contra hne
  obtain ⟨⟨y, hy⟩, hlt⟩ := exists_lt_of_lt_ciSup (hsep v₁ v₂ hne)
  simp only at hlt
  set t := wordMap φ u y with ht
  have hz : |r * (t - a)| ≤ 1 := by
    obtain ⟨hy1, hy2⟩ := hnorm y hy
    rw [abs_le]
    constructor
    · nlinarith
    · have : r * (t - a) ≤ r * r⁻¹ := mul_le_mul_of_nonneg_left (by linarith) hr.le
      rwa [mul_inv_cancel₀ hr.ne'] at this
  have hclose := abs_eval_sub_lt_of_cellIdxVec_eq heq hz
  rw [eval_polyOf α hr.ne', eval_polyOf α hr.ne', ← mul_sub,
    show Poly.eval (Poly.taylor k a (wordMap φ v₁)) t - x -
      (Poly.eval (Poly.taylor k a (wordMap φ v₂)) t - x) =
      Poly.eval (Poly.taylor k a (wordMap φ v₁)) t -
        Poly.eval (Poly.taylor k a (wordMap φ v₂)) t by ring, abs_mul] at hclose
  have hP : |Poly.eval (Poly.taylor k a (wordMap φ v₁)) t -
      Poly.eval (Poly.taylor k a (wordMap φ v₂)) t| < (k + 1) / 2 ^ ℓ := by
    have hαr0 : 0 ≤ |α * r| := abs_nonneg _
    have : |α * r| ≥ 1 := by rw [abs_of_nonneg (by linarith)]; exact hαr
    nlinarith [abs_nonneg (Poly.eval (Poly.taylor k a (wordMap φ v₁)) t -
      Poly.eval (Poly.taylor k a (wordMap φ v₂)) t)]
  have e₁ : wordMap φ (Fin.append v₁ u) y = wordMap φ v₁ t := by rw [wordMap_append]; rfl
  have e₂ : wordMap φ (Fin.append v₂ u) y = wordMap φ v₂ t := by rw [wordMap_append]; rfl
  rw [e₁, e₂] at hlt
  have t₁ := htaylor v₁ h₁ y hy
  have t₂ := htaylor v₂ h₂ y hy
  rw [← ht] at t₁ t₂
  have htri : |wordMap φ v₁ t - wordMap φ v₂ t| ≤
      |wordMap φ v₁ t - Poly.eval (Poly.taylor k a (wordMap φ v₁)) t| +
      |Poly.eval (Poly.taylor k a (wordMap φ v₁)) t -
        Poly.eval (Poly.taylor k a (wordMap φ v₂)) t| +
      |wordMap φ v₂ t - Poly.eval (Poly.taylor k a (wordMap φ v₂)) t| := by
    have := abs_sub_le (wordMap φ v₁ t) (Poly.eval (Poly.taylor k a (wordMap φ v₁)) t)
      (wordMap φ v₂ t)
    have := abs_sub_le (Poly.eval (Poly.taylor k a (wordMap φ v₁)) t)
      (Poly.eval (Poly.taylor k a (wordMap φ v₂)) t) (wordMap φ v₂ t)
    rw [abs_sub_comm (Poly.eval (Poly.taylor k a (wordMap φ v₂)) t) (wordMap φ v₂ t)] at this
    linarith
  have : (k + 3 : ℝ) / 2 ^ ℓ = 1 / 2 ^ ℓ + (k + 1) / 2 ^ ℓ + 1 / 2 ^ ℓ := by ring
  linarith

/-! ### The entropy increase for a high-entropy piece -/

/-- Rapaport's (4.13): for a piece `ζ` of large entropy, carried by `σ^{-n}[u]` and by words of
comparable derivatives, the entropy increase theorem gives
`H((Π_{n+n'} ζ).μ, 𝒟_{ℓ+L}) ≥ (d + ρ) ℓ log 2 - log 8 - log (2A + 2)`. -/
theorem ent_wordAct_ge_of_highPiece [NeZero N] (hφ : RapaportHyp φ) {p : Fin N → ℝ}
    (hp : AnalyticESC.IsProbVec p) {C : ℝ} (hC1 : 1 ≤ C) (hCd : distConst φ ≤ C)
    (hHD : ∀ (u : List (Fin N)) (l : ℕ), 1 ≤ l → ∀ x ∈ I,
      |iteratedDeriv l (realComp φ u) x| ≤ l.factorial * C ^ l * |deriv (realComp φ u) 0|)
    {n n' k ℓ L : ℕ} (hk : 1 ≤ k) (hℓ : 0 < ℓ) {ε d ρ A : ℝ}
    (hEI : ∀ ν : Measure (Poly k), IsProbabilityMeasure ν →
      (∀ᵐ q ∂ν, ‖q‖ ≤ ε⁻¹ ∧ ∀ x ∈ I, ε ≤ |Poly.derivEval q x|) →
      ε ≤ dyadicEntropyVec ν ℓ / ℓ →
      ∀ ψ : ℝ → ℝ, Set.MapsTo ψ I I → (∀ x ∈ I, HasDerivWithinAt ψ (deriv ψ x) I x) →
        (∀ x ∈ I, ε ≤ |deriv ψ x| ∧ |deriv ψ x| ≤ ε⁻¹) →
        d + ρ ≤ dyadicEntropy (act ν ((selfConformal φ p hp).map ψ)) ℓ / ℓ)
    (hε0 : 0 < ε) (hεnorm : ε * ((k + 1) * (2 * C ^ (k + 3))) ≤ 1) (hεder : ε ≤ (4 * C)⁻¹)
    (hεψ : ε * C ^ 2 ≤ 1)
    (u : Fin n' → Fin N) (ζ : Measure (ℕ → Fin N)) [IsProbabilityMeasure ζ]
    (hζu : ζ (shift^[n] ⁻¹' cylinder u)ᶜ = 0)
    (hshell : ∀ v₁ v₂ : Fin n → Fin N, ζ (cylinder v₁) ≠ 0 → ζ (cylinder v₂) ≠ 0 →
      |deriv (wordMap φ v₁) 0| ≤ 2 * |deriv (wordMap φ v₂) 0|)
    (hent : ε * ℓ * Real.log 2 ≤ ent ζ (pre n))
    (x : ℝ) (hx : ∀ v : Fin n → Fin N, ζ (cylinder v) ≠ 0 →
      x ∈ wordMap φ (Fin.append v u) '' I)
    (hrbig : 8 * k * (k + 1) * C ^ (k + 1) * (C * |deriv (wordMap φ u) 0|) ≤ 1)
    (htaylor : ∀ v : Fin n → Fin N, ζ (cylinder v) ≠ 0 →
      C ^ (k + 1) * |deriv (wordMap φ v) 0| * (C * |deriv (wordMap φ u) 0|) ^ (k + 1) ≤
        1 / 2 ^ (ℓ + L))
    (hsep : ∀ v₁ v₂ : Fin n → Fin N, v₁ ≠ v₂ → (k + 3) / 2 ^ ℓ <
      ⨆ y : I, |wordMap φ (Fin.append v₁ u) y - wordMap φ (Fin.append v₂ u) y|)
    (hA : ∀ v : Fin n → Fin N, ζ (cylinder v) ≠ 0 →
      C / (|deriv (wordMap φ v) 0| * |deriv (wordMap φ u) 0|) ≤ 2 ^ L * A) :
    (d + ρ) * ℓ * Real.log 2 - Real.log 8 - Real.log (2 * A + 2) ≤
      ent (wordAct φ (selfConformal φ p hp) ζ (n + n')) (cellIdx (ℓ + L)) := by
  classical
  set μ := selfConformal φ p hp with hμ
  have hμI : μ Iᶜ = 0 := selfConformal_compl_I hφ hp
  have hC0 : 0 < C := zero_lt_one.trans_le hC1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- a word of positive mass
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : Fin n → Fin N, ζ (cylinder v₀) ≠ 0 := by
    by_contra h
    push Not at h
    have h1 := sum_measure_cylinder ζ n
    simp [h] at h1
  have hd0 : ∀ {m : ℕ} (w : Fin m → Fin N), 0 < |deriv (wordMap φ w) 0| := fun w =>
    abs_pos.2 (deriv_realComp_ne_zero hφ _ zero_mem_I)
  have hd1 : ∀ {m : ℕ} (w : Fin m → Fin N), |deriv (wordMap φ w) 0| ≤ 1 := fun w =>
    (abs_deriv_realComp_le_cmax_pow hφ _ zero_mem_I).trans
      (pow_le_one₀ cmax_nonneg (cmax_lt_one hφ).le)
  -- the normalisation
  obtain ⟨a, D, ha, hD0, hDlow, hDup, hD1, hJ⟩ := exists_normalisation hφ u hCd
  set r := D⁻¹ with hr_def
  set α := (|deriv (wordMap φ v₀) 0|)⁻¹ with hα_def
  have hr0 : 0 < r := inv_pos.2 hD0
  have hr1 : 1 ≤ r := one_le_inv₀ hD0 |>.2 hD1
  have hα0 : 0 < α := inv_pos.2 (hd0 v₀)
  have hα1 : 1 ≤ α := one_le_inv₀ (hd0 v₀) |>.2 (hd1 v₀)
  have hαr : 1 ≤ α * r := by nlinarith
  have hu0 := hd0 u
  have hru : r * |deriv (wordMap φ u) 0| ≤ C := by
    rw [hr_def, inv_mul_le_iff₀ hD0]
    calc |deriv (wordMap φ u) 0| = C * (C⁻¹ * |deriv (wordMap φ u) 0|) := by field_simp
      _ ≤ C * D := by gcongr
      _ = D * C := mul_comm _ _
  have hrlow : (C * |deriv (wordMap φ u) 0|)⁻¹ ≤ r := by
    rw [hr_def]
    exact inv_anti₀ hD0 hDup
  have hrbig' : 8 * k * (k + 1) * C ^ (k + 1) ≤ r := by
    refine le_trans ?_ hrlow
    rw [le_inv_comm₀ (by positivity) (by positivity), ← one_div, le_div_iff₀ (by positivity)]
    linarith [hrbig]
  have hαv : ∀ v : Fin n → Fin N, ζ (cylinder v) ≠ 0 →
      1 / 2 ≤ α * |deriv (wordMap φ v) 0| ∧ α * |deriv (wordMap φ v) 0| ≤ 2 := by
    intro v hv
    have h1 := hshell v₀ v hv₀ hv
    have h2 := hshell v v₀ hv hv₀
    have hv0 := hd0 v
    have hv00 := hd0 v₀
    rw [hα_def]
    constructor
    · rw [inv_mul_eq_div, le_div_iff₀ hv00]
      linarith
    · rw [inv_mul_eq_div, div_le_iff₀ hv00]
      linarith
  -- the Taylor remainder
  have hT : ∀ v : Fin n → Fin N, ζ (cylinder v) ≠ 0 → ∀ y ∈ I,
      |wordMap φ v (wordMap φ u y) - Poly.eval (Poly.taylor k a (wordMap φ v))
        (wordMap φ u y)| ≤ 1 / 2 ^ (ℓ + L) := by
    intro v hv y hy
    have haI : a ∈ I := by
      obtain ⟨y', hy', rfl⟩ := ha
      exact mapsTo_realComp hφ _ hy'
    have h1 := abs_sub_eval_taylor_le hφ hHD (List.ofFn v) k haI
      (mapsTo_realComp hφ (List.ofFn u) hy)
    rw [← wordMap_def] at h1
    have h2 : |wordMap φ u y - a| ≤ C * |deriv (wordMap φ u) 0| := by
      obtain ⟨hy1, hy2⟩ := hJ y hy
      rw [abs_of_nonneg (by linarith)]
      linarith
    refine h1.trans (le_trans ?_ (htaylor v hv))
    gcongr
    exact h2
  -- the polynomials and the measure on polynomials
  set q : (Fin n → Fin N) → Poly k := fun v => polyOf k α r a x (wordMap φ v) with hq_def
  set lam : Measure (Fin n → Fin N) := ζ.map (pre n) with hlam
  set ν : Measure (Poly k) := lam.map q with hν
  have hqm : Measurable q := measurable_of_countable q
  have hνprob : IsProbabilityMeasure ν := inferInstance
  have hνbd : ∀ᵐ q' ∂ν, ‖q'‖ ≤ ε⁻¹ ∧ ∀ z ∈ I, ε ≤ |Poly.derivEval q' z| := by
    refine ae_map_map_pre ζ n q fun v hv => ?_
    obtain ⟨hb1, hb2⟩ := polyOf_bounds hφ hC1 hCd hHD v u hk hα0 (hαv v hv).1 (hαv v hv).2
      hr1 hru hrbig' ha (hx v hv)
    refine ⟨hb1.trans ?_, fun z hz => hεder.trans (hb2 z hz)⟩
    rw [le_inv_comm₀ (by positivity) hε0, ← one_div, le_div_iff₀ (by positivity)]
    linarith
  have hinj := cellIdxVec_polyOf_injective (ℓ := ℓ) u ζ (x := x) hr0 hαr
    (fun y hy => ⟨(hJ y hy).1, by rw [hr_def, inv_inv]; exact (hJ y hy).2⟩)
    (fun v hv y hy => (hT v hv y hy).trans (by
      gcongr
      · norm_num
      · omega)) hsep
  have hentν : ε ≤ dyadicEntropyVec ν ℓ / ℓ := by
    have h1 := ent_pre_le_ent_map ζ n ℓ q hinj
    rw [dyadicEntropyVec_eq_ent, div_div, le_div_iff₀ (by positivity)]
    have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    nlinarith
  -- the map `ψ`
  set ψ : ℝ → ℝ := fun y => r * (wordMap φ u y - a) with hψ_def
  have hψd : ∀ y ∈ I, HasDerivAt ψ (r * deriv (wordMap φ u) y) y := fun y hy =>
    (((differentiableAt_realComp hφ _ hy).hasDerivAt).sub_const a).const_mul r
  have hψmaps : Set.MapsTo ψ I I := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hJ y hy
    constructor
    · exact mul_nonneg hr0.le (by linarith)
    · have : r * (wordMap φ u y - a) ≤ r * D := mul_le_mul_of_nonneg_left (by linarith) hr0.le
      rwa [hr_def, inv_mul_cancel₀ hD0.ne'] at this
  have hψder : ∀ y ∈ I, HasDerivWithinAt ψ (deriv ψ y) I y := fun y hy => by
    rw [(hψd y hy).deriv]
    exact (hψd y hy).hasDerivWithinAt
  have hψbd : ∀ y ∈ I, ε ≤ |deriv ψ y| ∧ |deriv ψ y| ≤ ε⁻¹ := by
    intro y hy
    rw [(hψd y hy).deriv, abs_mul, abs_of_pos hr0]
    have hdy1 := abs_deriv_realComp_le hφ (List.ofFn u) zero_mem_I hy
    have hdy2 := abs_deriv_realComp_le hφ (List.ofFn u) hy zero_mem_I
    rw [← wordMap_def] at hdy1 hdy2
    have hy0 : 0 < |deriv (wordMap φ u) y| := abs_pos.2 (deriv_realComp_ne_zero hφ _ hy)
    constructor
    · -- `r |φ_u'(y)| ≥ C^{-2}`
      have h1 : |deriv (wordMap φ u) 0| ≤ C * |deriv (wordMap φ u) y| :=
        hdy1.trans (mul_le_mul_of_nonneg_right hCd (abs_nonneg _))
      have h2 : (C * |deriv (wordMap φ u) 0|)⁻¹ * |deriv (wordMap φ u) y| ≤
          r * |deriv (wordMap φ u) y| := mul_le_mul_of_nonneg_right hrlow (abs_nonneg _)
      have h3 : (C ^ 2)⁻¹ ≤ (C * |deriv (wordMap φ u) 0|)⁻¹ * |deriv (wordMap φ u) y| := by
        rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
        calc (C ^ 2)⁻¹ * (C * |deriv (wordMap φ u) 0|) = C⁻¹ * |deriv (wordMap φ u) 0| := by
              field_simp
          _ ≤ C⁻¹ * (C * |deriv (wordMap φ u) y|) := by gcongr
          _ = |deriv (wordMap φ u) y| := by field_simp
      have h4 : ε ≤ (C ^ 2)⁻¹ := by
        rw [le_inv_comm₀ hε0 (by positivity), ← one_div, le_div_iff₀ hε0]
        linarith
      linarith
    · have h1 : |deriv (wordMap φ u) y| ≤ C * |deriv (wordMap φ u) 0| :=
        hdy2.trans (mul_le_mul_of_nonneg_right hCd (abs_nonneg _))
      have h2 : r * |deriv (wordMap φ u) y| ≤ C ^ 2 := by
        calc r * |deriv (wordMap φ u) y| ≤ r * (C * |deriv (wordMap φ u) 0|) := by gcongr
          _ = C * (r * |deriv (wordMap φ u) 0|) := by ring
          _ ≤ C * C := by gcongr
          _ = C ^ 2 := by ring
      have h3 : C ^ 2 ≤ ε⁻¹ := by
        rw [le_inv_comm₀ (by positivity) hε0, ← one_div, le_div_iff₀ (by positivity)]
        linarith
      linarith
  have hEI' := hEI ν hνprob hνbd hentν ψ hψmaps hψder hψbd
  have hEIent : (d + ρ) * ℓ * Real.log 2 ≤ ent (act ν (μ.map ψ)) (cellIdx ℓ) := by
    rw [dyadicEntropy_eq_ent, div_div, le_div_iff₀ (by positivity)] at hEI'
    linarith
  -- the product space
  set Ω : Measure ((Fin n → Fin N) × ℝ) := lam.prod μ with hΩ
  set F : (Fin n → Fin N) × ℝ → ℝ := fun z => wordMapExt φ (Fin.append z.1 u) z.2 with hF_def
  set G : (Fin n → Fin N) × ℝ → ℝ := fun z =>
    Poly.eval (Poly.taylor k a (wordMap φ z.1)) (wordMapExt φ u z.2) with hG_def
  set ψe : ℝ → ℝ := fun y => r * (wordMapExt φ u y - a) with hψe_def
  set H : (Fin n → Fin N) × ℝ → ℝ := fun z => Poly.eval (q z.1) (ψe z.2) with hH_def
  have hψem : Measurable ψe :=
    (continuous_const.mul ((continuous_wordMapExt hφ u).sub continuous_const)).measurable
  have hFm : Measurable F := measurable_from_prod_countable_right fun v =>
    (continuous_wordMapExt hφ (Fin.append v u)).measurable
  have hGm : Measurable G := measurable_from_prod_countable_right fun v =>
    ((Poly.continuous_eval (Poly.taylor k a (wordMap φ v))).comp
      (continuous_wordMapExt hφ u)).measurable
  have hHm : Measurable H := measurable_from_prod_countable_right fun v =>
    (Poly.continuous_eval (q v)).measurable.comp hψem
  -- the two measures as images of `Ω`
  have hW : wordAct φ μ ζ (n + n') = Ω.map F := by
    rw [hΩ, map_prod_eq_sum lam μ hFm, wordAct_append_eq_sum u ζ hζu]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hlam, map_pre_singleton, map_wordMap_eq_map_wordMapExt hφ hμI]
  have hAct : act ν (μ.map ψ) = Ω.map H := by
    have h1 : μ.map ψ = μ.map ψe := by
      refine Measure.map_congr ?_
      filter_upwards [mem_ae_iff.2 hμI] with y hy
      simp only [hψ_def, hψe_def, wordMapExt_eq hφ u hy]
    rw [h1, act, hν, Measure.map_prod_map lam μ hqm hψem,
      Measure.map_map (Poly.measurable_eval_uncurry) (hqm.prodMap hψem)]
    rfl
  -- the set of full measure
  set S : Set ((Fin n → Fin N) × ℝ) := {z | ζ (cylinder z.1) ≠ 0 ∧ z.2 ∈ I} with hS_def
  have hSm : MeasurableSet S :=
    (measurable_fst
      (MeasurableSet.of_discrete (s := {v : Fin n → Fin N | ζ (cylinder v) ≠ 0}))).inter
      (measurable_snd measurableSet_Icc)
  have hSc : Ω Sᶜ = 0 := by
    have hsub : Sᶜ ⊆ {v : Fin n → Fin N | ζ (cylinder v) = 0} ×ˢ univ ∪ univ ×ˢ Iᶜ := by
      intro z hz
      simp only [hS_def, mem_compl_iff, mem_ofPred_eq, not_and_or, not_not] at hz
      rcases hz with h | h
      · exact Or.inl ⟨h, mem_univ _⟩
      · exact Or.inr ⟨mem_univ _, h⟩
    refine measure_mono_null hsub (measure_union_null ?_ ?_)
    · rw [hΩ, Measure.prod_prod, hlam, Measure.map_apply (measurable_pre n)
        MeasurableSet.of_discrete]
      have : pre n ⁻¹' {v : Fin n → Fin N | ζ (cylinder v) = 0} =
          {η | ζ (cylinder (pre n η)) = 0} := rfl
      rw [this, compl_cylinder_null, zero_mul]
    · rw [hΩ, Measure.prod_prod, hμI, mul_zero]
  have hΩprob : IsProbabilityMeasure Ω := inferInstance
  have hcomp := ent_comparison (Ω := Ω) hFm hGm hHm hSm hSc (ℓ := ℓ) (L := L) (s := α * r)
    (x₀ := x) (by positivity)
    (fun z hz => by
      simp only [hH_def, hG_def, hψe_def, hq_def]
      rw [wordMapExt_eq hφ u hz.2, eval_polyOf α hr0.ne'])
    (fun z hz => by
      simp only [hF_def, hG_def]
      rw [wordMapExt_eq hφ _ hz.2, wordMapExt_eq hφ u hz.2, wordMap_append]
      exact hT z.1 hz.1 z.2 hz.2)
    (fun z hz => by
      simp only [hF_def]
      rw [wordMapExt_eq hφ _ hz.2]
      exact mapsTo_realComp hφ _ hz.2)
  rw [← ent_map hHm (measurable_cellIdx ℓ), ← hAct, ← ent_map hFm (measurable_cellIdx _),
    ← hW] at hcomp
  -- the scale factor
  have hs : α * r ≤ 2 ^ L * A := by
    refine le_trans ?_ (hA v₀ hv₀)
    have hDinv : D⁻¹ ≤ (C⁻¹ * |deriv (wordMap φ u) 0|)⁻¹ := inv_anti₀ (by positivity) hDlow
    calc α * r = (|deriv (wordMap φ v₀) 0|)⁻¹ * D⁻¹ := rfl
      _ ≤ (|deriv (wordMap φ v₀) 0|)⁻¹ * (C⁻¹ * |deriv (wordMap φ u) 0|)⁻¹ := by gcongr
      _ = C / (|deriv (wordMap φ v₀) 0| * |deriv (wordMap φ u) 0|) := by
          field_simp
  have hlogA : Real.log (2 * (α * r) / 2 ^ L + 2) ≤ Real.log (2 * A + 2) := by
    refine Real.log_le_log (by positivity) ?_
    have : 2 * (α * r) / 2 ^ L ≤ 2 * A := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  linarith

end FractalGeometry.Rapaport.Analytic.SectionFour
