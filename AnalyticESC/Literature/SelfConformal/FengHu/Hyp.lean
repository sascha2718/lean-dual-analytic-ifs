module

public import AnalyticESC.Literature.SelfConformal.Coding

@[expose] public section

/-!
# `C^{1+Lip}` conformal systems on the unit interval

The hypotheses under which this directory proves the Feng–Hu theorem (D.-J. Feng and H. Hu,
*Dimension theory of iterated function systems*, Comm. Pure Appl. Math. 62 (2009), Theorem 2.8,
for conformal systems on the line): each map sends `I = [0, 1]` into itself, is differentiable on
`I` with continuous nonvanishing derivative `|φ_i'| ≤ c < 1`, and `log |φ_i'|` is `L`-Lipschitz on
`I`. No separation condition and no condition on fixed points is assumed. The hypotheses of
Rapaport (arXiv:2412.16753v2, Theorem 1.2), `AnalyticESC.RapaportHyp`, imply them
(`exists_conformalIFS_of_rapaportHyp`).

The coding facts `ConformalIFS.coding_mem` and `ConformalIFS.coding_eq` are the statements
`coding_mem` and `coding_eq` of the toolkit file `FractalGeometry/SelfConformal/Coding.lean`,
restated (with the same proofs) under these weaker hypotheses.

## Main declarations

* `ConformalIFS φ c L`: the hypotheses.
* `exists_conformalIFS_of_rapaportHyp`: Rapaport's hypotheses imply them.
* `ConformalIFS.coding_mem`, `ConformalIFS.coding_eq`: `Π(ω) ∈ I` and `Π(ω) = φ_{ω_0}(Π(σ ω))`.
* `ConformalIFS.abs_deriv_le_mul_exp`, `ConformalIFS.mul_exp_le_abs_deriv`: distortion on `I`.
* `ConformalIFS.abs_sub_le_of_abs_map_sub_le`, `ConformalIFS.abs_map_sub_le_of`: the one-step
  ball inclusions `φ_i⁻¹(B(φ_i y, t)) ∩ I ⊆ B(y, ρ)` and `φ_i(B(y, ρ) ∩ I) ⊆ B(φ_i y, s ρ)`.
* `ConformalIFS.injOn`: each map is injective on `I`.

Copied from the library `FractalGeometry` (module `FractalGeometry.SelfConformal.FengHu.Hyp`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.SelfConformal.FengHu

open MeasureTheory Set Filter Topology
open AnalyticESC (I realComp)

variable {N : ℕ}

/-- A `C^{1+Lip}` conformal system on `I = [0, 1]` with contraction bound `c` and Lipschitz
constant `L` for `log |φ_i'|`. -/
structure ConformalIFS (φ : Fin N → ℝ → ℝ) (c L : ℝ) : Prop where
  mapsTo : ∀ i, MapsTo (φ i) I I
  differentiableAt : ∀ i, ∀ x ∈ I, DifferentiableAt ℝ (φ i) x
  continuousOn_deriv : ∀ i, ContinuousOn (deriv (φ i)) I
  deriv_ne_zero : ∀ i, ∀ x ∈ I, deriv (φ i) x ≠ 0
  abs_deriv_le : ∀ i, ∀ x ∈ I, |deriv (φ i) x| ≤ c
  c_nonneg : 0 ≤ c
  c_lt_one : c < 1
  L_nonneg : 0 ≤ L
  abs_log_deriv_sub_le : ∀ i, ∀ x ∈ I, ∀ y ∈ I,
    abs (Real.log |deriv (φ i) x| - Real.log |deriv (φ i) y|) ≤ L * |x - y|

/-! ### Rapaport's hypotheses imply the conformal hypotheses -/

/-- `|log a - log b| ≤ |a - b| / m` for `a, b ≥ m > 0`. -/
theorem abs_log_sub_log_le {a b m : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / m := by
  have key : ∀ x y : ℝ, m ≤ x → m ≤ y → y ≤ x → Real.log x - Real.log y ≤ (x - y) / m := by
    intro x y hx hy hxy
    have hy0 : 0 < y := hm.trans_le hy
    rw [← Real.log_div (hm.trans_le hx).ne' hy0.ne']
    calc Real.log (x / y) ≤ x / y - 1 :=
          Real.log_le_sub_one_of_pos (div_pos (hm.trans_le hx) hy0)
      _ = (x - y) / y := by field_simp
      _ ≤ (x - y) / m := div_le_div_of_nonneg_left (by linarith) hm hy
  rcases le_total b a with hab | hab
  · rw [abs_of_nonneg (by linarith [Real.log_le_log (hm.trans_le hb) hab]),
      abs_of_nonneg (by linarith)]
    exact key a b ha hb hab
  · rw [abs_of_nonpos (by linarith [Real.log_le_log (hm.trans_le ha) hab]),
      abs_of_nonpos (by linarith), neg_sub, neg_sub]
    exact key b a hb ha hab

/-- Rapaport's hypotheses imply the `C^{1+Lip}` conformal hypotheses. -/
theorem exists_conformalIFS_of_rapaportHyp {φ : Fin N → ℝ → ℝ} (hφ : AnalyticESC.RapaportHyp φ) :
    ∃ c L, ConformalIFS φ c L := by
  have hI : IsCompact I := isCompact_Icc
  have hIne : I.Nonempty := ⟨0, zero_mem_I⟩
  have hd : ∀ i, ContinuousOn (deriv (φ i)) I := fun i => (hφ.analytic i).deriv.continuousOn
  have hd2 : ∀ i, ContinuousOn (deriv (deriv (φ i))) I :=
    fun i => (hφ.analytic i).deriv.deriv.continuousOn
  -- the contraction constant
  have hc : ∃ c, 0 ≤ c ∧ c < 1 ∧ ∀ i, ∀ x ∈ I, |deriv (φ i) x| ≤ c := by
    have hmax : ∀ i, ∃ x ∈ I, ∀ y ∈ I, |deriv (φ i) y| ≤ |deriv (φ i) x| := fun i => by
      obtain ⟨x, hx, h⟩ := hI.exists_isMaxOn hIne (hd i).abs
      exact ⟨x, hx, fun y hy => isMaxOn_iff.1 h y hy⟩
    choose x hx hxmax using hmax
    rcases isEmpty_or_nonempty (Fin N) with hN | hN
    · exact ⟨0, le_rfl, zero_lt_one, fun i => isEmptyElim i⟩
    · obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => |deriv (φ i) (x i)|
      exact ⟨|deriv (φ i₀) (x i₀)|, abs_nonneg _, hφ.deriv_lt_one i₀ _ (hx i₀),
        fun i y hy => (hxmax i y hy).trans (hi₀ i)⟩
  -- the Lipschitz constant of `log |φ_i'|`
  have hL : ∃ L, 0 ≤ L ∧ ∀ i, ∀ x ∈ I, ∀ y ∈ I,
      abs (Real.log |deriv (φ i) x| - Real.log |deriv (φ i) y|) ≤ L * |x - y| := by
    have hloc : ∀ i, ∃ Li, 0 ≤ Li ∧ ∀ x ∈ I, ∀ y ∈ I,
        abs (Real.log |deriv (φ i) x| - Real.log |deriv (φ i) y|) ≤ Li * |x - y| := by
      intro i
      obtain ⟨x₁, hx₁, hmin⟩ := hI.exists_isMinOn hIne (hd i).abs
      obtain ⟨x₂, hx₂, hmax⟩ := hI.exists_isMaxOn hIne (hd2 i).abs
      set m := |deriv (φ i) x₁| with hm
      set M := |deriv (deriv (φ i)) x₂| with hM
      have hm0 : 0 < m := hφ.deriv_pos i x₁ hx₁
      refine ⟨M / m, div_nonneg (abs_nonneg _) hm0.le, fun x hx y hy => ?_⟩
      have hlip : |deriv (φ i) x - deriv (φ i) y| ≤ M * |x - y| := by
        have := convex_I.norm_image_sub_le_of_norm_deriv_le (f := deriv (φ i))
          (fun z hz => ((hφ.analytic i).deriv z hz).differentiableAt)
          (fun z hz => by
            rw [Real.norm_eq_abs]
            exact isMaxOn_iff.1 hmax z hz) hy hx
        simpa [Real.norm_eq_abs] using this
      calc abs (Real.log |deriv (φ i) x| - Real.log |deriv (φ i) y|)
          ≤ abs (|deriv (φ i) x| - |deriv (φ i) y|) / m :=
            abs_log_sub_log_le hm0 (isMinOn_iff.1 hmin x hx) (isMinOn_iff.1 hmin y hy)
        _ ≤ |deriv (φ i) x - deriv (φ i) y| / m :=
            div_le_div_of_nonneg_right (abs_abs_sub_abs_le_abs_sub _ _) hm0.le
        _ ≤ M * |x - y| / m := by gcongr
        _ = M / m * |x - y| := by ring
    choose Li hLi0 hLi using hloc
    obtain ⟨L, hL⟩ := (Set.finite_range Li).bddAbove
    refine ⟨max L 0, le_max_right _ _, fun i x hx y hy => (hLi i x hx y hy).trans ?_⟩
    gcongr
    exact (hL (Set.mem_range_self i)).trans (le_max_left _ _)
  obtain ⟨c, hc0, hc1, hc⟩ := hc
  obtain ⟨L, hL0, hL⟩ := hL
  exact ⟨c, L, fun i => hφ.mapsTo i, fun i x hx => (hφ.analytic i x hx).differentiableAt, hd,
    fun i x hx => abs_pos.1 (hφ.deriv_pos i x hx), hc, hc0, hc1, hL0, hL⟩

namespace ConformalIFS

variable {φ : Fin N → ℝ → ℝ} {c L : ℝ}

/-! ### Basic consequences -/

/-- Each map is continuous on `I`. -/
theorem continuousOn (hφ : ConformalIFS φ c L) (i : Fin N) : ContinuousOn (φ i) I :=
  fun x hx => (hφ.differentiableAt i x hx).continuousAt.continuousWithinAt

/-- `|φ_i'| > 0` on `I`. -/
theorem abs_deriv_pos (hφ : ConformalIFS φ c L) (i : Fin N) {x : ℝ} (hx : x ∈ I) :
    0 < |deriv (φ i) x| :=
  abs_pos.2 (hφ.deriv_ne_zero i x hx)

/-- Each map is `c`-Lipschitz on `I`. -/
theorem abs_map_sub_le (hφ : ConformalIFS φ c L) (i : Fin N) {x y : ℝ} (hx : x ∈ I)
    (hy : y ∈ I) : |φ i x - φ i y| ≤ c * |x - y| := by
  have h := convex_I.norm_image_sub_le_of_norm_deriv_le (f := φ i)
    (fun z hz => hφ.differentiableAt i z hz)
    (fun z hz => by rw [Real.norm_eq_abs]; exact hφ.abs_deriv_le i z hz) hy hx
  simpa [Real.norm_eq_abs] using h

/-- Distortion of `|φ_i'|` on `I`: `|φ_i'(w)| ≤ |φ_i'(y)| e^{L |w - y|}`. -/
theorem abs_deriv_le_mul_exp (hφ : ConformalIFS φ c L) (i : Fin N) {w y : ℝ} (hw : w ∈ I)
    (hy : y ∈ I) : |deriv (φ i) w| ≤ |deriv (φ i) y| * Real.exp (L * |w - y|) := by
  have h := (abs_le.1 (hφ.abs_log_deriv_sub_le i w hw y hy)).2
  calc |deriv (φ i) w| = Real.exp (Real.log |deriv (φ i) w|) :=
        (Real.exp_log (hφ.abs_deriv_pos i hw)).symm
    _ ≤ Real.exp (Real.log |deriv (φ i) y| + L * |w - y|) := Real.exp_le_exp.2 (by linarith)
    _ = |deriv (φ i) y| * Real.exp (L * |w - y|) := by
        rw [Real.exp_add, Real.exp_log (hφ.abs_deriv_pos i hy)]

/-- Distortion of `|φ_i'|` on `I`: `|φ_i'(y)| e^{-L |w - y|} ≤ |φ_i'(w)|`. -/
theorem mul_exp_le_abs_deriv (hφ : ConformalIFS φ c L) (i : Fin N) {w y : ℝ} (hw : w ∈ I)
    (hy : y ∈ I) : |deriv (φ i) y| * Real.exp (-(L * |w - y|)) ≤ |deriv (φ i) w| := by
  have h := (abs_le.1 (hφ.abs_log_deriv_sub_le i w hw y hy)).1
  calc |deriv (φ i) y| * Real.exp (-(L * |w - y|))
      = Real.exp (Real.log |deriv (φ i) y| - L * |w - y|) := by
        rw [Real.exp_sub, Real.exp_neg, Real.exp_log (hφ.abs_deriv_pos i hy), div_eq_mul_inv]
    _ ≤ Real.exp (Real.log |deriv (φ i) w|) := Real.exp_le_exp.2 (by linarith)
    _ = |deriv (φ i) w| := Real.exp_log (hφ.abs_deriv_pos i hw)

/-- The derivative of each map has a constant sign on `I`. -/
theorem deriv_pos_or_neg (hφ : ConformalIFS φ c L) (i : Fin N) :
    (∀ x ∈ I, 0 < deriv (φ i) x) ∨ (∀ x ∈ I, deriv (φ i) x < 0) := by
  by_contra h
  push Not at h
  obtain ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩ := h
  have hab := hφ.deriv_ne_zero i a ha
  have hbb := hφ.deriv_ne_zero i b hb
  have ha0 : deriv (φ i) a < 0 := lt_of_le_of_ne ha' hab
  have hb0 : 0 < deriv (φ i) b := lt_of_le_of_ne hb' (Ne.symm hbb)
  obtain ⟨z, hz, hz0⟩ := isPreconnected_Icc.intermediate_value ha hb (hφ.continuousOn_deriv i)
    ⟨ha0.le, hb0.le⟩
  exact hφ.deriv_ne_zero i z hz hz0

/-- Each map is strictly monotone or strictly antitone on `I`. -/
theorem strictMonoOn_or_strictAntiOn (hφ : ConformalIFS φ c L) (i : Fin N) :
    StrictMonoOn (φ i) I ∨ StrictAntiOn (φ i) I := by
  rcases hφ.deriv_pos_or_neg i with h | h
  · exact Or.inl (strictMonoOn_of_deriv_pos convex_I (hφ.continuousOn i)
      fun x hx => h x (interior_subset hx))
  · exact Or.inr (strictAntiOn_of_deriv_neg convex_I (hφ.continuousOn i)
      fun x hx => h x (interior_subset hx))

/-- Each map is injective on `I`. -/
theorem injOn (hφ : ConformalIFS φ c L) (i : Fin N) : InjOn (φ i) I := by
  rcases hφ.strictMonoOn_or_strictAntiOn i with h | h
  · exact h.injOn
  · exact h.injOn

/-! ### One-step ball inclusions -/

/-- Upper inclusion: if `|φ_i'| ≤ s` on `B(y, ρ) ∩ I`, then `φ_i` maps `B(y, ρ) ∩ I` into
`B(φ_i y, s ρ)`. -/
theorem abs_map_sub_le_of (hφ : ConformalIFS φ c L) (i : Fin N) {y z ρ s : ℝ} (hy : y ∈ I)
    (hz : z ∈ I) (hzy : |z - y| ≤ ρ)
    (hs : ∀ w ∈ I, |w - y| ≤ ρ → |deriv (φ i) w| ≤ s) : |φ i z - φ i y| ≤ s * ρ := by
  have hD : Convex ℝ (I ∩ Metric.closedBall y ρ) := convex_I.inter (convex_closedBall y ρ)
  have h := hD.norm_image_sub_le_of_norm_deriv_le (f := φ i)
    (fun w hw => hφ.differentiableAt i w hw.1)
    (fun w hw => by
      rw [Real.norm_eq_abs]
      exact hs w hw.1 (by simpa [Real.dist_eq] using hw.2))
    ⟨hy, Metric.mem_closedBall_self ((abs_nonneg _).trans hzy)⟩
    ⟨hz, by simpa [Real.dist_eq] using hzy⟩
  have hs0 : 0 ≤ s := (abs_nonneg _).trans (hs y hy (by simpa using (abs_nonneg _).trans hzy))
  simp only [Real.norm_eq_abs] at h
  exact h.trans (by gcongr)

/-- The lower inclusion for an increasing map with positive derivative. -/
private theorem abs_sub_le_of_pos {f : ℝ → ℝ} (hdiff : ∀ x ∈ I, DifferentiableAt ℝ f x)
    (hpos : ∀ x ∈ I, 0 < deriv f x) {y z ρ t : ℝ} (hy : y ∈ I) (hz : z ∈ I) (hρ : 0 < ρ)
    (ht : ∀ w ∈ I, |w - y| ≤ ρ → t ≤ |deriv f w| * ρ) (hfz : |f z - f y| ≤ t) :
    |z - y| ≤ ρ := by
  have hcont : ContinuousOn f I := fun x hx => (hdiff x hx).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn f I :=
    strictMonoOn_of_deriv_pos convex_I hcont fun x hx => hpos x (interior_subset hx)
  -- the slope over an interval of length `ρ` inside `I`
  have slope : ∀ a b, a ∈ I → b ∈ I → a < b → b - a = ρ → (a = y ∨ b = y) →
      t ≤ f b - f a := by
    intro a b ha hb hab hlen hend
    have hsub : Icc a b ⊆ I := Icc_subset_Icc ha.1 hb.2
    obtain ⟨ξ, hξ, hξ'⟩ := exists_deriv_eq_slope f hab (hcont.mono hsub)
      fun w hw => (hdiff w (hsub (Ioo_subset_Icc_self hw))).differentiableWithinAt
    have hξI : ξ ∈ I := hsub (Ioo_subset_Icc_self hξ)
    have hξy : |ξ - y| ≤ ρ := by
      rcases hend with rfl | rfl
      · rw [abs_of_pos (by linarith [hξ.1])]; linarith [hξ.2]
      · rw [abs_of_neg (by linarith [hξ.2])]; linarith [hξ.1]
    have h1 := ht ξ hξI hξy
    rw [abs_of_pos (hpos ξ hξI), hξ', hlen, div_mul_cancel₀ _ hρ.ne'] at h1
    exact h1
  have ht0 : 0 ≤ t := (abs_nonneg _).trans hfz
  by_contra hcon
  push Not at hcon
  rcases lt_or_gt_of_ne (show z - y ≠ 0 by intro h; rw [h, abs_zero] at hcon; linarith) with
    hneg | hpos'
  · -- `z < y - ρ`
    rw [abs_of_neg hneg] at hcon
    have hz' : y - ρ ∈ I := ⟨by linarith [hz.1], by linarith [hy.2]⟩
    have h1 := slope (y - ρ) y hz' hy (by linarith) (by ring) (Or.inr rfl)
    have h2 : f z < f (y - ρ) := hmono hz hz' (by linarith)
    rw [abs_of_neg (by linarith)] at hfz
    linarith
  · -- `z > y + ρ`
    rw [abs_of_pos hpos'] at hcon
    have hz' : y + ρ ∈ I := ⟨by linarith [hy.1], by linarith [hz.2]⟩
    have h1 := slope y (y + ρ) hy hz' (by linarith) (by ring) (Or.inl rfl)
    have h2 : f (y + ρ) < f z := hmono hz' hz (by linarith)
    rw [abs_of_pos (by linarith)] at hfz
    linarith

/-- Lower inclusion: if `t ≤ |φ_i'| ρ` on `B(y, ρ) ∩ I`, then `φ_i⁻¹(B(φ_i y, t)) ∩ I ⊆ B(y, ρ)`. -/
theorem abs_sub_le_of_abs_map_sub_le (hφ : ConformalIFS φ c L) (i : Fin N) {y z ρ t : ℝ}
    (hy : y ∈ I) (hz : z ∈ I) (hρ : 0 < ρ)
    (ht : ∀ w ∈ I, |w - y| ≤ ρ → t ≤ |deriv (φ i) w| * ρ) (hfz : |φ i z - φ i y| ≤ t) :
    |z - y| ≤ ρ := by
  rcases hφ.deriv_pos_or_neg i with h | h
  · exact abs_sub_le_of_pos (hφ.differentiableAt i) h hy hz hρ ht hfz
  · refine abs_sub_le_of_pos (f := -φ i) (fun x hx => (hφ.differentiableAt i x hx).neg)
      (fun x hx => by rw [deriv.neg]; linarith [h x hx]) hy hz hρ
      (fun w hw hwy => by rw [deriv.neg, abs_neg]; exact ht w hw hwy) ?_
    rw [Pi.neg_apply, Pi.neg_apply, neg_sub_neg, abs_sub_comm]
    exact hfz

/-! ### Compositions, words and the coding map -/

/-- Each composition `φ_u` maps `I` into `I`. -/
theorem mapsTo_realComp (hφ : ConformalIFS φ c L) (u : List (Fin N)) :
    MapsTo (realComp φ u) I I := by
  induction u with
  | nil => exact mapsTo_id _
  | cons i u ih => exact (hφ.mapsTo i).comp ih

end ConformalIFS

/-- `φ_{ω|_{n+1}} = φ_{ω_0} ∘ φ_{(σ ω)|_n}`. -/
theorem realComp_word_succ (φ : Fin N → ℝ → ℝ) (ω : ℕ → Fin N) (n : ℕ) (x : ℝ) :
    realComp φ (word ω (n + 1)) x =
      φ (ω 0) (realComp φ (word (shift ω) n) x) := by
  rw [word_succ]
  rfl

namespace ConformalIFS

variable {φ : Fin N → ℝ → ℝ} {c L : ℝ}

/-- `|φ_{ω|_{n+1}}(0) - φ_{ω|_n}(0)| ≤ c^n`. -/
theorem abs_realComp_word_succ_sub_le (hφ : ConformalIFS φ c L) (ω : ℕ → Fin N) (n : ℕ) :
    |realComp φ (word ω (n + 1)) 0 - realComp φ (word ω n) 0| ≤ c ^ n := by
  induction n generalizing ω with
  | zero =>
    simp only [pow_zero]
    exact abs_sub_le_one_of_mem_I (hφ.mapsTo_realComp _ zero_mem_I) zero_mem_I
  | succ n ih =>
    rw [realComp_word_succ φ ω (n + 1), realComp_word_succ φ ω n]
    calc _ ≤ c * |realComp φ (word (shift ω) (n + 1)) 0 -
          realComp φ (word (shift ω) n) 0| :=
          hφ.abs_map_sub_le _ (hφ.mapsTo_realComp _ zero_mem_I) (hφ.mapsTo_realComp _ zero_mem_I)
      _ ≤ c * c ^ n := by gcongr; exacts [hφ.c_nonneg, ih _]
      _ = c ^ (n + 1) := by ring

/-- The coding map is well defined: `φ_{ω|_n}(0) → Π(ω)`. -/
theorem tendsto_coding (hφ : ConformalIFS φ c L) (ω : ℕ → Fin N) :
    Tendsto (fun n => realComp φ (word ω n) 0) atTop (𝓝 (coding φ ω)) := by
  have h : CauchySeq fun n => realComp φ (word ω n) 0 :=
    cauchySeq_of_le_geometric c 1 hφ.c_lt_one fun n => by
      rw [Real.dist_eq, abs_sub_comm, one_mul]
      exact hφ.abs_realComp_word_succ_sub_le ω n
  exact h.tendsto_limUnder

/-- `Π(ω) ∈ I`. -/
theorem coding_mem (hφ : ConformalIFS φ c L) (ω : ℕ → Fin N) : coding φ ω ∈ I :=
  isClosed_Icc.mem_of_tendsto (hφ.tendsto_coding ω)
    (Eventually.of_forall fun _ => hφ.mapsTo_realComp _ zero_mem_I)

/-- `Π(ω) = φ_{ω_0}(Π(σ ω))`. -/
theorem coding_eq (hφ : ConformalIFS φ c L) (ω : ℕ → Fin N) :
    coding φ ω = φ (ω 0) (coding φ (shift ω)) := by
  have h1 : Tendsto (fun n => realComp φ (word ω (n + 1)) 0) atTop (𝓝 (coding φ ω)) :=
    (hφ.tendsto_coding ω).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => realComp φ (word ω (n + 1)) 0) atTop
      (𝓝 (φ (ω 0) (coding φ (shift ω)))) := by
    simp_rw [realComp_word_succ]
    have ht : Tendsto (fun n => realComp φ (word (shift ω) n) 0) atTop
        (𝓝[I] (coding φ (shift ω))) :=
      tendsto_nhdsWithin_iff.2 ⟨hφ.tendsto_coding _,
        Eventually.of_forall fun _ => hφ.mapsTo_realComp _ zero_mem_I⟩
    exact ((hφ.continuousOn _) _ (hφ.coding_mem _)).tendsto.comp ht
  exact tendsto_nhds_unique h1 h2

end ConformalIFS

end FractalGeometry.SelfConformal.FengHu
