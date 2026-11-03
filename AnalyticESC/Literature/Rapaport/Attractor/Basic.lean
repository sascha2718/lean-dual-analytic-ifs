module

public import AnalyticESC.Literature.SelfConformal.Toolkit

@[expose] public section

/-!
# Complements to the toolkit: compositions, sup norms and invariant sets

Facts about a system `φ : Fin M → ℝ → ℝ` satisfying `AnalyticESC.RapaportHyp φ` (A. Rapaport,
*Dimension of self-conformal measures associated to an exponentially separated analytic IFS on ℝ*,
arXiv:2412.16753v2) that the proof of Corollary 1.3 needs beyond the toolkit
`FractalGeometry.SelfConformal.Toolkit`.

Main declarations:

* `mapsTo_realComp_of_mapsTo`: compositions preserve every set preserved by the maps;
* `analyticOnNhd_realComp`: compositions are real analytic on a neighbourhood of `I`;
* `abs_sub_le_of_deriv_le`: a derivative bound on `I` gives a Lipschitz bound on `I`;
* `supDeriv`: the sup norm `‖φ_u'‖_I`, with `supDeriv_bounds`, `supDeriv_pos`,
  `abs_realComp_sub_le_supDeriv` and the bounded distortion estimate `abs_log_supDeriv_sub_le`;
* `coding_mem_of_mapsTo`: the coding map takes values in every closed nonempty `S ⊆ I` with
  `φ_i(S) ⊆ S`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Attractor.Basic`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Attractor

open Set Filter Topology MeasureTheory AnalyticESC FractalGeometry.SelfConformal

variable {M : ℕ} {φ : Fin M → ℝ → ℝ}

/-- If every map sends `S` into `S`, so does every composition. -/
theorem mapsTo_realComp_of_mapsTo {S : Set ℝ} (h : ∀ i, MapsTo (φ i) S S)
    (l : List (Fin M)) : MapsTo (realComp φ l) S S := by
  induction l with
  | nil => exact mapsTo_id _
  | cons i l ih => exact (h i).comp ih

/-- Each composition is real analytic on a neighbourhood of each point of `I`. -/
theorem analyticOnNhd_realComp (hφ : RapaportHyp φ) (l : List (Fin M)) :
    AnalyticOnNhd ℝ (realComp φ l) I := by
  induction l with
  | nil => exact analyticOnNhd_id
  | cons i l ih => exact (hφ.analytic i).comp ih (mapsTo_realComp hφ l)

/-- A derivative bound on `I` gives a Lipschitz bound on `I`. -/
theorem abs_sub_le_of_deriv_le {f : ℝ → ℝ} (hf : ∀ x ∈ I, DifferentiableAt ℝ f x) {c : ℝ}
    (hc : ∀ x ∈ I, |deriv f x| ≤ c) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    |f x - f y| ≤ c * |x - y| := by
  have h := convex_I.norm_image_sub_le_of_norm_deriv_le hf
    (fun z hz => by rw [Real.norm_eq_abs]; exact hc z hz) hy hx
  simpa only [Real.norm_eq_abs] using h

/-! ### The sup norm of the derivative -/

/-- The sup norm `‖φ_u'‖_I = sup_{x ∈ I} |φ_u'(x)|` of the derivative of `φ_u` on `I`. -/
noncomputable def supDeriv (φ : Fin M → ℝ → ℝ) (l : List (Fin M)) : ℝ :=
  ⨆ x : I, |deriv (realComp φ l) x|

/-- Bounds for the sup norm: `|φ_u'(x)| ≤ ‖φ_u'‖_I` on `I`, and
`c_min^{|u|} ≤ ‖φ_u'‖_I ≤ c_max^{|u|}`. -/
theorem supDeriv_bounds (hφ : RapaportHyp φ) (l : List (Fin M)) :
    (∀ x ∈ I, |deriv (realComp φ l) x| ≤ supDeriv φ l) ∧ cmin φ ^ l.length ≤ supDeriv φ l ∧
      supDeriv φ l ≤ cmax φ ^ l.length :=
  ⟨fun _ hx => abs_deriv_realComp_le_iSup hφ l hx,
    (cmin_pow_le_abs_deriv_realComp hφ l zero_mem_I).trans
      (abs_deriv_realComp_le_iSup hφ l zero_mem_I),
    ciSup_le fun x => abs_deriv_realComp_le_cmax_pow hφ l x.2⟩

/-- `0 < ‖φ_u'‖_I`. -/
theorem supDeriv_pos (hφ : RapaportHyp φ) (l : List (Fin M)) : 0 < supDeriv φ l :=
  (abs_pos.2 (deriv_realComp_ne_zero hφ l zero_mem_I)).trans_le
    ((supDeriv_bounds hφ l).1 0 zero_mem_I)

/-- `φ_u` is `‖φ_u'‖_I`-Lipschitz on `I`. -/
theorem abs_realComp_sub_le_supDeriv (hφ : RapaportHyp φ) (l : List (Fin M)) {x y : ℝ}
    (hx : x ∈ I) (hy : y ∈ I) :
    |realComp φ l x - realComp φ l y| ≤ supDeriv φ l * |x - y| :=
  abs_sub_le_of_deriv_le (fun _ hz => differentiableAt_realComp hφ l hz)
    (supDeriv_bounds hφ l).1 hx hy

/-- Bounded distortion for the sup norm: `|log ‖φ_u'‖_I - log |φ_u'(y)|| ≤ log C` for `y ∈ I`,
where `C = distConst φ`. -/
theorem abs_log_supDeriv_sub_le (hφ : RapaportHyp φ) (l : List (Fin M)) {y : ℝ} (hy : y ∈ I) :
    |Real.log (supDeriv φ l) - Real.log (|deriv (realComp φ l) y|)| ≤ Real.log (distConst φ) := by
  have hpos : 0 < |deriv (realComp φ l) y| := abs_pos.2 (deriv_realComp_ne_zero hφ l hy)
  have h1 : Real.log |deriv (realComp φ l) y| ≤ Real.log (supDeriv φ l) :=
    Real.log_le_log hpos ((supDeriv_bounds hφ l).1 y hy)
  have h2 := Real.log_le_log (supDeriv_pos hφ l) (iSup_abs_deriv_realComp_le hφ l hy)
  rw [Real.log_mul distConst_pos.ne' hpos.ne'] at h2
  have h3 : 0 ≤ Real.log (distConst φ) := Real.log_nonneg (one_lt_distConst hφ).le
  have h2' : Real.log (supDeriv φ l) ≤ Real.log (distConst φ) + Real.log |deriv (realComp φ l) y| :=
    h2
  rw [abs_le]
  constructor <;> linarith

/-! ### Invariant sets -/

/-- The coding map takes values in every closed nonempty set `S ⊆ I` with `φ_i(S) ⊆ S`. -/
theorem coding_mem_of_mapsTo (hφ : RapaportHyp φ) {S : Set ℝ} (hS : IsClosed S)
    (hne : S.Nonempty) (hSI : S ⊆ I) (hinv : ∀ i, MapsTo (φ i) S S) (ω : ℕ → Fin M) :
    coding φ ω ∈ S := by
  obtain ⟨x₀, hx₀⟩ := hne
  exact hS.mem_of_tendsto (tendsto_realComp_word hφ ω (hSI hx₀))
    (Eventually.of_forall fun _ => mapsTo_realComp_of_mapsTo hinv _ hx₀)

end FractalGeometry.Rapaport.Attractor
