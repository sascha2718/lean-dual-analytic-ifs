module

public import AnalyticESC.Dual.Projection
public import AnalyticESC.Analysis

@[expose] public section

/-!
# The linearisation of a single map

For a map `f` of the class with fixed point `p ∈ I`: the function `Ĥ_f` of (5.1), and the
linearising map `ĝ(z) = lim_{n → ∞} (f^n(z) - p)/f'(p)^n` of (5.2), which is holomorphic on `B_ε`,
satisfies `ĝ ∘ f = f'(p) ĝ` and `ĝ'' = Ĥ_f ĝ'`, and has positive derivative on `I`.

The paper defines `ĝ` by integrating `Ĥ_f` and derives (5.2); here `ĝ` is the limit (5.2). With
`λ = f'(p)`, the maps `ĝ_n(z) = (f^n(z) - p)/λ^n` have derivatives
`P_n(z) = (f^n)'(z)/λ^n = ∏_{k<n} f'(f^k(z))/λ`. The factors satisfy
`|f'(f^k(z))/λ - 1| ≤ A c_max^k` on `B_ε`, so the `P_n` are uniformly bounded, and `|P_{n+1} - P_n|`
and, by the mean value inequality, `|ĝ_{n+1} - ĝ_n|` decay geometrically. Hence `ĝ` and
`ĝ' = lim P_n` are sums of uniformly convergent series of holomorphic maps, and
`ĝ'' = lim P_n' = lim Ĥ_n P_n = Ĥ_f ĝ'`, where `Ĥ_n` is the partial sum of (5.1).
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-- The function `Ĥ_f(z) = ∑_{k ≥ 0} (f''/f')(f^k(z)) · (f^k)'(z)` of (5.1). -/
noncomputable def hatH (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' k, deriv (deriv f) (f^[k] z) / deriv f (f^[k] z) * deriv (f^[k]) z

/-- The linearising map `ĝ(z) = lim_{n → ∞} (f^n(z) - p)/f'(p)^n` of (5.2). -/
noncomputable def koenigs (f : ℂ → ℂ) (p : ℂ) (z : ℂ) : ℂ :=
  limUnder atTop fun n : ℕ => (f^[n] z - p) / deriv f p ^ n

/-! ## Auxiliary definitions -/

/-- The system consisting of the single map `f`. -/
private def koenigsIFS {ε : ℝ} {f : ℂ → ℂ} (hε : 0 < ε) (hf : InClass ε f) : IFS 1 ε :=
  ⟨fun _ => f, hε, fun _ => hf⟩

/-- The term `(f''/f')(f^k(z)) · (f^k)'(z)` of (5.1). -/
private noncomputable def hatHTerm (f : ℂ → ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  deriv (deriv f) (f^[k] z) / deriv f (f^[k] z) * deriv (f^[k]) z

/-- `ĝ_n(z) = (f^n(z) - p)/f'(p)^n`. -/
private noncomputable def gSeq (f : ℂ → ℂ) (p : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  (f^[n] z - p) / deriv f p ^ n

/-- `P_n(z) = (f^n)'(z)/f'(p)^n`, the derivative of `ĝ_n`. -/
private noncomputable def PSeq (f : ℂ → ℂ) (p : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  deriv (f^[n]) z / deriv f p ^ n

private theorem gSeq_zero (f : ℂ → ℂ) (q z : ℂ) : gSeq f q 0 z = z - q := by simp [gSeq]

private theorem PSeq_zero (f : ℂ → ℂ) (q z : ℂ) : PSeq f q 0 z = 1 := by simp [PSeq]

private theorem gSeq_fixed {f : ℂ → ℂ} {q : ℂ} (hfq : f q = q) (n : ℕ) : gSeq f q n q = 0 := by
  simp [gSeq, Function.iterate_fixed hfq n]

/-- `ĝ_n = ĝ_0 + ∑_{k<n} (ĝ_{k+1} - ĝ_k)`. -/
private theorem gSeq_eq_sum (f : ℂ → ℂ) (q : ℂ) (n : ℕ) (z : ℂ) :
    gSeq f q n z = z - q + ∑ k ∈ Finset.range n, (gSeq f q (k + 1) z - gSeq f q k z) := by
  rw [Finset.sum_range_sub (fun k => gSeq f q k z), gSeq_zero]
  ring

/-- `P_n = P_0 + ∑_{k<n} (P_{k+1} - P_k)`. -/
private theorem PSeq_eq_sum (f : ℂ → ℂ) (q : ℂ) (n : ℕ) (z : ℂ) :
    PSeq f q n z = 1 + ∑ k ∈ Finset.range n, (PSeq f q (k + 1) z - PSeq f q k z) := by
  rw [Finset.sum_range_sub (fun k => PSeq f q k z), PSeq_zero]
  ring

/-- A complex number with zero imaginary part is real. -/
private theorem eq_ofReal_re_of_im_eq_zero {w : ℂ} (h : w.im = 0) : w = (w.re : ℂ) :=
  Complex.ext (by simp) (by simp [h])

/-- A limit of products of positive factors `a_k` with `∑ |a_k - 1| < ∞` is positive. -/
private theorem pos_of_tendsto_prod {a : ℕ → ℝ} (ha : ∀ k, 0 < a k)
    (hs : Summable fun k => a k - 1) {r : ℝ}
    (hr : Tendsto (fun n => ∏ k ∈ Finset.range n, a k) atTop (𝓝 r)) : 0 < r := by
  have hlog : Summable fun k => Real.log (a k) := by
    simpa using Real.summable_log_one_add_of_summable hs
  have h1 : Tendsto (fun n => ∏ k ∈ Finset.range n, a k) atTop
      (𝓝 (Real.exp (∑' k, Real.log (a k)))) := by
    refine ((Real.continuous_exp.tendsto _).comp hlog.hasSum.tendsto_sum_nat).congr fun n => ?_
    simp [Function.comp, Real.exp_sum, Real.exp_log (ha _)]
  rw [tendsto_nhds_unique hr h1]
  exact Real.exp_pos _

section

variable {ε : ℝ} {f : ℂ → ℂ} (hε : 0 < ε) (hf : InClass ε f)

include hε hf

/-! ## Iterates of a single map -/

private theorem koenigsIFS_f (i : Fin 1) : (koenigsIFS hε hf).f i = f := rfl

private theorem koenigsIFS_comp (n : ℕ) : (koenigsIFS hε hf).comp (List.replicate n 0) = f^[n] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, IFS.comp_cons, ih, Function.iterate_succ', koenigsIFS_f]

private theorem mapsTo_iterate (n : ℕ) : MapsTo (f^[n]) (nbhd ε) (nbhd ε) := by
  rw [← koenigsIFS_comp hε hf]
  exact (koenigsIFS hε hf).mapsTo_comp _

private theorem mapsTo_iterate_closure (n : ℕ) :
    MapsTo (f^[n]) (closure (nbhd ε)) (closure (nbhd ε)) := by
  rw [← koenigsIFS_comp hε hf]
  exact (koenigsIFS hε hf).mapsTo_comp_closure _

private theorem differentiableAt_iterate (n : ℕ) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    DifferentiableAt ℂ (f^[n]) z := by
  rw [← koenigsIFS_comp hε hf]
  exact (koenigsIFS hε hf).differentiableAt_comp _ hz

private theorem differentiableOn_deriv_iterate (n : ℕ) :
    DifferentiableOn ℂ (deriv (f^[n])) (nbhd ε) := by
  obtain ⟨U, hUo, hU, hd⟩ := (koenigsIFS hε hf).exists_differentiableOn_comp (List.replicate n 0)
  rw [koenigsIFS_comp] at hd
  exact (hd.deriv hUo).mono (subset_closure.trans hU)

private theorem deriv_iterate_succ (n : ℕ) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    deriv (f^[n + 1]) z = deriv f (f^[n] z) * deriv (f^[n]) z := by
  have h := (koenigsIFS hε hf).deriv_comp_cons 0 (List.replicate n 0) hz
  rwa [← List.replicate_succ, koenigsIFS_comp, koenigsIFS_comp, koenigsIFS_f] at h

private theorem norm_iterate_sub_le (n : ℕ) {z w : ℂ} (hz : z ∈ nbhd ε) (hw : w ∈ nbhd ε) :
    ‖f^[n] z - f^[n] w‖ ≤ (koenigsIFS hε hf).cmax ^ n * ‖z - w‖ := by
  have h := (koenigsIFS hε hf).norm_comp_sub_le (List.replicate n 0) hz hw
  rwa [koenigsIFS_comp, List.length_replicate] at h

private theorem cmax_nonneg' : 0 ≤ (koenigsIFS hε hf).cmax := (koenigsIFS hε hf).cmax_nonneg

private theorem cmax_lt_one' : (koenigsIFS hε hf).cmax < 1 := (koenigsIFS hε hf).cmax_lt_one

private theorem summable_geometric_cmax (C : ℝ) :
    Summable fun n : ℕ => C * (koenigsIFS hε hf).cmax ^ n :=
  (summable_geometric_of_lt_one (cmax_nonneg' hε hf) (cmax_lt_one' hε hf)).mul_left C

omit hε in
/-- `f'` is holomorphic on `B_{2ε}`. -/
private theorem differentiableAt_deriv {z : ℂ} (hz : z ∈ nbhd (2 * ε)) :
    DifferentiableAt ℂ (deriv f) z :=
  (hf.differentiableOn.deriv (isOpen_nbhd _) z hz).differentiableAt ((isOpen_nbhd _).mem_nhds hz)

omit hε in
/-- A bound for `f''` on `B_ε`. -/
private theorem exists_norm_deriv_deriv_le :
    ∃ L, 0 ≤ L ∧ ∀ z ∈ nbhd ε, ‖deriv (deriv f) z‖ ≤ L := by
  have hc : ContinuousOn (deriv (deriv f)) (nbhd (2 * ε)) :=
    ((hf.differentiableOn.deriv (isOpen_nbhd _)).deriv (isOpen_nbhd _)).continuousOn
  obtain ⟨C, hC⟩ := (isCompact_closure_nbhd ε).exists_bound_of_continuousOn
    (hc.mono IFS.closure_nbhd_subset_two)
  exact ⟨max C 0, le_max_right _ _, fun z hz => (hC z (subset_closure hz)).trans (le_max_left _ _)⟩

/-! ## The function `Ĥ_f` -/

private theorem dualTerm_koenigsIFS (k : ℕ) (z : ℂ) :
    (koenigsIFS hε hf).dualTerm (.inf fun _ => 0) k z = hatHTerm f k z := by
  rw [(koenigsIFS hε hf).dualTerm_of_get?_eq_some (Word.get?_inf _ k)]
  simp only [Word.take_inf, List.ofFn_const, List.reverse_replicate, koenigsIFS_comp hε hf,
    IFS.nonlin, koenigsIFS_f, hatHTerm]

private theorem hatH_eq_dualProj : hatH f = (koenigsIFS hε hf).dualProj (.inf fun _ => 0) := by
  funext z
  simp only [hatH, IFS.dualProj, dualTerm_koenigsIFS hε hf, hatHTerm]

private theorem summable_hatHTerm {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    Summable fun k => hatHTerm f k z := by
  have h := (koenigsIFS hε hf).summable_dualTerm (.inf fun _ => 0) hz
  simpa only [dualTerm_koenigsIFS hε hf] using h

/-- `(f^n)'' = Ĥ_n (f^n)'`, with `Ĥ_n` the partial sum of (5.1). -/
private theorem deriv_deriv_iterate (n : ℕ) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    deriv (deriv (f^[n])) z = (∑ k ∈ Finset.range n, hatHTerm f k z) * deriv (f^[n]) z := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := (koenigsIFS hε hf).deriv_deriv_comp_cons 0 (List.replicate n 0) hz
    rw [← List.replicate_succ, koenigsIFS_comp, koenigsIFS_comp, koenigsIFS_f] at h
    have hne : deriv f (f^[n] z) ≠ 0 := hf.deriv_ne_zero _ (mapsTo_iterate_closure hε hf n hz)
    rw [h, deriv_iterate_succ hε hf n hz, Finset.sum_range_succ, ih, hatHTerm]
    field_simp
    ring

theorem differentiableOn_hatH : DifferentiableOn ℂ (hatH f) (nbhd ε) := by
  rw [hatH_eq_dualProj hε hf]
  exact (koenigsIFS hε hf).differentiableOn_dualProj _

theorem im_hatH_ofReal {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) : (hatH f t).im = 0 := by
  rw [hatH_eq_dualProj hε hf]
  exact (koenigsIFS hε hf).im_dualProj_ofReal _ ht

/-! ## The approximants `ĝ_n` and their derivatives `P_n` -/

private theorem hasDerivAt_gSeq {q : ℂ} (n : ℕ) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    HasDerivAt (gSeq f q n) (PSeq f q n z) z :=
  ((differentiableAt_iterate hε hf n hz).hasDerivAt.sub_const q).div_const _

private theorem differentiableOn_PSeq {q : ℂ} (n : ℕ) :
    DifferentiableOn ℂ (PSeq f q n) (nbhd ε) :=
  (differentiableOn_deriv_iterate hε hf n).div_const _

/-- `P_n' = Ĥ_n P_n`, with `Ĥ_n` the partial sum of (5.1). -/
private theorem deriv_PSeq {q : ℂ} (n : ℕ) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    deriv (PSeq f q n) z = (∑ k ∈ Finset.range n, hatHTerm f k z) * PSeq f q n z := by
  change deriv (fun w => deriv (f^[n]) w / deriv f q ^ n) z = _
  rw [deriv_div_const, deriv_deriv_iterate hε hf n hz, PSeq, mul_div_assoc]

section Approximants

variable {q : ℂ} (hq : q ∈ nbhd ε) (hfq : f q = q)

include hq hfq

omit hε hfq in
private theorem deriv_ne_zero_fixed : deriv f q ≠ 0 := hf.deriv_ne_zero q (subset_closure hq)

omit hfq in
private theorem PSeq_succ (n : ℕ) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    PSeq f q (n + 1) z = PSeq f q n z * (deriv f (f^[n] z) / deriv f q) := by
  have hne := deriv_ne_zero_fixed hf hq
  rw [PSeq, PSeq, deriv_iterate_succ hε hf n hz, pow_succ]
  field_simp

omit hfq in
/-- `P_n(z) = ∏_{k<n} f'(f^k(z))/f'(p)`. -/
private theorem PSeq_eq_prod (n : ℕ) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    PSeq f q n z = ∏ k ∈ Finset.range n, deriv f (f^[k] z) / deriv f q := by
  induction n with
  | zero => simp [PSeq_zero]
  | succ n ih => rw [PSeq_succ hε hf hq n hz, ih, Finset.prod_range_succ]

/-- The factors of `P_n` satisfy `|f'(f^k(z))/f'(p) - 1| ≤ A c_max^k` on `B_ε`. -/
private theorem exists_norm_ratio_sub_one_le : ∃ A, 0 ≤ A ∧ ∀ k, ∀ z ∈ nbhd ε,
    ‖deriv f (f^[k] z) / deriv f q - 1‖ ≤ A * (koenigsIFS hε hf).cmax ^ k := by
  obtain ⟨L, hL0, hL⟩ := exists_norm_deriv_deriv_le hf
  obtain ⟨R, hR⟩ := (isBounded_nbhd ε).exists_norm_le
  have hne := deriv_ne_zero_fixed hf hq
  have hlam : 0 < ‖deriv f q‖ := norm_pos_iff.2 hne
  have hR0 : 0 ≤ R := (norm_nonneg q).trans (hR q hq)
  have hc0 := cmax_nonneg' hε hf
  set c := (koenigsIFS hε hf).cmax
  refine ⟨L * (R + R) / ‖deriv f q‖, by positivity, fun k z hz => ?_⟩
  have hw := mapsTo_iterate hε hf k hz
  -- the mean value inequality for `f'`
  have h1 : ‖deriv f (f^[k] z) - deriv f q‖ ≤ L * ‖f^[k] z - q‖ :=
    (convex_nbhd ε).norm_image_sub_le_of_norm_deriv_le
      (fun w hw => differentiableAt_deriv hf (IFS.nbhd_subset_two hw)) hL hq hw
  have h2 : ‖f^[k] z - q‖ ≤ c ^ k * (R + R) := by
    have h := norm_iterate_sub_le hε hf k hz hq
    rw [Function.iterate_fixed hfq k] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hc0 _))
    exact (norm_sub_le _ _).trans (add_le_add (hR z hz) (hR q hq))
  rw [div_sub_one hne, norm_div, div_le_iff₀ hlam]
  calc ‖deriv f (f^[k] z) - deriv f q‖ ≤ L * (c ^ k * (R + R)) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 hL0)
    _ = L * (R + R) / ‖deriv f q‖ * c ^ k * ‖deriv f q‖ := by field_simp

/-- The `P_n` are uniformly bounded on `B_ε`. -/
private theorem exists_norm_PSeq_le : ∃ B, 0 ≤ B ∧ ∀ n, ∀ z ∈ nbhd ε, ‖PSeq f q n z‖ ≤ B := by
  obtain ⟨A, hA0, hA⟩ := exists_norm_ratio_sub_one_le hε hf hq hfq
  have hc0 := cmax_nonneg' hε hf
  have hc1 := cmax_lt_one' hε hf
  set c := (koenigsIFS hε hf).cmax
  refine ⟨Real.exp (A / (1 - c)), (Real.exp_pos _).le, fun n z hz => ?_⟩
  rw [PSeq_eq_prod hε hf hq n (subset_closure hz)]
  set b : ℕ → ℂ := fun k => deriv f (f^[k] z) / deriv f q - 1 with hb
  have hprod : ∏ k ∈ Finset.range n, deriv f (f^[k] z) / deriv f q =
      ∏ k ∈ Finset.range n, (1 + b k) :=
    Finset.prod_congr rfl fun k _ => by simp [hb]
  have hsum : ∑ k ∈ Finset.range n, ‖b k‖ ≤ A / (1 - c) := by
    calc ∑ k ∈ Finset.range n, ‖b k‖ ≤ ∑ k ∈ Finset.range n, A * c ^ k :=
          Finset.sum_le_sum fun k _ => hA k z hz
      _ = A * ∑ k ∈ Finset.Ico 0 n, c ^ k := by rw [Finset.mul_sum, Finset.range_eq_Ico]
      _ ≤ A * (c ^ 0 / (1 - c)) :=
          mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hc0 hc1) hA0
      _ = A / (1 - c) := by rw [pow_zero]; ring
  rw [hprod]
  calc ‖∏ k ∈ Finset.range n, (1 + b k)‖
      ≤ ‖∏ k ∈ Finset.range n, (1 + b k) - 1‖ + ‖(1 : ℂ)‖ := norm_le_norm_sub_add _ _
    _ ≤ (Real.exp (∑ k ∈ Finset.range n, ‖b k‖) - 1) + 1 := by
        rw [norm_one]
        gcongr
        exact Finset.norm_prod_one_add_sub_one_le _ _
    _ = Real.exp (∑ k ∈ Finset.range n, ‖b k‖) := by ring
    _ ≤ Real.exp (A / (1 - c)) := Real.exp_le_exp.2 hsum

/-- `|P_{n+1} - P_n| ≤ C c_max^n` on `B_ε`. -/
private theorem exists_norm_PSeq_sub_le : ∃ C, 0 ≤ C ∧ ∀ n, ∀ z ∈ nbhd ε,
    ‖PSeq f q (n + 1) z - PSeq f q n z‖ ≤ C * (koenigsIFS hε hf).cmax ^ n := by
  obtain ⟨A, hA0, hA⟩ := exists_norm_ratio_sub_one_le hε hf hq hfq
  obtain ⟨B, hB0, hB⟩ := exists_norm_PSeq_le hε hf hq hfq
  refine ⟨B * A, mul_nonneg hB0 hA0, fun n z hz => ?_⟩
  rw [PSeq_succ hε hf hq n (subset_closure hz), ← mul_sub_one, norm_mul, mul_assoc]
  exact mul_le_mul (hB n z hz) (hA n z hz) (norm_nonneg _) hB0

/-- `|ĝ_{n+1} - ĝ_n| ≤ C c_max^n` on `B_ε`, by the mean value inequality. -/
private theorem exists_norm_gSeq_sub_le : ∃ C, 0 ≤ C ∧ ∀ n, ∀ z ∈ nbhd ε,
    ‖gSeq f q (n + 1) z - gSeq f q n z‖ ≤ C * (koenigsIFS hε hf).cmax ^ n := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_PSeq_sub_le hε hf hq hfq
  obtain ⟨R, hR⟩ := (isBounded_nbhd ε).exists_norm_le
  have hR0 : 0 ≤ R := (norm_nonneg q).trans (hR q hq)
  have hc0 := cmax_nonneg' hε hf
  set c := (koenigsIFS hε hf).cmax
  refine ⟨C * (R + R), mul_nonneg hC0 (by linarith), fun n z hz => ?_⟩
  have hd : ∀ w ∈ nbhd ε, HasDerivAt (fun w => gSeq f q (n + 1) w - gSeq f q n w)
      (PSeq f q (n + 1) w - PSeq f q n w) w := fun w hw =>
    (hasDerivAt_gSeq hε hf (n + 1) (subset_closure hw)).sub
      (hasDerivAt_gSeq hε hf n (subset_closure hw))
  have h := (convex_nbhd ε).norm_image_sub_le_of_norm_deriv_le
    (fun w hw => (hd w hw).differentiableAt)
    (fun w hw => by rw [(hd w hw).deriv]; exact hC n w hw) hq hz
  simp only [gSeq_fixed hfq, sub_zero] at h
  calc _ ≤ C * c ^ n * ‖z - q‖ := h
    _ ≤ C * c ^ n * (R + R) := mul_le_mul_of_nonneg_left
        ((norm_sub_le _ _).trans (add_le_add (hR z hz) (hR q hq))) (by positivity)
    _ = C * (R + R) * c ^ n := by ring

/-! ## Convergence -/

private theorem tendsto_gSeq {z : ℂ} (hz : z ∈ nbhd ε) :
    Tendsto (fun n => gSeq f q n z) atTop
      (𝓝 (z - q + ∑' k, (gSeq f q (k + 1) z - gSeq f q k z))) := by
  obtain ⟨C, -, hC⟩ := exists_norm_gSeq_sub_le hε hf hq hfq
  have hs : Summable fun k => gSeq f q (k + 1) z - gSeq f q k z :=
    (summable_geometric_cmax hε hf C).of_norm_bounded fun k => hC k z hz
  exact (hs.hasSum.tendsto_sum_nat.const_add (z - q)).congr fun n => (gSeq_eq_sum f q n z).symm

/-- `ĝ = (z - p) + ∑_k (ĝ_{k+1} - ĝ_k)` on `B_ε`. -/
private theorem koenigs_eq_tsum {z : ℂ} (hz : z ∈ nbhd ε) :
    koenigs f q z = z - q + ∑' k, (gSeq f q (k + 1) z - gSeq f q k z) :=
  (tendsto_gSeq hε hf hq hfq hz).limUnder_eq

private theorem tendsto_koenigs {z : ℂ} (hz : z ∈ nbhd ε) :
    Tendsto (fun n => gSeq f q n z) atTop (𝓝 (koenigs f q z)) := by
  rw [koenigs_eq_tsum hε hf hq hfq hz]
  exact tendsto_gSeq hε hf hq hfq hz

omit hq hfq in
private theorem differentiableOn_gSeq_sub (k : ℕ) :
    DifferentiableOn ℂ (fun w => gSeq f q (k + 1) w - gSeq f q k w) (nbhd ε) := fun _ hw =>
  ((hasDerivAt_gSeq hε hf (k + 1) (subset_closure hw)).sub
    (hasDerivAt_gSeq hε hf k (subset_closure hw))).differentiableAt.differentiableWithinAt

private theorem differentiableOn_koenigs' : DifferentiableOn ℂ (koenigs f q) (nbhd ε) := by
  obtain ⟨C, -, hC⟩ := exists_norm_gSeq_sub_le hε hf hq hfq
  have h : DifferentiableOn ℂ
      (fun w => w - q + ∑' k, (gSeq f q (k + 1) w - gSeq f q k w)) (nbhd ε) :=
    (differentiableOn_id.sub_const q).add (Complex.differentiableOn_tsum_of_summable_norm
      (summable_geometric_cmax hε hf C) (differentiableOn_gSeq_sub hε hf) (isOpen_nbhd ε)
      fun k w hw => hC k w hw)
  exact h.congr fun w hw => koenigs_eq_tsum hε hf hq hfq hw

/-- `ĝ' = 1 + ∑_k (P_{k+1} - P_k)` on `B_ε`. -/
private theorem hasDerivAt_koenigs {z : ℂ} (hz : z ∈ nbhd ε) :
    HasDerivAt (koenigs f q) (1 + ∑' k, (PSeq f q (k + 1) z - PSeq f q k z)) z := by
  obtain ⟨C, -, hC⟩ := exists_norm_gSeq_sub_le hε hf hq hfq
  have ho := isOpen_nbhd ε
  have hSd : DifferentiableOn ℂ (fun w => ∑' k, (gSeq f q (k + 1) w - gSeq f q k w))
      (nbhd ε) :=
    Complex.differentiableOn_tsum_of_summable_norm (summable_geometric_cmax hε hf C)
      (differentiableOn_gSeq_sub hε hf) ho fun k w hw => hC k w hw
  have hsum := Complex.hasSum_deriv_of_summable_norm (summable_geometric_cmax hε hf C)
    (differentiableOn_gSeq_sub hε hf) ho (fun k w hw => hC k w hw) hz
  have hderiv : ∀ k, deriv (fun w => gSeq f q (k + 1) w - gSeq f q k w) z =
      PSeq f q (k + 1) z - PSeq f q k z := fun k =>
    ((hasDerivAt_gSeq hε hf (k + 1) (subset_closure hz)).sub
      (hasDerivAt_gSeq hε hf k (subset_closure hz))).deriv
  simp only [hderiv] at hsum
  rw [hsum.tsum_eq]
  have h1 : HasDerivAt (fun w => w - q + ∑' k, (gSeq f q (k + 1) w - gSeq f q k w))
      (1 + deriv (fun w => ∑' k, (gSeq f q (k + 1) w - gSeq f q k w)) z) z :=
    ((hasDerivAt_id z).sub_const q).add (hSd.differentiableAt (ho.mem_nhds hz)).hasDerivAt
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [ho.mem_nhds hz] with w hw using koenigs_eq_tsum hε hf hq hfq hw

private theorem deriv_koenigs_eq {z : ℂ} (hz : z ∈ nbhd ε) :
    deriv (koenigs f q) z = 1 + ∑' k, (PSeq f q (k + 1) z - PSeq f q k z) :=
  (hasDerivAt_koenigs hε hf hq hfq hz).deriv

private theorem tendsto_PSeq {z : ℂ} (hz : z ∈ nbhd ε) :
    Tendsto (fun n => PSeq f q n z) atTop (𝓝 (deriv (koenigs f q) z)) := by
  obtain ⟨C, -, hC⟩ := exists_norm_PSeq_sub_le hε hf hq hfq
  have hs : Summable fun k => PSeq f q (k + 1) z - PSeq f q k z :=
    (summable_geometric_cmax hε hf C).of_norm_bounded fun k => hC k z hz
  rw [deriv_koenigs_eq hε hf hq hfq hz]
  exact (hs.hasSum.tendsto_sum_nat.const_add 1).congr fun n => (PSeq_eq_sum f q n z).symm

/-- `ĝ'' = Ĥ_f ĝ'` on `B_ε`, as the limit of `P_n' = Ĥ_n P_n`. -/
private theorem deriv_deriv_koenigs' {z : ℂ} (hz : z ∈ nbhd ε) :
    deriv (deriv (koenigs f q)) z = hatH f z * deriv (koenigs f q) z := by
  obtain ⟨C, -, hC⟩ := exists_norm_PSeq_sub_le hε hf hq hfq
  have ho := isOpen_nbhd ε
  have hdiff : ∀ k, DifferentiableOn ℂ (fun w => PSeq f q (k + 1) w - PSeq f q k w) (nbhd ε) :=
    fun k => (differentiableOn_PSeq hε hf (k + 1)).sub (differentiableOn_PSeq hε hf k)
  have hsum := Complex.hasSum_deriv_of_summable_norm (summable_geometric_cmax hε hf C) hdiff ho
    (fun k w hw => hC k w hw) hz
  have heq : deriv (koenigs f q) =ᶠ[𝓝 z]
      fun w => 1 + ∑' k, (PSeq f q (k + 1) w - PSeq f q k w) := by
    filter_upwards [ho.mem_nhds hz] with w hw using deriv_koenigs_eq hε hf hq hfq hw
  rw [heq.deriv_eq, deriv_const_add]
  -- the partial sums of the derivatives are the `P_n'`
  have hda : ∀ k, DifferentiableAt ℂ (PSeq f q k) z := fun k =>
    (differentiableOn_PSeq hε hf k).differentiableAt (ho.mem_nhds hz)
  have hpartial : ∀ n, ∑ k ∈ Finset.range n,
      deriv (fun w => PSeq f q (k + 1) w - PSeq f q k w) z = deriv (PSeq f q n) z := by
    intro n
    rw [Finset.sum_congr rfl fun k _ => deriv_fun_sub (hda (k + 1)) (hda k),
      Finset.sum_range_sub (fun k => deriv (PSeq f q k) z)]
    have h0 : PSeq f q 0 = fun _ => 1 := funext (PSeq_zero f q)
    rw [h0, deriv_const, sub_zero]
  have h1 := hsum.tendsto_sum_nat.congr hpartial
  have h2 : Tendsto (fun n => (∑ k ∈ Finset.range n, hatHTerm f k z) * PSeq f q n z) atTop
      (𝓝 (hatH f z * deriv (koenigs f q) z)) :=
    (summable_hatHTerm hε hf (subset_closure hz)).hasSum.tendsto_sum_nat.mul
      (tendsto_PSeq hε hf hq hfq hz)
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  rw [deriv_PSeq hε hf n (subset_closure hz)]

private theorem koenigs_self' : koenigs f q q = 0 := by
  refine tendsto_nhds_unique (tendsto_koenigs hε hf hq hfq hq) ?_
  simp only [gSeq_fixed hfq]
  exact tendsto_const_nhds

private theorem deriv_koenigs_self' : deriv (koenigs f q) q = 1 := by
  have hne := deriv_ne_zero_fixed hf hq
  have h : ∀ n, PSeq f q n q = 1 := fun n => by
    rw [PSeq_eq_prod hε hf hq n (subset_closure hq)]
    exact Finset.prod_eq_one fun k _ => by rw [Function.iterate_fixed hfq k, div_self hne]
  refine tendsto_nhds_unique (tendsto_PSeq hε hf hq hfq hq) ?_
  simp only [h]
  exact tendsto_const_nhds

private theorem koenigs_comp' {z : ℂ} (hz : z ∈ nbhd ε) :
    koenigs f q (f z) = deriv f q * koenigs f q z := by
  have hfz : f z ∈ nbhd ε := hf.mapsTo (subset_closure hz)
  have hne := deriv_ne_zero_fixed hf hq
  have h := ((tendsto_koenigs hε hf hq hfq hz).comp (tendsto_add_atTop_nat 1)).const_mul
    (deriv f q)
  refine tendsto_nhds_unique (tendsto_koenigs hε hf hq hfq hfz) (h.congr fun n => ?_)
  simp only [Function.comp, gSeq, Function.iterate_succ_apply]
  rw [pow_succ]
  field_simp

end Approximants

/-! ## Realness and positivity on `I` -/

omit hε in
private theorem im_deriv_ofReal {t : ℝ} (ht : (t : ℂ) ∈ nbhd (2 * ε)) : (deriv f t).im = 0 :=
  im_deriv_eq_zero (isOpen_nbhd _) hf.differentiableOn hf.im_eq_zero ht

private theorem im_iterate_ofReal (n : ℕ) {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) :
    (f^[n] t).im = 0 := by
  rw [← koenigsIFS_comp hε hf]
  exact (koenigsIFS hε hf).im_comp_ofReal _ ht

private theorem re_iterate_mem_I (n : ℕ) {x : ℝ} (hx : x ∈ I) : (f^[n] x).re ∈ I := by
  rw [← koenigsIFS_comp hε hf]
  exact (koenigsIFS hε hf).re_comp_mem_I _ hx

/-- `f'` has constant sign on `I`: it is real, continuous and nonvanishing there. -/
private theorem re_deriv_mul_pos {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    0 < (deriv f x).re * (deriv f y).re := by
  by_contra! hneg
  have h2ε : 0 < 2 * ε := by linarith
  have hc : ContinuousOn (deriv f) (nbhd (2 * ε)) :=
    (hf.differentiableOn.deriv (isOpen_nbhd _)).continuousOn
  have hcont : ContinuousOn (fun t : ℝ => (deriv f t).re) (uIcc x y) :=
    Complex.continuous_re.comp_continuousOn (hc.comp Complex.continuous_ofReal.continuousOn
      fun t ht => ofReal_mem_nbhd h2ε (uIcc_subset_Icc hx hy ht))
  obtain ⟨t, ht, ht0⟩ : (0 : ℝ) ∈ (fun t : ℝ => (deriv f t).re) '' uIcc x y := by
    apply intermediate_value_uIcc hcont
    rcases mul_nonpos_iff.1 hneg with h | h
    · exact mem_uIcc.2 (Or.inr ⟨h.2, h.1⟩)
    · exact mem_uIcc.2 (Or.inl ⟨h.1, h.2⟩)
  have htI : t ∈ I := uIcc_subset_Icc hx hy ht
  refine hf.deriv_ne_zero _ (subset_closure (ofReal_mem_nbhd hε htI)) (Complex.ext ?_ ?_)
  · simpa using ht0
  · simpa using im_deriv_ofReal hf (ofReal_mem_nbhd h2ε htI)

/-! ## The main statements -/

variable {p : ℝ} (hp : p ∈ I) (hfp : f p = p)

include hp hfp

theorem differentiableOn_koenigs : DifferentiableOn ℂ (koenigs f p) (nbhd ε) :=
  differentiableOn_koenigs' hε hf (ofReal_mem_nbhd hε hp) hfp

theorem koenigs_self : koenigs f p p = 0 :=
  koenigs_self' hε hf (ofReal_mem_nbhd hε hp) hfp

theorem deriv_koenigs_self : deriv (koenigs f p) p = 1 :=
  deriv_koenigs_self' hε hf (ofReal_mem_nbhd hε hp) hfp

theorem koenigs_comp {z : ℂ} (hz : z ∈ nbhd ε) :
    koenigs f p (f z) = deriv f p * koenigs f p z :=
  koenigs_comp' hε hf (ofReal_mem_nbhd hε hp) hfp hz

theorem deriv_deriv_koenigs {z : ℂ} (hz : z ∈ nbhd ε) :
    deriv (deriv (koenigs f p)) z = hatH f z * deriv (koenigs f p) z :=
  deriv_deriv_koenigs' hε hf (ofReal_mem_nbhd hε hp) hfp hz

theorem im_koenigs_ofReal {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) : (koenigs f p t).im = 0 := by
  have hp' := ofReal_mem_nbhd hε hp
  have hlam := im_deriv_ofReal hf (IFS.nbhd_subset_two hp')
  have hn : ∀ n, (gSeq f p n t).im = 0 := fun n => by
    have h : gSeq f p n t = ((((f^[n] t).re - p) / (deriv f p).re ^ n : ℝ) : ℂ) := by
      push_cast
      rw [← eq_ofReal_re_of_im_eq_zero (im_iterate_ofReal hε hf n ht),
        ← eq_ofReal_re_of_im_eq_zero hlam]
      rfl
    rw [h, Complex.ofReal_im]
  refine tendsto_nhds_unique
    ((Complex.continuous_im.tendsto _).comp (tendsto_koenigs hε hf hp' hfp ht)) ?_
  simp only [Function.comp_def, hn]
  exact tendsto_const_nhds

/-- On `I`, the derivative of `ĝ` is real and positive. -/
theorem deriv_koenigs_ofReal {x : ℝ} (hx : x ∈ I) :
    (deriv (koenigs f p) x).im = 0 ∧ 0 < (deriv (koenigs f p) x).re := by
  have hp' := ofReal_mem_nbhd hε hp
  have hx' := ofReal_mem_nbhd hε hx
  have hlam := im_deriv_ofReal hf (IFS.nbhd_subset_two hp')
  have hy : ∀ k, f^[k] (x : ℂ) = ((f^[k] x).re : ℂ) := fun k =>
    eq_ofReal_re_of_im_eq_zero (im_iterate_ofReal hε hf k hx')
  -- the factors `f'(f^k(x))/f'(p)` of `P_n(x)` are real and positive
  set a : ℕ → ℝ := fun k => (deriv f (f^[k] x)).re / (deriv f p).re with ha_def
  have hreal : ∀ k, deriv f (f^[k] x) / deriv f p = (a k : ℂ) := fun k => by
    have hd : (deriv f (f^[k] x)).im = 0 := by
      rw [hy k]
      exact im_deriv_ofReal hf
        (IFS.nbhd_subset_two (ofReal_mem_nbhd hε (re_iterate_mem_I hε hf k hx)))
    simp only [ha_def]
    push_cast
    rw [← eq_ofReal_re_of_im_eq_zero hd, ← eq_ofReal_re_of_im_eq_zero hlam]
  have hpos : ∀ k, 0 < a k := fun k => by
    have h := re_deriv_mul_pos hε hf (re_iterate_mem_I hε hf k hx) hp
    rw [← hy k] at h
    rcases mul_pos_iff.1 h with h | h
    · exact div_pos h.1 h.2
    · exact div_pos_of_neg_of_neg h.1 h.2
  have hP : ∀ n, PSeq f p n x = ((∏ k ∈ Finset.range n, a k : ℝ) : ℂ) := fun n => by
    rw [PSeq_eq_prod hε hf hp' n (subset_closure hx'), Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun k _ => hreal k
  have hT := tendsto_PSeq hε hf hp' hfp hx'
  constructor
  · refine tendsto_nhds_unique ((Complex.continuous_im.tendsto _).comp hT) ?_
    simp only [Function.comp_def, hP, Complex.ofReal_im]
    exact tendsto_const_nhds
  · obtain ⟨A, -, hA⟩ := exists_norm_ratio_sub_one_le hε hf hp' hfp
    have hs : Summable fun k => a k - 1 := by
      refine (summable_geometric_cmax hε hf A).of_norm_bounded fun k => ?_
      have h := hA k x hx'
      rwa [hreal k, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real] at h
    refine pos_of_tendsto_prod hpos hs ?_
    have h := (Complex.continuous_re.tendsto _).comp hT
    simpa only [Function.comp_def, hP, Complex.ofReal_re] using h

end

end AnalyticESC
