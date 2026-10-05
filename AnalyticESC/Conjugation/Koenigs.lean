module

public import AnalyticESC.Dual.Projection
public import AnalyticESC.Analysis
public import AnalyticESC.Analysis.Primitive

@[expose] public section

/-!
# The linearisation of a single map

For a map `f` of the class with fixed point `p ∈ I`, define `Ĥ_f` by (5.1) and
`ĝ(z) = ∫ₚᶻ exp(∫ₚʷ Ĥ_f) dw`, as in Lemma 5.1. Segment integration gives holomorphy on
`B_ε`, continuity on its closure, the ODE `ĝ'' = Ĥ_f ĝ'`, and positivity of `ĝ'` on `I`.

For the partial sums `Ĥ_n`, integrating the logarithmic derivative gives
`exp(∫ₚᶻ Ĥ_n) = (f^n)'(z)/f'(p)^n = ∏_{k<n} f'(f^k(z))/f'(p)`. Passing to the limit under the
integral yields (5.2), and shifting that limit proves `ĝ ∘ f = f'(p) ĝ`. The same limit,
combined with commutativity, is used in the singleton case of Theorem 2.3.
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-- The function `Ĥ_f(z) = ∑_{k ≥ 0} (f''/f')(f^k(z)) · (f^k)'(z)` of (5.1). -/
noncomputable def hatH (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' k, deriv (deriv f) (f^[k] z) / deriv f (f^[k] z) * deriv (f^[k]) z

/-- The ODE solution `ĝ(z) = ∫ₚᶻ exp(∫ₚʷ Ĥ_f) dw` from Lemma 5.1. -/
noncomputable def koenigs (f : ℂ → ℂ) (p : ℂ) (z : ℂ) : ℂ :=
  segmentPrimitive (fun w => Complex.exp (segmentPrimitive (hatH f) p w)) p z

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

private theorem PSeq_zero (f : ℂ → ℂ) (q z : ℂ) : PSeq f q 0 z = 1 := by simp [PSeq]

private theorem gSeq_fixed {f : ℂ → ℂ} {q : ℂ} (hfq : f q = q) (n : ℕ) : gSeq f q n q = 0 := by
  simp [gSeq, Function.iterate_fixed hfq n]


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

section ODEConstruction

omit hfq

/-! ## Constructing the solution of the ODE by two integrations -/

private theorem hasDerivAt_hatHPrimitive {z : ℂ} (hz : z ∈ nbhd ε) :
    HasDerivAt (segmentPrimitive (hatH f) q) (hatH f z) z :=
  hasDerivAt_segmentPrimitive (isOpen_nbhd ε) (convex_nbhd ε)
    (differentiableOn_hatH hε hf) hq hz

private theorem hasDerivAt_koenigs' {z : ℂ} (hz : z ∈ nbhd ε) :
    HasDerivAt (koenigs f q) (Complex.exp (segmentPrimitive (hatH f) q z)) z := by
  change HasDerivAt (segmentPrimitive (fun w => Complex.exp (segmentPrimitive (hatH f) q w)) q)
    (Complex.exp (segmentPrimitive (hatH f) q z)) z
  exact hasDerivAt_segmentPrimitive (isOpen_nbhd ε) (convex_nbhd ε)
    (fun w hw => ((hasDerivAt_hatHPrimitive hε hf hq hw).cexp).differentiableAt.differentiableWithinAt)
    hq hz

private theorem differentiableOn_koenigs' : DifferentiableOn ℂ (koenigs f q) (nbhd ε) :=
  fun _ hz => (hasDerivAt_koenigs' hε hf hq hz).differentiableAt.differentiableWithinAt

private theorem continuousOn_koenigs' : ContinuousOn (koenigs f q) (closure (nbhd ε)) := by
  have hH : ContinuousOn (hatH f) (closure (nbhd ε)) := by
    rw [hatH_eq_dualProj hε hf]
    exact (koenigsIFS hε hf).continuousOn_dualProj _
  exact continuousOn_segmentPrimitive (convex_nbhd ε).closure
    ((continuousOn_segmentPrimitive (convex_nbhd ε).closure hH (subset_closure hq)).cexp)
    (subset_closure hq)

private theorem deriv_koenigs_eq {z : ℂ} (hz : z ∈ nbhd ε) :
    deriv (koenigs f q) z = Complex.exp (segmentPrimitive (hatH f) q z) :=
  (hasDerivAt_koenigs' hε hf hq hz).deriv

private theorem deriv_deriv_koenigs' {z : ℂ} (hz : z ∈ nbhd ε) :
    deriv (deriv (koenigs f q)) z = hatH f z * deriv (koenigs f q) z := by
  have heq : deriv (koenigs f q) =ᶠ[𝓝 z] fun w => Complex.exp (segmentPrimitive (hatH f) q w) :=
    Filter.eventuallyEq_of_mem ((isOpen_nbhd ε).mem_nhds hz)
      (fun w hw => deriv_koenigs_eq hε hf hq hw)
  rw [heq.deriv_eq, ((hasDerivAt_hatHPrimitive hε hf hq hz).cexp).deriv,
    deriv_koenigs_eq hε hf hq hz]
  ring

private theorem deriv_koenigs_self' : deriv (koenigs f q) q = 1 := by
  rw [deriv_koenigs_eq hε hf hq hq, segmentPrimitive_self, Complex.exp_zero]

end ODEConstruction

/-! ## Integrating the logarithmic derivatives, then taking the product limit -/

private noncomputable def partialH (f : ℂ → ℂ) (n : ℕ) (z : ℂ) :=
  ∑ k ∈ Finset.range n, hatHTerm f k z

omit hq hfq in
private theorem differentiableOn_partialH (n : ℕ) :
    DifferentiableOn ℂ (partialH f n) (nbhd ε) := by
  apply DifferentiableOn.fun_sum
  intro k hk
  have h := (koenigsIFS hε hf).differentiableOn_dualTerm (.inf fun _ => 0) k
  have heq : (koenigsIFS hε hf).dualTerm (.inf fun _ => 0) k = hatHTerm f k :=
    funext (dualTerm_koenigsIFS hε hf k)
  rw [← heq]
  exact h

/-- The exponential of the integrated finite logarithmic-derivative sum is the finite
product `P_n = (f^n)'/λ^n`. This is the finite version of the displayed integral identity
in the proof of Lemma 5.1. -/
private theorem PSeq_eq_exp_primitive (n : ℕ) {z : ℂ} (hz : z ∈ nbhd ε) :
    PSeq f q n z = Complex.exp (segmentPrimitive (partialH f n) q z) := by
  let E (w : ℂ) := Complex.exp (segmentPrimitive (partialH f n) q w)
  have hE : ∀ w ∈ nbhd ε, HasDerivAt E (E w * partialH f n w) w := fun w hw =>
    (hasDerivAt_segmentPrimitive (isOpen_nbhd ε) (convex_nbhd ε)
      (differentiableOn_partialH hε hf n) hq hw).cexp
  have hP : ∀ w ∈ nbhd ε, HasDerivAt (PSeq f q n) (partialH f n w * PSeq f q n w) w := by
    intro w hw
    rw [partialH, ← deriv_PSeq hε hf (q := q) n (subset_closure hw)]
    exact ((differentiableOn_PSeq hε hf n).differentiableAt ((isOpen_nbhd ε).mem_nhds hw)).hasDerivAt
  have hQ : ∀ w ∈ nbhd ε, HasDerivAt (fun w => PSeq f q n w / E w) 0 w := by
    intro w hw
    convert! (hP w hw).div (hE w hw) (Complex.exp_ne_zero _) using 1
    field_simp
    ring
  have hconst := (isOpen_nbhd ε).is_const_of_deriv_eq_zero (isPreconnected_nbhd ε)
    (fun w hw => (hQ w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hQ w hw).deriv) hz hq
  have hPq : PSeq f q n q = 1 := by
    rw [PSeq_eq_prod hε hf hq n (subset_closure hq)]
    exact Finset.prod_eq_one fun k _ => by
      rw [Function.iterate_fixed hfq k, div_self (deriv_ne_zero_fixed hf hq)]
  have hEq : E q = 1 := by simp [E]
  rw [hPq, hEq, div_one, div_eq_one_iff_eq (Complex.exp_ne_zero _)] at hconst
  exact hconst

omit hq hfq in
private theorem exists_partialH_bound : ∃ B, ∀ n, ∀ z ∈ nbhd ε, ‖partialH f n z‖ ≤ B := by
  obtain ⟨C, hC0, hC⟩ := (koenigsIFS hε hf).exists_dualTerm_bound
  let c := (koenigsIFS hε hf).cmax
  refine ⟨C / (1 - c), fun n z hz => ?_⟩
  calc ‖partialH f n z‖ ≤ ∑ k ∈ Finset.range n, ‖hatHTerm f k z‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, C * c ^ k := Finset.sum_le_sum fun k hk => by
      rw [← dualTerm_koenigsIFS hε hf k z]
      exact hC (.inf fun _ => 0) k z (subset_closure hz)
    _ = C * ∑ k ∈ Finset.Ico 0 n, c ^ k := by rw [Finset.mul_sum, Finset.range_eq_Ico]
    _ ≤ C * (c ^ 0 / (1 - c)) := mul_le_mul_of_nonneg_left
      (geom_sum_Ico_le_of_lt_one (cmax_nonneg' hε hf) (cmax_lt_one' hε hf)) hC0
    _ = _ := by rw [pow_zero]; ring

private theorem tendsto_PSeq {z : ℂ} (hz : z ∈ nbhd ε) :
    Tendsto (fun n => PSeq f q n z) atTop (𝓝 (deriv (koenigs f q) z)) := by
  obtain ⟨B, hB⟩ := exists_partialH_bound hε hf
  have hlim := tendsto_segmentPrimitive (convex_nbhd ε)
    (fun n => (differentiableOn_partialH hε hf n).continuousOn) hB
    (fun w hw => (summable_hatHTerm hε hf (subset_closure hw)).hasSum.tendsto_sum_nat) hq hz
  rw [deriv_koenigs_eq hε hf hq hz]
  exact ((Complex.continuous_exp.tendsto _).comp hlim).congr
    (fun n => (PSeq_eq_exp_primitive hε hf hq hfq n hz).symm)

/-- Equation (5.2), deduced by integrating the derivative products after constructing `ĝ`
from the ODE. -/
private theorem tendsto_koenigs {z : ℂ} (hz : z ∈ nbhd ε) :
    Tendsto (fun n => gSeq f q n z) atTop (𝓝 (koenigs f q z)) := by
  obtain ⟨B, -, hB⟩ := exists_norm_PSeq_le hε hf hq hfq
  have hlim := tendsto_segmentPrimitive (convex_nbhd ε)
    (fun n => (differentiableOn_PSeq hε hf n).continuousOn) hB
    (fun w hw => tendsto_PSeq hε hf hq hfq hw) hq hz
  have heq : ∀ n, segmentPrimitive (PSeq f q n) q z = gSeq f q n z := by
    intro n
    have ht := segmentPrimitive_eq_sub (convex_nbhd ε) (g := gSeq f q n)
      (differentiableOn_PSeq hε hf (q := q) n).continuousOn
      (fun w hw => hasDerivAt_gSeq hε hf n (subset_closure hw)) hq hz
    simpa only [gSeq_fixed hfq, sub_zero] using ht
  have heq' : segmentPrimitive (deriv (koenigs f q)) q z = koenigs f q z := by
    have ht := segmentPrimitive_eq_sub (convex_nbhd ε)
      ((differentiableOn_koenigs' hε hf hq).deriv (isOpen_nbhd ε)).continuousOn
      (fun w hw => ((differentiableOn_koenigs' hε hf hq).differentiableAt
        ((isOpen_nbhd ε).mem_nhds hw)).hasDerivAt) hq hz
    simpa only [koenigs, segmentPrimitive_self, sub_zero] using ht
  simpa only [heq, heq'] using hlim

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

/-- Commuting maps with a common fixed point are linearised by the same `ĝ`.
This is the limit argument (5.2) used in the singleton case of Theorem 2.3. -/
theorem koenigs_commuting {g : ℂ → ℂ} (hg : InClass ε g) (hgq : g q = q)
    (hcomm : ∀ z ∈ nbhd ε, f (g z) = g (f z)) {z : ℂ} (hz : z ∈ nbhd ε) :
    koenigs f q (g z) = deriv g q * koenigs f q z := by
  have hit : ∀ n, f^[n] (g z) = g (f^[n] z) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      exact hcomm _ (mapsTo_iterate hε hf n hz)
  have hlim : Tendsto (fun n => f^[n] z) atTop (𝓝 q) := by
    rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (cmax_nonneg' hε hf)
        (cmax_lt_one' hε hf)).mul_const ‖z - q‖ |>.trans (by simp))
    simpa only [Function.iterate_fixed hfq] using norm_iterate_sub_le hε hf n hz hq
  have hgd := hg.differentiableOn.differentiableAt
    ((isOpen_nbhd _).mem_nhds (IFS.nbhd_subset_two hq))
  have hds : Tendsto (fun n => dslope g q (f^[n] z)) atTop (𝓝 (deriv g q)) := by
    simpa only [dslope_same, Function.comp_def] using
      (continuousAt_dslope_same.2 hgd).tendsto.comp hlim
  have hprod := hds.mul (tendsto_koenigs hε hf hq hfq hz)
  apply tendsto_nhds_unique (tendsto_koenigs hε hf hq hfq (hg.mapsTo (subset_closure hz)))
  refine hprod.congr fun n => ?_
  have he := sub_smul_dslope g q (f^[n] z)
  simp only [smul_eq_mul, hgq] at he
  simp only [gSeq, hit]
  rw [← he]
  ring

end Approximants

/-! ## The main statements -/

variable {p : ℝ} (hp : p ∈ I) (hfp : f p = p)

include hp hfp

-- Keep the common fixed-point interface for the public statements below.
set_option linter.unusedSectionVars false

theorem differentiableOn_koenigs : DifferentiableOn ℂ (koenigs f p) (nbhd ε) :=
  differentiableOn_koenigs' hε hf (ofReal_mem_nbhd hε hp)

theorem continuousOn_koenigs : ContinuousOn (koenigs f p) (closure (nbhd ε)) :=
  continuousOn_koenigs' hε hf (ofReal_mem_nbhd hε hp)

theorem koenigs_self : koenigs f p p = 0 :=
  segmentPrimitive_self _ _

theorem deriv_koenigs_self : deriv (koenigs f p) p = 1 :=
  deriv_koenigs_self' hε hf (ofReal_mem_nbhd hε hp)

theorem koenigs_comp {z : ℂ} (hz : z ∈ nbhd ε) :
    koenigs f p (f z) = deriv f p * koenigs f p z :=
  koenigs_comp' hε hf (ofReal_mem_nbhd hε hp) hfp hz

theorem deriv_deriv_koenigs {z : ℂ} (hz : z ∈ nbhd ε) :
    deriv (deriv (koenigs f p)) z = hatH f z * deriv (koenigs f p) z :=
  deriv_deriv_koenigs' hε hf (ofReal_mem_nbhd hε hp) hz

theorem im_koenigs_ofReal {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) : (koenigs f p t).im = 0 := by
  have hp' := ofReal_mem_nbhd hε hp
  have hd : DifferentiableOn ℂ (segmentPrimitive (hatH f) p) (nbhd ε) :=
    fun z hz => (hasDerivAt_hatHPrimitive hε hf hp' hz).differentiableAt.differentiableWithinAt
  apply im_segmentPrimitive_eq_zero (convex_nbhd ε) hd.continuousOn.cexp _ hp' ht
  intro x hx
  have him := im_segmentPrimitive_eq_zero (convex_nbhd ε)
    (differentiableOn_hatH hε hf).continuousOn (fun x hx => im_hatH_ofReal hε hf hx) hp' hx
  simp only [Complex.exp_im, him, Real.sin_zero, mul_zero]

/-- On `I`, the derivative of `ĝ` is real and positive. -/
theorem deriv_koenigs_ofReal {x : ℝ} (hx : x ∈ I) :
    (deriv (koenigs f p) x).im = 0 ∧ 0 < (deriv (koenigs f p) x).re := by
  have hp' := ofReal_mem_nbhd hε hp
  have hx' := ofReal_mem_nbhd hε hx
  have him := im_segmentPrimitive_eq_zero (convex_nbhd ε)
    (differentiableOn_hatH hε hf).continuousOn (fun t ht => im_hatH_ofReal hε hf ht) hp' hx'
  rw [deriv_koenigs_eq hε hf hp' hx', Complex.exp_im, Complex.exp_re, him]
  simpa using Real.exp_pos (segmentPrimitive (hatH f) p x).re

end

end AnalyticESC
