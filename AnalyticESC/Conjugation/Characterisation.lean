module

public import AnalyticESC.Conjugation.Uniqueness
public import AnalyticESC.Conjugation.Composite
public import AnalyticESC.Conjugation.Zeros

@[expose] public section

/-!
# Theorem 1.12

Every system is conjugated to one with a similarity map; it is conjugated to a self-similar
system exactly when all dual natural projections agree on `[0,1]`; and it is sub-conjugated to a
self-similar system exactly when two distinct periodic words of the same period have equal dual
natural projections. Both equivalences hold without the hypothesis that the attractor is not a
singleton; `theorem_1_12` states them as in the paper.
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-! ## Single maps of the class -/

section Single

variable {ε : ℝ} {f : ℂ → ℂ}

/-- At points of `[0,1]`, the derivative of a map of the class is real, nonzero and of modulus
less than one. -/
private theorem char_re_deriv_ne_zero_abs_lt_one (hε : 0 < ε) (hf : InClass ε f) {x : ℝ}
    (hx : x ∈ I) : (deriv f x).re ≠ 0 ∧ |(deriv f x).re| < 1 := by
  have hcl : (x : ℂ) ∈ closure (nbhd ε) := subset_closure (ofReal_mem_nbhd hε hx)
  have him : (deriv f x).im = 0 := im_deriv_eq_zero (isOpen_nbhd _) hf.differentiableOn
    hf.im_eq_zero (ofReal_mem_nbhd (by linarith) hx)
  exact ⟨fun h => hf.deriv_ne_zero _ hcl (Complex.ext h him),
    (Complex.abs_re_le_norm _).trans_lt (hf.norm_deriv_lt_one _ hcl)⟩

/-- The real restriction of a map of the class has derivative `Re f'` at points of `[0,1]`. -/
private theorem char_hasDerivAt_re (hε : 0 < ε) (hf : InClass ε f) {x : ℝ} (hx : x ∈ I) :
    HasDerivAt (fun t : ℝ => (f t).re) (deriv f x).re x :=
  hasDerivAt_re_ofReal (hf.differentiableOn.differentiableAt
    ((isOpen_nbhd _).mem_nhds (ofReal_mem_nbhd (by linarith) hx)))

/-- The real restriction of a map of the class has nonzero derivative on `[0,1]`. -/
private theorem char_deriv_re_ne_zero (hε : 0 < ε) (hf : InClass ε f) {x : ℝ}
    (hx : x ∈ I) : deriv (fun t : ℝ => (f t).re) x ≠ 0 := by
  rw [(char_hasDerivAt_re hε hf hx).deriv]
  exact (char_re_deriv_ne_zero_abs_lt_one hε hf hx).1

/-- The real restriction of a map of the class is analytic near `[0,1]`. -/
private theorem char_analyticOnNhd_re (hε : 0 < ε) (hf : InClass ε f) :
    AnalyticOnNhd ℝ (fun t : ℝ => (f t).re) I :=
  analyticOnNhd_re_ofReal hε (hf.differentiableOn.mono IFS.nbhd_subset_two)

/-- `Re ĝ ∘ f = Re f'(p) · Re ĝ` on `[0,1]`. -/
private theorem char_re_koenigs_conj (hε : 0 < ε) (hf : InClass ε f) {p : ℝ} (hp : p ∈ I)
    (hfp : f p = p) {x : ℝ} (hx : x ∈ I) :
    (koenigs f p ((f x).re : ℂ)).re = (deriv f p).re * (koenigs f p x).re := by
  have hx' := ofReal_mem_nbhd hε hx
  have hfx : (((f x).re : ℝ) : ℂ) = f x :=
    Complex.ext (by simp) (by simp [hf.im_eq_zero x (ofReal_mem_nbhd (by linarith) hx)])
  rw [hfx, koenigs_comp hε hf hp hfp hx', Complex.mul_re, im_koenigs_ofReal hε hf hp hfp hx',
    mul_zero, sub_zero]

/-- The real restriction `Re ĝ` of the linearising map is an analytic coordinate with positive
derivative on `[0,1]`, vanishes at `p` and solves `φ'' = Re Ĥ_f φ'` on `[0,1]`. -/
private theorem char_re_koenigs_spec (hε : 0 < ε) (hf : InClass ε f) {p : ℝ} (hp : p ∈ I)
    (hfp : f p = p) :
    IsAnalyticCoord (fun t : ℝ => (koenigs f p t).re) ∧
      (∀ x ∈ I, 0 < deriv (fun t : ℝ => (koenigs f p t).re) x) ∧
      (koenigs f p p).re = 0 ∧
      ∀ x ∈ I, deriv (deriv (fun t : ℝ => (koenigs f p t).re)) x =
        (hatH f x).re * deriv (fun t : ℝ => (koenigs f p t).re) x := by
  have han : AnalyticOnNhd ℝ (fun t : ℝ => (koenigs f p t).re) I :=
    analyticOnNhd_re_ofReal hε (differentiableOn_koenigs hε hf hp hfp)
  have hd : ∀ x ∈ I, 0 < deriv (fun t : ℝ => (koenigs f p t).re) x := fun x hx => by
    rw [(hasDerivAt_re_ofReal ((differentiableOn_koenigs hε hf hp hfp).differentiableAt
      ((isOpen_nbhd ε).mem_nhds (ofReal_mem_nbhd hε hx)))).deriv]
    exact (deriv_koenigs_ofReal hε hf hp hfp hx).2
  refine ⟨⟨han, (strictMonoOn_of_deriv_pos (convex_Icc 0 1) han.continuousOn
    fun x hx => hd x (interior_subset hx)).injOn⟩, hd, by simp [koenigs_self hε hf hp hfp], ?_⟩
  exact deriv_deriv_eq_hatH_mul hε hf han (fun x hx => (hd x hx).ne') (lam := (deriv f p).re)
    (t := 0) fun x hx => by rw [add_zero]; exact char_re_koenigs_conj hε hf hp hfp hx

/-- A solution of `φ'' = Re Ĥ_f φ'` on `[0,1]` conjugates `f` to an affine contraction. -/
private theorem char_exists_conj_of_ode (hε : 0 < ε) (hf : InClass ε f) {p : ℝ} (hp : p ∈ I)
    (hfp : f p = p) {φ : ℝ → ℝ} (hφ : AnalyticOnNhd ℝ φ I)
    (hode : ∀ x ∈ I, deriv (deriv φ) x = (hatH f x).re * deriv φ x) :
    ∃ lam t : ℝ, lam ≠ 0 ∧ |lam| < 1 ∧ ∀ x ∈ I, φ (f x).re = lam * φ x + t := by
  have h := eq_add_mul_koenigs hε hf hp hfp hφ hode
  refine ⟨(deriv f p).re, φ p * (1 - (deriv f p).re), (char_re_deriv_ne_zero_abs_lt_one hε hf hp).1,
    (char_re_deriv_ne_zero_abs_lt_one hε hf hp).2, fun x hx => ?_⟩
  rw [h _ (hf.re_mem_I x hx), h x hx, char_re_koenigs_conj hε hf hp hfp hx]
  ring

/-- Two maps of the class conjugated to affine maps by the same analytic `φ` with `φ' ≠ 0` have
the same `Ĥ` on `[0,1]`. -/
private theorem char_hatH_eq_of_conj {ε₁ ε₂ : ℝ} {f₁ f₂ : ℂ → ℂ} (hε₁ : 0 < ε₁)
    (hf₁ : InClass ε₁ f₁) (hε₂ : 0 < ε₂) (hf₂ : InClass ε₂ f₂) {φ : ℝ → ℝ}
    (hφ : AnalyticOnNhd ℝ φ I) (hφ' : ∀ x ∈ I, deriv φ x ≠ 0) {a₁ b₁ a₂ b₂ : ℝ}
    (h₁ : ∀ x ∈ I, φ (f₁ x).re = a₁ * φ x + b₁) (h₂ : ∀ x ∈ I, φ (f₂ x).re = a₂ * φ x + b₂) :
    ∀ x ∈ I, hatH f₁ x = hatH f₂ x := by
  intro x hx
  have e₁ := deriv_deriv_eq_hatH_mul hε₁ hf₁ hφ hφ' h₁ x hx
  have e₂ := deriv_deriv_eq_hatH_mul hε₂ hf₂ hφ hφ' h₂ x hx
  refine Complex.ext (mul_right_cancel₀ (hφ' x hx) (e₁.symm.trans e₂)) ?_
  rw [im_hatH_ofReal hε₁ hf₁ (ofReal_mem_nbhd hε₁ hx),
    im_hatH_ofReal hε₂ hf₂ (ofReal_mem_nbhd hε₂ hx)]

end Single

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- Compositions along nonempty words are `c_max`-Lipschitz on `[0,1]`. -/
private theorem char_abs_re_comp_sub_le {w : List (Fin N)} (hw : w ≠ []) {x y : ℝ} (hx : x ∈ I)
    (hy : y ∈ I) : |(Φ.comp w x).re - (Φ.comp w y).re| ≤ Φ.cmax * |x - y| := by
  have h := Φ.norm_comp_sub_le w (ofReal_mem_nbhd Φ.ε_pos hx) (ofReal_mem_nbhd Φ.ε_pos hy)
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  calc |(Φ.comp w x).re - (Φ.comp w y).re| = |(Φ.comp w x - Φ.comp w y).re| := by
        rw [Complex.sub_re]
    _ ≤ ‖Φ.comp w x - Φ.comp w y‖ := Complex.abs_re_le_norm _
    _ ≤ Φ.cmax ^ w.length * |x - y| := h
    _ ≤ Φ.cmax * |x - y| := mul_le_mul_of_nonneg_right
        (pow_le_of_le_one Φ.cmax_nonneg Φ.cmax_lt_one.le
          fun h => hw (List.length_eq_zero_iff.1 h)) (abs_nonneg _)

/-- `Ĥ_{f_k} = H_{k^∞}` on `[0,1]`. -/
private theorem char_hatH_f_eq_dualProj_const (k : Fin N) :
    ∀ x ∈ I, hatH (Φ.f k) x = Φ.dualProj (.inf fun _ => k) x := by
  intro x hx
  have h := Φ.hatH_comp_eq_dualProj one_pos ![k] x hx
  have hw : periodic one_pos (![k] ∘ Fin.rev) = fun _ => k :=
    funext fun n => by unfold periodic; exact Matrix.cons_val_fin_one k ![] _
  have hc : Φ.comp (List.ofFn ![k]) = Φ.f k := by simp
  rwa [hw, hc] at h

/-- Theorem 1.12, first claim: `Φ` is conjugated, by a map with nonvanishing derivative, to an
analytic IFS in which `g ∘ f_i ∘ g⁻¹` is a similarity. -/
theorem theorem_1_12_similarity (i : Fin N) :
    ∃ g, IsAnalyticCoord g ∧ (∀ x ∈ I, deriv g x ≠ 0) ∧
      ∃ lam t : ℝ, lam ≠ 0 ∧ |lam| < 1 ∧ ∀ x ∈ I, g (Φ.f i x).re = lam * g x + t := by
  have hf := Φ.inClass i
  obtain ⟨p, ⟨hp, hfp⟩, -⟩ := existsUnique_fixedPoint Φ.ε_pos hf
  obtain ⟨hco, hd, -, -⟩ := char_re_koenigs_spec Φ.ε_pos hf hp hfp
  obtain ⟨h0, h1⟩ := char_re_deriv_ne_zero_abs_lt_one Φ.ε_pos hf hp
  exact ⟨_, hco, fun x hx => (hd x hx).ne', _, 0, h0, h1, fun x hx => by
    rw [add_zero]; exact char_re_koenigs_conj Φ.ε_pos hf hp hfp hx⟩

/-- Theorem 1.12 (a), for every system. -/
theorem conjSelfSimilar_iff :
    ConjSelfSimilar Φ.realMaps ↔
      ∀ i j : ℕ → Fin N, ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact ⟨fun _ i _ => (i 0).elim0,
      fun _ => ⟨id, ⟨analyticOnNhd_id, injOn_id _⟩, 0, 0, fun j => j.elim0⟩⟩
  have hε := Φ.ε_pos
  set k₀ : Fin N := ⟨0, hN⟩
  choose p hp hfp using fun k => (existsUnique_fixedPoint hε (Φ.inClass k)).exists
  have hmaps : ∀ k, MapsTo (Φ.realMaps k) I I := fun k x hx => (Φ.inClass k).re_mem_I x hx
  constructor
  · rintro ⟨g, ⟨hg, hinj⟩, lam, t, hconj⟩
    -- an analytic coordinate with nonvanishing derivative conjugating every `F_k` to an affine map
    obtain ⟨φ, hφ, hφ', hc⟩ : ∃ φ : ℝ → ℝ, AnalyticOnNhd ℝ φ I ∧ (∀ x ∈ I, deriv φ x ≠ 0) ∧
        ∀ k, ∃ a b : ℝ, ∀ x ∈ I, φ (Φ.f k x).re = a * φ x + b := by
      by_cases hpq : ∃ k l, p k ≠ p l
      · -- two fixed points differ: `g` itself has nonvanishing derivative
        obtain ⟨k, l, hkl⟩ := hpq
        have hFp : ∀ k, Φ.realMaps k (p k) = p k := fun k => by
          simp only [realMaps, hfp k, Complex.ofReal_re]
        refine ⟨g, hg, deriv_ne_zero_of_conj Φ.cmax_lt_one hmaps
          (fun k x hx y hy => Φ.char_abs_re_comp_sub_le (List.cons_ne_nil k []) hx hy)
          (fun k x hx => (char_hasDerivAt_re hε (Φ.inClass k) hx).differentiableAt)
          (fun k x hx => char_deriv_re_ne_zero hε (Φ.inClass k) hx) hg hinj
          (fun k => (hconj k).2.2) (hp k) (hp l) (hFp k) (hFp l) hkl,
          fun k => ⟨lam k, t k, (hconj k).2.2⟩⟩
      · -- a common fixed point: the maps commute, so `Re ĝ` for `f_{k₀}` conjugates each of them
        push Not at hpq
        have hf₀ := Φ.inClass k₀
        have hFq : ∀ k, Φ.realMaps k (p k₀) = p k₀ := fun k => by
          simp only [realMaps, ← hpq k k₀, hfp k, Complex.ofReal_re]
        obtain ⟨⟨hGa, -⟩, hGd, hG0, -⟩ := char_re_koenigs_spec hε hf₀ (hp k₀) (hfp k₀)
        refine ⟨_, hGa, fun x hx => (hGd x hx).ne', fun k => ?_⟩
        have hcomm := comp_comm_of_conj hinj (hmaps k) (hmaps k₀) (hconj k).2.2
          (hconj k₀).2.2 (hp k₀) (hFq k) (hFq k₀)
        set G : ℝ → ℝ := fun t => (koenigs (Φ.f k₀) (p k₀) t).re
        set φ : ℝ → ℝ := fun x => G (Φ.realMaps k x)
        have hφa : AnalyticOnNhd ℝ φ I := fun x hx =>
          (hGa _ (hmaps k hx)).comp (char_analyticOnNhd_re hε (Φ.inClass k) x hx)
        have hφ' : ∀ x ∈ I, deriv φ x ≠ 0 := fun x hx => by
          have hd : HasDerivAt φ (deriv G (Φ.realMaps k x) * (deriv (Φ.f k) x).re) x :=
            ((hGa _ (hmaps k hx)).differentiableAt.hasDerivAt).comp x
              (char_hasDerivAt_re hε (Φ.inClass k) hx)
          rw [hd.deriv]
          exact mul_ne_zero (hGd _ (hmaps k hx)).ne'
            (char_re_deriv_ne_zero_abs_lt_one hε (Φ.inClass k) hx).1
        have hφc : ∀ x ∈ I, φ (Φ.f k₀ x).re = (deriv (Φ.f k₀) (p k₀)).re * φ x + 0 :=
          fun x hx => by
            rw [add_zero]
            show G (Φ.realMaps k (Φ.realMaps k₀ x)) = _
            rw [hcomm x hx]
            exact char_re_koenigs_conj hε hf₀ (hp k₀) (hfp k₀) (hmaps k hx)
        have heq := eq_add_mul_koenigs hε hf₀ (hp k₀) (hfp k₀) hφa
          (deriv_deriv_eq_hatH_mul hε hf₀ hφa hφ' hφc)
        have hφq : φ (p k₀) = 0 := by
          show G (Φ.realMaps k (p k₀)) = 0
          rw [hFq k]
          exact hG0
        refine ⟨deriv φ (p k₀), 0, fun x hx => ?_⟩
        have h := heq x hx
        rw [hφq, zero_add] at h
        rw [add_zero]
        exact h
    refine Φ.dualProj_eq_of_forall_const fun k l x hx => ?_
    rw [← Φ.char_hatH_f_eq_dualProj_const k x hx, ← Φ.char_hatH_f_eq_dualProj_const l x hx]
    obtain ⟨a₁, b₁, h₁⟩ := hc k
    obtain ⟨a₂, b₂, h₂⟩ := hc l
    exact char_hatH_eq_of_conj hε (Φ.inClass k) hε (Φ.inClass l) hφ hφ' h₁ h₂ x hx
  · intro h
    have hH : ∀ k, ∀ x ∈ I, hatH (Φ.f k) x = hatH (Φ.f k₀) x := fun k x hx => by
      rw [Φ.char_hatH_f_eq_dualProj_const k x hx, Φ.char_hatH_f_eq_dualProj_const k₀ x hx]
      exact h _ _ x hx
    obtain ⟨hco, -, -, hode⟩ := char_re_koenigs_spec hε (Φ.inClass k₀) (hp k₀) (hfp k₀)
    choose lam t hlam using fun k => char_exists_conj_of_ode hε (Φ.inClass k) (hp k) (hfp k) hco.1
      fun x hx => by rw [hH k x hx]; exact hode x hx
    exact ⟨_, hco, lam, t, hlam⟩

/-- Theorem 1.12 (b), for every system. -/
theorem subConjSelfSimilar_iff :
    Φ.SubConjSelfSimilar ↔
      ∃ (m : ℕ) (hm : 0 < m) (i j : Fin m → Fin N), i ≠ j ∧
        ∀ x ∈ I, Φ.dualProj (.inf (periodic hm i)) x = Φ.dualProj (.inf (periodic hm j)) x := by
  have hε := Φ.ε_pos
  have hne : ∀ {m : ℕ} (w : Fin m → Fin N), 0 < m → List.ofFn w ≠ [] := fun w hm h =>
    hm.ne' (List.ofFn_eq_nil_iff.1 h)
  have hrev : ∀ {m : ℕ} (w : Fin m → Fin N), (w ∘ Fin.rev) ∘ Fin.rev = w := fun w =>
    funext fun k => by simp
  have hrev_ne : ∀ {m : ℕ} {u v : Fin m → Fin N}, u ≠ v → u ∘ Fin.rev ≠ v ∘ Fin.rev :=
    fun {m u v} huv h => huv (by rw [← hrev u, h, hrev])
  constructor
  · rintro ⟨m, i, j, hij, g, ⟨hg, hinj⟩, lam, t, hconj⟩
    have hm : 0 < m := Nat.pos_of_ne_zero fun h => hij (by subst h; exact Subsingleton.elim _ _)
    obtain ⟨ε₁, hε₁, hf₁⟩ := Φ.exists_inClass_comp (hne i hm)
    obtain ⟨ε₂, hε₂, hf₂⟩ := Φ.exists_inClass_comp (hne j hm)
    obtain ⟨p₁, ⟨hp₁, hfp₁⟩, -⟩ := existsUnique_fixedPoint hε₁ hf₁
    obtain ⟨p₂, ⟨hp₂, hfp₂⟩, -⟩ := existsUnique_fixedPoint hε₂ hf₂
    have hci : ∀ x ∈ I, g (Φ.comp (List.ofFn i) x).re = lam 0 * g x + t 0 := (hconj 0).2.2
    have hcj : ∀ x ∈ I, g (Φ.comp (List.ofFn j) x).re = lam 1 * g x + t 1 := (hconj 1).2.2
    have hmi : MapsTo (fun x : ℝ => (Φ.comp (List.ofFn i) x).re) I I := fun x hx =>
      hf₁.re_mem_I x hx
    have hmj : MapsTo (fun x : ℝ => (Φ.comp (List.ofFn j) x).re) I I := fun x hx =>
      hf₂.re_mem_I x hx
    have hFi : (Φ.comp (List.ofFn i) p₁).re = p₁ := by rw [hfp₁, Complex.ofReal_re]
    have hFj : (Φ.comp (List.ofFn j) p₂).re = p₂ := by rw [hfp₂, Complex.ofReal_re]
    by_cases hpq : p₁ = p₂
    · -- a common fixed point: `f_i` and `f_j` commute on `[0,1]`, so `f_{ij} = f_{ji}` there
      subst hpq
      have hcomm := comp_comm_of_conj hinj hmi hmj hci hcj hp₁ hFi hFj
      have hm' : 0 < m + m := by omega
      have hcomp : ∀ {u v : Fin m → Fin N}, ∀ y ∈ I, Φ.comp (List.ofFn (Fin.append u v)) y =
          ((Φ.comp (List.ofFn u) ((Φ.comp (List.ofFn v) y).re : ℂ)).re : ℂ) := fun y hy => by
        rw [List.ofFn_fin_append, Φ.comp_append, Function.comp_apply]
        conv_lhs => rw [Φ.comp_ofReal _ hy]
        exact Φ.comp_ofReal _ (Φ.re_comp_mem_I _ hy)
      obtain ⟨ε₃, hε₃, hf₃⟩ := Φ.exists_inClass_comp (hne (Fin.append i j) hm')
      obtain ⟨ε₄, hε₄, hf₄⟩ := Φ.exists_inClass_comp (hne (Fin.append j i) hm')
      have hH := hatH_eq_of_eqOn_I hε₃ hf₃ hε₄ hf₄ fun y hy => by
        rw [hcomp y hy, hcomp y hy]
        exact congrArg _ (hcomm y hy)
      refine ⟨m + m, hm', Fin.append i j ∘ Fin.rev, Fin.append j i ∘ Fin.rev,
        hrev_ne fun h => hij (funext fun k => ?_), fun x hx => ?_⟩
      · simpa using congrFun h (Fin.castAdd m k)
      · rw [← Φ.hatH_comp_eq_dualProj hm' _ x hx, ← Φ.hatH_comp_eq_dualProj hm' _ x hx]
        exact hH x hx
    · -- distinct fixed points: `g` has nonvanishing derivative
      have hd := deriv_ne_zero_of_conj (F := ![fun x : ℝ => (Φ.comp (List.ofFn i) x).re,
          fun x : ℝ => (Φ.comp (List.ofFn j) x).re]) (k := 0) (l := 1) Φ.cmax_lt_one
        (Fin.forall_fin_two.2 ⟨hmi, hmj⟩)
        (Fin.forall_fin_two.2 ⟨fun x hx y hy => Φ.char_abs_re_comp_sub_le (hne i hm) hx hy,
          fun x hx y hy => Φ.char_abs_re_comp_sub_le (hne j hm) hx hy⟩)
        (Fin.forall_fin_two.2
          ⟨fun x hx => (char_hasDerivAt_re hε₁ hf₁ hx).differentiableAt,
            fun x hx => (char_hasDerivAt_re hε₂ hf₂ hx).differentiableAt⟩)
        (Fin.forall_fin_two.2 ⟨fun x hx => char_deriv_re_ne_zero hε₁ hf₁ hx,
          fun x hx => char_deriv_re_ne_zero hε₂ hf₂ hx⟩)
        hg hinj (fun k => (hconj k).2.2) hp₁ hp₂ hFi hFj hpq
      have hH := char_hatH_eq_of_conj hε₁ hf₁ hε₂ hf₂ hg hd hci hcj
      refine ⟨m, hm, i ∘ Fin.rev, j ∘ Fin.rev, hrev_ne hij, fun x hx => ?_⟩
      rw [← Φ.hatH_comp_eq_dualProj hm _ x hx, ← Φ.hatH_comp_eq_dualProj hm _ x hx]
      exact hH x hx
  · rintro ⟨m, hm, i, j, hij, h⟩
    have hH : ∀ x ∈ I, hatH (Φ.comp (List.ofFn (i ∘ Fin.rev))) x =
        hatH (Φ.comp (List.ofFn (j ∘ Fin.rev))) x := fun x hx => by
      rw [Φ.hatH_comp_eq_dualProj hm _ x hx, Φ.hatH_comp_eq_dualProj hm _ x hx, hrev, hrev]
      exact h x hx
    obtain ⟨ε₁, hε₁, hf₁⟩ := Φ.exists_inClass_comp (hne (i ∘ Fin.rev) hm)
    obtain ⟨ε₂, hε₂, hf₂⟩ := Φ.exists_inClass_comp (hne (j ∘ Fin.rev) hm)
    obtain ⟨p₁, ⟨hp₁, hfp₁⟩, -⟩ := existsUnique_fixedPoint hε₁ hf₁
    obtain ⟨p₂, ⟨hp₂, hfp₂⟩, -⟩ := existsUnique_fixedPoint hε₂ hf₂
    obtain ⟨hco, -, -, hode⟩ := char_re_koenigs_spec hε₁ hf₁ hp₁ hfp₁
    obtain ⟨l₁, t₁, c₁⟩ := char_exists_conj_of_ode hε₁ hf₁ hp₁ hfp₁ hco.1 hode
    obtain ⟨l₂, t₂, c₂⟩ := char_exists_conj_of_ode hε₂ hf₂ hp₂ hfp₂ hco.1 fun x hx => by
      rw [← hH x hx]; exact hode x hx
    exact ⟨m, i ∘ Fin.rev, j ∘ Fin.rev, hrev_ne hij, _, hco, ![l₁, l₂], ![t₁, t₂],
      Fin.forall_fin_two.2 ⟨c₁, c₂⟩⟩

set_option linter.unusedVariables false in
/-- Theorem 1.12 (a) and (b), for systems whose attractor is not a singleton. -/
theorem theorem_1_12 (hnd : ¬ ∃ x, Φ.attractor = {x}) :
    (ConjSelfSimilar Φ.realMaps ↔
      ∀ i j : ℕ → Fin N, ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x) ∧
    (Φ.SubConjSelfSimilar ↔
      ∃ (m : ℕ) (hm : 0 < m) (i j : Fin m → Fin N), i ≠ j ∧
        ∀ x ∈ I, Φ.dualProj (.inf (periodic hm i)) x = Φ.dualProj (.inf (periodic hm j)) x) :=
  ⟨Φ.conjSelfSimilar_iff, Φ.subConjSelfSimilar_iff⟩

end IFS

end AnalyticESC
