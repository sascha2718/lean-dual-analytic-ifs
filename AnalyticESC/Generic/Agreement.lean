module

public import AnalyticESC.Dual.Cylinders

@[expose] public section

/-!
# Dual compositions of two systems that agree along an orbit

Tools for the proof of Theorem 1.4 in Section 4.2. If the maps of `Ψ` agree with those of `Φ` to
second order along the orbit of a point `x`, then `G_w h = F_w h` at `x`. If they agree only to
first order at `x` itself, then `G_w h` at `x` is `F_w h` shifted by the change of `f''/f'` at
`x`. The section also bounds the width of the cylinder intervals and shows that the dual maps send
the closed cylinder into the open one under bounds on `[0,1]` alone.
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-- `g` agrees with `f` to second order at `y`: equal values, first and second derivatives. -/
def AgreeAt (f g : ℂ → ℂ) (y : ℂ) : Prop :=
  g y = f y ∧ deriv g y = deriv f y ∧ deriv (deriv g) y = deriv (deriv f) y

namespace IFS

variable {N : ℕ} {ε ε' : ℝ}

/-! ## Dual compositions along an orbit -/

/-- One step of `F_{i w}`: `F_{i w} h = f_i' · (F_w h ∘ f_i) + f_i''/f_i'`. -/
private theorem dualComp_cons_apply (Φ : IFS N ε) (i : Fin N) (w : List (Fin N)) (h : ℂ → ℂ)
    (z : ℂ) :
    Φ.dualComp (i :: w) h z = deriv (Φ.f i) z * Φ.dualComp w h (Φ.f i z) + Φ.nonlin i z :=
  rfl

/-- The orbit of `z` along a prefix of `i w` passes through `f_i(z)`. -/
private theorem comp_reverse_take_succ_cons (Φ : IFS N ε) (i : Fin N) (w : List (Fin N))
    (m : ℕ) (z : ℂ) :
    Φ.comp ((i :: w).take (m + 1)).reverse z = Φ.comp (w.take m).reverse (Φ.f i z) := by
  rw [List.take_succ_cons, List.reverse_cons, Φ.comp_append]
  rfl

/-- Shift the agreement hypothesis along `i w` to the orbit of `f_i(z)` along `w`. -/
private theorem agreeAt_tail (Φ : IFS N ε) (Ψ : IFS N ε') {i : Fin N} {w : List (Fin N)}
    {z : ℂ}
    (hag : ∀ m (hm : m < (i :: w).length),
      AgreeAt (Φ.f (i :: w)[m]) (Ψ.f (i :: w)[m]) (Φ.comp ((i :: w).take m).reverse z)) :
    ∀ m (hm : m < w.length),
      AgreeAt (Φ.f w[m]) (Ψ.f w[m]) (Φ.comp (w.take m).reverse (Φ.f i z)) := fun m hm => by
  have := hag (m + 1) (by simp [hm])
  rwa [comp_reverse_take_succ_cons, List.getElem_cons_succ] at this

/-- If `g_{w_m}` agrees with `f_{w_m}` to second order at `f_{w_{m-1}} ∘ ⋯ ∘ f_{w_0}(z)` for every
`m < |w|`, then `G_w h = F_w h` at `z`. -/
theorem dualComp_eq_of_agreeAt (Φ : IFS N ε) (Ψ : IFS N ε') {w : List (Fin N)} {z : ℂ}
    (hag : ∀ m (hm : m < w.length),
      AgreeAt (Φ.f w[m]) (Ψ.f w[m]) (Φ.comp (w.take m).reverse z))
    (h : ℂ → ℂ) : Ψ.dualComp w h z = Φ.dualComp w h z := by
  induction w generalizing z with
  | nil => rfl
  | cons i w ih =>
    obtain ⟨h0, h1, h2⟩ := hag 0 (by simp)
    simp only [List.getElem_cons_zero, List.take_zero, List.reverse_nil, comp_nil, id] at h0 h1 h2
    rw [dualComp_cons_apply, dualComp_cons_apply, h0, ih (agreeAt_tail Φ Ψ hag), h1, nonlin,
      nonlin, h1, h2]

/-- If `g_i` agrees with `f_i` to first order at `z`, and the later maps agree to second order
along the orbit of `f_i(z)`, then `G_{i w} h - F_{i w} h = g_i''/g_i' - f_i''/f_i'` at `z`. -/
theorem dualComp_cons_eq_of_agreeAt (Φ : IFS N ε) (Ψ : IFS N ε') {i : Fin N}
    {w : List (Fin N)} {z : ℂ} (h0 : Ψ.f i z = Φ.f i z) (h1 : deriv (Ψ.f i) z = deriv (Φ.f i) z)
    (hag : ∀ m (hm : m < w.length),
      AgreeAt (Φ.f w[m]) (Ψ.f w[m]) (Φ.comp (w.take m).reverse (Φ.f i z)))
    (h : ℂ → ℂ) :
    Ψ.dualComp (i :: w) h z = Φ.dualComp (i :: w) h z + (Ψ.nonlin i z - Φ.nonlin i z) := by
  rw [dualComp_cons_apply, dualComp_cons_apply, h0, h1, dualComp_eq_of_agreeAt Φ Ψ hag]
  ring

/-- The cylinder intervals of `Φ` and `Ψ` at `x` agree under the hypothesis of
`dualComp_eq_of_agreeAt`. -/
theorem dualCylAt_eq_of_agreeAt (Φ : IFS N ε) (Ψ : IFS N ε') (k K : ℝ) {w : List (Fin N)}
    {x : ℝ}
    (hag : ∀ m (hm : m < w.length),
      AgreeAt (Φ.f w[m]) (Ψ.f w[m]) (Φ.comp (w.take m).reverse x)) :
    Ψ.dualCylAt k K w x = Φ.dualCylAt k K w x := by
  rw [dualCylAt, dualCylAt, dualComp_eq_of_agreeAt Φ Ψ hag, dualComp_eq_of_agreeAt Φ Ψ hag]

/-- Under the hypothesis of `dualComp_cons_eq_of_agreeAt` at a real point `x`, the cylinder
interval of `Ψ` at `x` is that of `Φ` shifted by the real part of the change of `f_i''/f_i'`. -/
theorem dualCylAt_cons_eq_of_agreeAt (Φ : IFS N ε) (Ψ : IFS N ε') (k K : ℝ) {i : Fin N}
    {w : List (Fin N)} {x : ℝ} (h0 : Ψ.f i x = Φ.f i x)
    (h1 : deriv (Ψ.f i) x = deriv (Φ.f i) x)
    (hag : ∀ m (hm : m < w.length),
      AgreeAt (Φ.f w[m]) (Ψ.f w[m]) (Φ.comp (w.take m).reverse (Φ.f i x))) :
    Ψ.dualCylAt k K (i :: w) x =
      (· + (Ψ.nonlin i x - Φ.nonlin i x).re) '' Φ.dualCylAt k K (i :: w) x := by
  rw [dualCylAt, dualCylAt, image_add_const_uIcc, dualComp_cons_eq_of_agreeAt Φ Ψ h0 h1 hag,
    dualComp_cons_eq_of_agreeAt Φ Ψ h0 h1 hag, Complex.add_re, Complex.add_re]

/-- `G_i` maps `cl (-K,K)` into `(-K,K)` when `|g_i'| ≤ c` and `|g_i''/g_i'| ≤ M` on `[0,1]` and
`c K + M < K`. -/
theorem mapsTo_dualOp_dualCylClosed_of_le (Ψ : IFS N ε') {c M K : ℝ}
    (hc : ∀ i, ∀ x ∈ I, ‖deriv (Ψ.f i) x‖ ≤ c) (hM : ∀ i, ∀ x ∈ I, ‖Ψ.nonlin i x‖ ≤ M)
    (hK : c * K + M < K) (i : Fin N) :
    MapsTo (Ψ.dualOp i) (dualCylClosed ε' (-K) K) (dualCyl ε' (-K) K) := by
  rintro h ⟨hd, hre, hb⟩
  have hfx : ∀ x ∈ I, Ψ.f i x = (((Ψ.f i x).re : ℝ) : ℂ) ∧ (Ψ.f i x).re ∈ I := fun x hx =>
    ⟨Complex.ext (by simp)
      (by simp [Ψ.im_f_ofReal i (nbhd_subset_two (ofReal_mem_nbhd Ψ.ε_pos hx))]),
      (Ψ.inClass i).re_mem_I x hx⟩
  have him : ∀ x ∈ I, (Ψ.dualOp i h x).im = 0 := by
    intro x hx
    have hxn := ofReal_mem_nbhd Ψ.ε_pos hx
    simp only [dualOp]
    rw [(hfx x hx).1]
    simp [Complex.mul_im, Ψ.im_deriv_f_ofReal i (nbhd_subset_two hxn), hre _ (hfx x hx).2,
      Ψ.im_nonlin_ofReal i hxn]
  refine ⟨?_, him, fun x hx => ?_⟩
  · obtain ⟨U, -, hU, -, hnl⟩ := Ψ.exists_differentiableOn_nonlin i
    have h1 : DifferentiableOn ℂ (deriv (Ψ.f i)) (nbhd ε') :=
      ((Ψ.differentiableOn_f i).deriv (isOpen_nbhd _)).mono nbhd_subset_two
    have h2 : DifferentiableOn ℂ (fun z => h (Ψ.f i z)) (nbhd ε') :=
      hd.comp ((Ψ.differentiableOn_f i).mono nbhd_subset_two) (Ψ.mapsTo_f i)
    exact (h1.mul h2).add (hnl.mono (subset_closure.trans hU))
  · have hy := hfx x hx
    have hhy : ‖h (Ψ.f i x)‖ ≤ K := by
      rw [hy.1, ← Complex.abs_re_eq_norm.2 (hre _ hy.2)]
      exact abs_le.2 (hb _ hy.2)
    -- `0 ≤ c`, from the bound at `x`
    have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc i x hx)
    have hnorm : ‖Ψ.dualOp i h x‖ ≤ c * K + M := by
      simp only [dualOp]
      refine (norm_add_le _ _).trans (add_le_add ?_ (hM i x hx))
      rw [norm_mul]
      exact mul_le_mul (hc i x hx) hhy (norm_nonneg _) hc0
    exact abs_lt.1 ((Complex.abs_re_le_norm _).trans_lt (hnorm.trans_lt hK))

end IFS

/-- Two intersecting sets of diameter less than `δ/3`, one of them shifted by `τ` with
`|τ| ≥ δ`, are disjoint. -/
theorem disjoint_image_add_of_abs_sub_lt {A B : Set ℝ} {δ τ : ℝ}
    (hA : ∀ a ∈ A, ∀ a' ∈ A, |a - a'| < δ / 3) (hB : ∀ b ∈ B, ∀ b' ∈ B, |b - b'| < δ / 3)
    (hAB : (A ∩ B).Nonempty) (hτ : δ ≤ |τ|) : Disjoint ((· + τ) '' A) B := by
  obtain ⟨x, hxA, hxB⟩ := hAB
  have hδ : 0 < δ := by simpa using hA x hxA x hxA
  rw [Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ hb
  -- `a` and `a + τ` are both within `δ/3` of `x`, so `|τ| < 2δ/3`
  have h1 := hA a ha x hxA
  have h2 := hB (a + τ) hb x hxB
  have h3 : |τ| ≤ |a + τ - x| + |a - x| := by
    simpa using abs_sub (a + τ - x) (a - x)
  linarith

end AnalyticESC
