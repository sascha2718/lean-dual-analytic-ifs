module

public import AnalyticESC.Conjugation.Basic

@[expose] public section

/-!
# Conjugacies by injective analytic maps

Two facts about an analytic map `g` that is injective on `[0,1]` and conjugates contractions of
`[0,1]` to affine maps: `g'` has no zero in `[0,1]` once two of the maps have distinct fixed
points, and maps with a common fixed point commute.
-/

namespace AnalyticESC

open Set Filter Topology

/-- The derivative of an analytic map injective on `[0,1]` has finitely many zeros there. -/
theorem finite_zeros_deriv {g : ℝ → ℝ} (hg : AnalyticOnNhd ℝ g I) (hinj : InjOn g I) :
    {x | x ∈ I ∧ deriv g x = 0}.Finite := by
  by_contra hinf
  obtain ⟨x₀, hx₀, hacc⟩ :=
    Set.Infinite.exists_accPt_of_subset_isCompact hinf isCompact_Icc fun x hx => hx.1
  have hd : AnalyticOnNhd ℝ (deriv g) I := fun x hx => (hg x hx).deriv
  have hfreq : ∃ᶠ z in 𝓝[≠] x₀, deriv g z = 0 :=
    (accPt_iff_frequently_nhdsNE.1 hacc).mono fun z hz => hz.2
  -- By the identity theorem, `g'` vanishes on `[0,1]`, so `g` is constant there.
  have hzero : EqOn (deriv g) 0 I :=
    hd.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_Icc hx₀ hfreq
  have hconst : ∀ x ∈ Icc (0 : ℝ) 1, g x = g 0 := by
    apply constant_of_derivWithin_zero
    · exact fun x hx => (hg x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      have hxI : x ∈ I := Ico_subset_Icc_self hx
      rw [(hg x hxI).differentiableAt.derivWithin (uniqueDiffOn_Icc zero_lt_one x hxI)]
      exact hzero hxI
  have h01 := hinj (right_mem_Icc.2 zero_le_one) (left_mem_Icc.2 zero_le_one)
    (hconst 1 (right_mem_Icc.2 zero_le_one))
  exact one_ne_zero h01

/-- A distance not exceeding `c < 1` times itself vanishes. -/
private lemma eq_of_abs_sub_le_mul {c x y : ℝ} (hc : c < 1) (h : |x - y| ≤ c * |x - y|) :
    x = y := by
  have h0 : 0 ≤ |x - y| := abs_nonneg _
  have h1 : |x - y| = 0 := by nlinarith
  exact sub_eq_zero.mp (abs_eq_zero.mp h1)

/-- Differentiating `g ∘ F = λ g + t` on `[0,1]` at a point of `[0,1]`. -/
private lemma deriv_comp_eq_of_conj {F g : ℝ → ℝ} {lam t x : ℝ} (hx : x ∈ I)
    (hF : DifferentiableAt ℝ F x) (hg : DifferentiableAt ℝ g x)
    (hgF : DifferentiableAt ℝ g (F x)) (hconj : ∀ y ∈ I, g (F y) = lam * g y + t) :
    deriv g (F x) * deriv F x = lam * deriv g x := by
  have h1 : HasDerivAt (g ∘ F) (deriv g (F x) * deriv F x) x :=
    hgF.hasDerivAt.comp x hF.hasDerivAt
  have h2 : HasDerivAt (fun y => lam * g y + t) (lam * deriv g x) x :=
    (hg.hasDerivAt.const_mul lam).add_const t
  have h1' : HasDerivWithinAt (fun y => lam * g y + t) (deriv g (F x) * deriv F x) I x :=
    h1.hasDerivWithinAt.congr_of_mem (fun y hy => (hconj y hy).symm) hx
  exact (uniqueDiffOn_Icc zero_lt_one x hx).eq_deriv _ h1' h2.hasDerivWithinAt

/-- If an analytic `g`, injective on `[0,1]`, conjugates contractions `F_k` of `[0,1]` with nonzero
derivative to affine maps, and two of the `F_k` have distinct fixed points, then `g'` has no zero
in `[0,1]`. -/
theorem deriv_ne_zero_of_conj {M : ℕ} {F : Fin M → ℝ → ℝ} {g : ℝ → ℝ} {c : ℝ} (hc : c < 1)
    (hmaps : ∀ k, MapsTo (F k) I I) (hlip : ∀ k, ∀ x ∈ I, ∀ y ∈ I, |F k x - F k y| ≤ c * |x - y|)
    (hdiff : ∀ k, ∀ x ∈ I, DifferentiableAt ℝ (F k) x) (hderiv : ∀ k, ∀ x ∈ I, deriv (F k) x ≠ 0)
    (hg : AnalyticOnNhd ℝ g I) (hinj : InjOn g I) {lam t : Fin M → ℝ}
    (hconj : ∀ k, ∀ x ∈ I, g (F k x) = lam k * g x + t k) {k l : Fin M} {p q : ℝ} (hp : p ∈ I)
    (hq : q ∈ I) (hFp : F k p = p) (hFq : F l q = q) (hpq : p ≠ q) :
    ∀ x ∈ I, deriv g x ≠ 0 := by
  intro z hz hgz
  set Z := {x | x ∈ I ∧ deriv g x = 0}
  have hZfin : Z.Finite := finite_zeros_deriv hg hinj
  have hzZ : z ∈ Z := ⟨hz, hgz⟩
  -- `c ≥ 0`, as `F k` does not increase the positive distance `|p - q|` beyond `c |p - q|`.
  have hc0 : 0 ≤ c := by
    have h := hlip k p hp q hq
    have hpos : 0 < |p - q| := abs_pos.2 (sub_ne_zero.2 hpq)
    nlinarith [abs_nonneg (F k p - F k q)]
  -- Each `F j` maps `Z` into `Z`.
  have hinv : ∀ j, MapsTo (F j) Z Z := by
    intro j x hx
    refine ⟨hmaps j hx.1, ?_⟩
    have hid := deriv_comp_eq_of_conj hx.1 (hdiff j x hx.1) (hg x hx.1).differentiableAt
      (hg _ (hmaps j hx.1)).differentiableAt (hconj j)
    rw [hx.2, mul_zero] at hid
    exact (mul_eq_zero.1 hid).resolve_right (hderiv j x hx.1)
  -- `λ_k ≠ 0`: otherwise `F k` is constant on `[0,1]` and has zero derivative at `1/2`.
  have hlam : lam k ≠ 0 := by
    intro h0
    have hcst : ∀ x ∈ I, F k x = F k 0 := by
      intro x hx
      refine hinj (hmaps k hx) (hmaps k (left_mem_Icc.2 zero_le_one)) ?_
      rw [hconj k x hx, hconj k 0 (left_mem_Icc.2 zero_le_one), h0, zero_mul, zero_mul]
    have hhalf : (1 / 2 : ℝ) ∈ I := ⟨by norm_num, by norm_num⟩
    have hev : F k =ᶠ[𝓝 (1 / 2 : ℝ)] fun _ => F k 0 := by
      filter_upwards [Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)] with x hx
      exact hcst x (Ioo_subset_Icc_self hx)
    exact hderiv k _ hhalf (by rw [hev.deriv_eq, deriv_const])
  -- `F k` is injective on `[0,1]`, hence a bijection of the finite set `Z`.
  have hFinj : InjOn (F k) Z := by
    intro x hx y hy hxy
    have h := congrArg g hxy
    rw [hconj k x hx.1, hconj k y hy.1] at h
    exact hinj hx.1 hy.1 (mul_left_cancel₀ hlam (add_right_cancel h))
  have hbij : BijOn (F k) Z Z := (hZfin.injOn_iff_bijOn_of_mapsTo (hinv k)).1 hFinj
  -- The diameter of `Z` is attained at a pair whose preimage pair shows it is at most `c` times
  -- itself, so `Z` is a single point.
  obtain ⟨⟨a, b⟩, hab, hmax⟩ := Set.exists_max_image (Z ×ˢ Z) (fun u => |u.1 - u.2|)
    (hZfin.prod hZfin) ⟨(z, z), hzZ, hzZ⟩
  obtain ⟨a', ha', rfl⟩ := hbij.surjOn hab.1
  obtain ⟨b', hb', rfl⟩ := hbij.surjOn hab.2
  have hdiam : F k a' = F k b' := by
    refine eq_of_abs_sub_le_mul hc ((hlip k a' ha'.1 b' hb'.1).trans ?_)
    exact mul_le_mul_of_nonneg_left (hmax (a', b') ⟨ha', hb'⟩) hc0
  have hsub : ∀ u ∈ Z, ∀ v ∈ Z, u = v := by
    intro u hu v hv
    have h := hmax (u, v) ⟨hu, hv⟩
    simp only [hdiam, sub_self, abs_zero] at h
    exact sub_eq_zero.mp (abs_nonpos_iff.mp h)
  -- Both fixed points coincide with the unique point `z` of `Z`.
  have hzp : p = z := by
    have hFz : F k z = z := hsub _ (hinv k hzZ) _ hzZ
    refine eq_of_abs_sub_le_mul hc ?_
    simpa only [hFp, hFz] using hlip k p hp z hz
  have hzq : q = z := by
    have hFz : F l z = z := hsub _ (hinv l hzZ) _ hzZ
    refine eq_of_abs_sub_le_mul hc ?_
    simpa only [hFq, hFz] using hlip l q hq z hz
  exact hpq (hzp.trans hzq.symm)

/-- Two maps of `[0,1]` with a common fixed point that are conjugated by an injective `g` to
affine maps commute on `[0,1]`. -/
theorem comp_comm_of_conj {F G g : ℝ → ℝ} (hinj : InjOn g I) (hF : MapsTo F I I)
    (hG : MapsTo G I I) {a b s t : ℝ} (hgF : ∀ x ∈ I, g (F x) = a * g x + s)
    (hgG : ∀ x ∈ I, g (G x) = b * g x + t) {p : ℝ} (hp : p ∈ I) (hFp : F p = p) (hGp : G p = p) :
    ∀ x ∈ I, F (G x) = G (F x) := by
  intro x hx
  have hs : g p = a * g p + s := by simpa only [hFp] using hgF p hp
  have ht : g p = b * g p + t := by simpa only [hGp] using hgG p hp
  refine hinj (hF (hG hx)) (hG (hF hx)) ?_
  rw [hgF _ (hG hx), hgG _ (hF hx), hgG x hx, hgF x hx]
  linear_combination (1 - a) * ht - (1 - b) * hs
