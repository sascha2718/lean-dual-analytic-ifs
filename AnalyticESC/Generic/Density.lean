module

public import AnalyticESC.Generic.Agreement
public import AnalyticESC.Generic.Bump
public import AnalyticESC.Generic.Points

@[expose] public section

/-!
# The density step of Theorem 1.4

The proof of Theorem 1.4 in Section 4.2, after the reduction by Lemma 4.2: an IFS whose maps send
`[0,1]` into `(0,1)` and whose compositions along distinct finite words differ on `[0,1]` has
arbitrarily `d₂`-close perturbations whose dual IFS satisfies the SSC.

The proof follows the paper with words of length `n + 1`, to match Lemma 2.5. The points of
Lemma 4.3 and their orbits are split, for each letter `ℓ`, into the set `𝒴_ℓ` of the points
`x_{i,j}` of the bad pairs with `i₁ = ℓ` and the set `𝒵_ℓ` of the remaining orbit points, and
Proposition 4.4 perturbs each map accordingly. The bound for `g_i''/g_i'` on `[0,1]` is
`M = 2 (B + C + 1) / c_min`, with `B` a bound for `f_i''/f_i'` and `C` the sum of the constants
of Proposition 4.4; it does not depend on `δ ≤ 1`.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace IFS

variable {N : ℕ} {ε ε' : ℝ}

/-! ## Orbits -/

/-- The point of index `m ≤ |w|` lies on the orbit `𝒪_w(t)`. -/
private theorem re_comp_take_mem_orbit (Φ : IFS N ε) {w : List (Fin N)} {m : ℕ}
    (hm : m ≤ w.length) (t : ℝ) : (Φ.comp (w.take m).reverse t).re ∈ Φ.orbit w t :=
  List.mem_map.2 ⟨m, List.mem_range.2 (Nat.lt_succ_of_le hm), rfl⟩

/-- The base point `t` is the first point of the orbit `𝒪_w(t)`. -/
private theorem self_mem_orbit (Φ : IFS N ε) (w : List (Fin N)) (t : ℝ) : t ∈ Φ.orbit w t := by
  simpa using Φ.re_comp_take_mem_orbit (Nat.zero_le w.length) t

/-- On an injective orbit, the points after the first differ from the base point. -/
private theorem re_comp_take_ne (Φ : IFS N ε) {w : List (Fin N)} {t : ℝ}
    (hnd : (Φ.orbit w t).Nodup) {m : ℕ} (h0 : 0 < m) (hm : m ≤ w.length) :
    (Φ.comp (w.take m).reverse t).re ≠ t := by
  intro h
  have := List.inj_on_of_nodup_map hnd (List.mem_range.2 (Nat.lt_succ_of_le hm))
    (List.mem_range.2 (Nat.succ_pos w.length)) (by simpa using h)
  omega

/-- The points of an orbit from a point of `I` lie in `I`. -/
private theorem mem_I_of_mem_orbit (Φ : IFS N ε) {w : List (Fin N)} {t y : ℝ} (ht : t ∈ I)
    (hy : y ∈ Φ.orbit w t) : y ∈ I := by
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hy
  exact Φ.re_comp_mem_I _ ht

/-! ## The point sets `𝒴_ℓ` and `𝒵_ℓ` -/

/-- The pairs of `ℬ_{n+1}` as a finite set. -/
private noncomputable def pairsFinset (N n : ℕ) :
    Finset ((Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N)) := by
  classical exact Finset.univ.filter (· ∈ pairs N (n + 1))

private theorem mem_pairsFinset {n : ℕ} {p : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N)} :
    p ∈ pairsFinset N n ↔ p ∈ pairs N (n + 1) := by
  simp [pairsFinset]

/-- A pair `(i, j)` is bad when `F_i(k,K)` and `F_j(k,K)` are not disjoint in the sense
of (2.2). -/
private def Bad (Φ : IFS N ε) (k K : ℝ) {n : ℕ} (p : (Fin n → Fin N) × (Fin n → Fin N)) :
    Prop :=
  ¬ Φ.DualCylDisjoint k K (List.ofFn p.1) (List.ofFn p.2)

/-- The union of the orbits `𝒪_i(x_{i,j}) ∪ 𝒪_j(x_{i,j})` over `(i, j) ∈ ℬ_{n+1}`. -/
private noncomputable def orbitPoints (Φ : IFS N ε) (n : ℕ)
    (x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ) : Finset ℝ := by
  classical exact (pairsFinset N n).biUnion fun p =>
    (Φ.orbit (List.ofFn p.1) (x p) ++ Φ.orbit (List.ofFn p.2) (x p)).toFinset

/-- The set `𝒴_ℓ`: the points `x_{i,j}` of the bad pairs `(i, j)` with `i₁ = ℓ`. -/
private noncomputable def badPoints (Φ : IFS N ε) (k K : ℝ) (n : ℕ)
    (x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ) (ℓ : Fin N) : Finset ℝ := by
  classical exact ((pairsFinset N n).filter fun p => Φ.Bad k K p ∧ p.1 0 = ℓ).image x

/-- The set `𝒵_ℓ`: the orbit points outside `𝒴_ℓ`. -/
private noncomputable def goodPoints (Φ : IFS N ε) (k K : ℝ) (n : ℕ)
    (x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ) (ℓ : Fin N) : Finset ℝ := by
  classical exact Φ.orbitPoints n x \ Φ.badPoints k K n x ℓ

private theorem mem_orbitPoints {Φ : IFS N ε} {n : ℕ}
    {x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ} {y : ℝ} :
    y ∈ Φ.orbitPoints n x ↔ ∃ p ∈ pairs N (n + 1),
      y ∈ Φ.orbit (List.ofFn p.1) (x p) ++ Φ.orbit (List.ofFn p.2) (x p) := by
  simp only [orbitPoints, Finset.mem_biUnion, List.mem_toFinset, mem_pairsFinset]

private theorem mem_badPoints {Φ : IFS N ε} {k K : ℝ} {n : ℕ}
    {x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ} {ℓ : Fin N} {y : ℝ} :
    y ∈ Φ.badPoints k K n x ℓ ↔
      ∃ p ∈ pairs N (n + 1), (Φ.Bad k K p ∧ p.1 0 = ℓ) ∧ x p = y := by
  simp only [badPoints, Finset.mem_image, Finset.mem_filter, mem_pairsFinset, and_assoc]

private theorem mem_goodPoints {Φ : IFS N ε} {k K : ℝ} {n : ℕ}
    {x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ} {ℓ : Fin N} {y : ℝ} :
    y ∈ Φ.goodPoints k K n x ℓ ↔ y ∈ Φ.orbitPoints n x ∧ y ∉ Φ.badPoints k K n x ℓ := by
  simp only [goodPoints, Finset.mem_sdiff]

/-- The conclusions of Lemma 4.3 for the points `x` and words of length `n + 1`, without the
condition that the two orbits of a pair meet only at the base point, which is not needed. -/
private structure IsPointChoice (Φ : IFS N ε) (k K : ℝ) (n : ℕ)
    (x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ) : Prop where
  mem_I : ∀ p ∈ pairs N (n + 1), x p ∈ I
  disjoint : ∀ p ∈ pairs N (n + 1), Φ.DualCylDisjoint k K (List.ofFn p.1) (List.ofFn p.2) →
    Disjoint (Φ.dualCylAt k K (List.ofFn p.1) (x p)) (Φ.dualCylAt k K (List.ofFn p.2) (x p))
  nodup_fst : ∀ p ∈ pairs N (n + 1), (Φ.orbit (List.ofFn p.1) (x p)).Nodup
  nodup_snd : ∀ p ∈ pairs N (n + 1), (Φ.orbit (List.ofFn p.2) (x p)).Nodup
  sep : ∀ p ∈ pairs N (n + 1), ∀ q ∈ pairs N (n + 1), p ≠ q →
    ∀ y ∈ Φ.orbit (List.ofFn p.1) (x p) ++ Φ.orbit (List.ofFn p.2) (x p),
      y ∉ Φ.orbit (List.ofFn q.1) (x q) ++ Φ.orbit (List.ofFn q.2) (x q)

namespace IsPointChoice

variable {Φ : IFS N ε} {k K : ℝ} {n : ℕ}
  {x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ}

/-- Distinct pairs have distinct points `x_{i,j}`. -/
private theorem eq_of_eq (hx : IsPointChoice Φ k K n x)
    {p q : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N)} (hp : p ∈ pairs N (n + 1))
    (hq : q ∈ pairs N (n + 1)) (h : x p = x q) : p = q := by
  by_contra hpq
  refine hx.sep p hp q hq hpq (x p) (List.mem_append_left _ (Φ.self_mem_orbit _ _)) ?_
  rw [h]
  exact List.mem_append_left _ (Φ.self_mem_orbit _ _)

/-- `x_{i,j} ∈ 𝒴_ℓ` exactly when `(i, j)` is bad and `i₁ = ℓ`. -/
private theorem mem_badPoints_iff (hx : IsPointChoice Φ k K n x)
    {p : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N)} (hp : p ∈ pairs N (n + 1)) (ℓ : Fin N) :
    x p ∈ Φ.badPoints k K n x ℓ ↔ Φ.Bad k K p ∧ p.1 0 = ℓ := by
  rw [mem_badPoints]
  constructor
  · rintro ⟨q, hq, hqb, hqx⟩
    rwa [← hx.eq_of_eq hq hp hqx]
  · exact fun h => ⟨p, hp, h, rfl⟩

/-- The orbit points of a pair other than its base point lie in every `𝒵_ℓ`. -/
private theorem mem_goodPoints_of_ne (hx : IsPointChoice Φ k K n x)
    {p : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N)} (hp : p ∈ pairs N (n + 1)) {y : ℝ}
    (hy : y ∈ Φ.orbit (List.ofFn p.1) (x p) ++ Φ.orbit (List.ofFn p.2) (x p)) (hne : y ≠ x p)
    (ℓ : Fin N) : y ∈ Φ.goodPoints k K n x ℓ := by
  refine mem_goodPoints.2 ⟨mem_orbitPoints.2 ⟨p, hp, hy⟩, fun hY => ?_⟩
  obtain ⟨q, hq, -, rfl⟩ := mem_badPoints.1 hY
  have hpq : p ≠ q := by
    rintro rfl
    exact hne rfl
  exact hx.sep p hp q hq hpq (x q) hy (List.mem_append_left _ (Φ.self_mem_orbit _ _))

/-- The base point `x_{i,j}` lies in `𝒵_ℓ` unless `(i, j)` is bad and `i₁ = ℓ`. -/
private theorem self_mem_goodPoints (hx : IsPointChoice Φ k K n x)
    {p : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N)} (hp : p ∈ pairs N (n + 1)) {ℓ : Fin N}
    (h : ¬ (Φ.Bad k K p ∧ p.1 0 = ℓ)) : x p ∈ Φ.goodPoints k K n x ℓ :=
  mem_goodPoints.2 ⟨mem_orbitPoints.2 ⟨p, hp, List.mem_append_left _ (Φ.self_mem_orbit _ _)⟩,
    fun hY => h ((hx.mem_badPoints_iff hp ℓ).1 hY)⟩

/-- The later points of the orbit of the first word of a pair lie in every `𝒵_ℓ`. -/
private theorem re_comp_fst_mem_goodPoints (hx : IsPointChoice Φ k K n x)
    {p : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N)} (hp : p ∈ pairs N (n + 1)) {m : ℕ}
    (h0 : 0 < m) (hm : m ≤ n + 1) (ℓ : Fin N) :
    (Φ.comp ((List.ofFn p.1).take m).reverse (x p)).re ∈ Φ.goodPoints k K n x ℓ := by
  have hm' : m ≤ (List.ofFn p.1).length := by rwa [List.length_ofFn]
  exact hx.mem_goodPoints_of_ne hp (List.mem_append_left _ (Φ.re_comp_take_mem_orbit hm' _))
    (Φ.re_comp_take_ne (hx.nodup_fst p hp) h0 hm') ℓ

/-- The later points of the orbit of the second word of a pair lie in every `𝒵_ℓ`. -/
private theorem re_comp_snd_mem_goodPoints (hx : IsPointChoice Φ k K n x)
    {p : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N)} (hp : p ∈ pairs N (n + 1)) {m : ℕ}
    (h0 : 0 < m) (hm : m ≤ n + 1) (ℓ : Fin N) :
    (Φ.comp ((List.ofFn p.2).take m).reverse (x p)).re ∈ Φ.goodPoints k K n x ℓ := by
  have hm' : m ≤ (List.ofFn p.2).length := by rwa [List.length_ofFn]
  exact hx.mem_goodPoints_of_ne hp (List.mem_append_right _ (Φ.re_comp_take_mem_orbit hm' _))
    (Φ.re_comp_take_ne (hx.nodup_snd p hp) h0 hm') ℓ

private theorem badPoints_subset_I (hx : IsPointChoice Φ k K n x) (ℓ : Fin N) :
    ∀ y ∈ Φ.badPoints k K n x ℓ, y ∈ I := by
  intro y hy
  obtain ⟨p, hp, -, rfl⟩ := mem_badPoints.1 hy
  exact hx.mem_I p hp

private theorem goodPoints_subset_I (hx : IsPointChoice Φ k K n x) (ℓ : Fin N) :
    ∀ y ∈ Φ.goodPoints k K n x ℓ, y ∈ I := by
  intro y hy
  obtain ⟨p, hp, hy⟩ := mem_orbitPoints.1 (mem_goodPoints.1 hy).1
  rcases List.mem_append.1 hy with hy | hy
  · exact Φ.mem_I_of_mem_orbit (hx.mem_I p hp) hy
  · exact Φ.mem_I_of_mem_orbit (hx.mem_I p hp) hy

end IsPointChoice

private theorem disjoint_badPoints_goodPoints (Φ : IFS N ε) (k K : ℝ) (n : ℕ)
    (x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ) (ℓ : Fin N) :
    Disjoint (Φ.badPoints k K n x ℓ) (Φ.goodPoints k K n x ℓ) :=
  Finset.disjoint_left.2 fun _ hY hZ => (mem_goodPoints.1 hZ).2 hY

/-! ## Agreement along orbits -/

/-- Agreement at a point of an orbit from a point of `I`, from agreement at the real points
of `𝒵_ℓ`. -/
private theorem agreeAt_comp (Φ : IFS N ε) (Ψ : IFS N ε') {Z : Fin N → Finset ℝ}
    (hZ : ∀ ℓ, ∀ z ∈ Z ℓ, AgreeAt (Φ.f ℓ) (Ψ.f ℓ) z) {t : ℝ} (ht : t ∈ I) {v : List (Fin N)}
    {ℓ : Fin N} (h : (Φ.comp v t).re ∈ Z ℓ) : AgreeAt (Φ.f ℓ) (Ψ.f ℓ) (Φ.comp v t) := by
  rw [Φ.comp_ofReal v ht]
  exact hZ ℓ _ h

/-- The orbit of `w` from `f_i(z)` is the tail of the orbit of `i w` from `z`. -/
private theorem comp_take_reverse_f (Φ : IFS N ε) (i : Fin N) (w : List (Fin N)) (m : ℕ)
    (z : ℂ) : Φ.comp (w.take m).reverse (Φ.f i z) = Φ.comp ((i :: w).take (m + 1)).reverse z := by
  rw [List.take_succ_cons, List.reverse_cons, Φ.comp_append]
  rfl

/-- If the points of the orbit of `w` from `t` lie in the sets `𝒵` of the corresponding letters,
the cylinder intervals of `Φ` and `Ψ` at `t` agree. -/
private theorem dualCylAt_eq_of_mem (Φ : IFS N ε) (Ψ : IFS N ε') {Z : Fin N → Finset ℝ}
    (hZ : ∀ ℓ, ∀ z ∈ Z ℓ, AgreeAt (Φ.f ℓ) (Ψ.f ℓ) z) (k K : ℝ) {w : List (Fin N)} {t : ℝ}
    (ht : t ∈ I) (h : ∀ m (hm : m < w.length), (Φ.comp (w.take m).reverse t).re ∈ Z w[m]) :
    Ψ.dualCylAt k K w t = Φ.dualCylAt k K w t :=
  dualCylAt_eq_of_agreeAt Φ Ψ k K fun m hm => agreeAt_comp Φ Ψ hZ ht (h m hm)

/-- If `g_i` agrees with `f_i` to first order at `t` and the later points of the orbit of `i w`
from `t` lie in the sets `𝒵` of the corresponding letters, the cylinder interval of `Ψ` at `t` is
that of `Φ` shifted by the change of `f_i''/f_i'` at `t`. -/
private theorem dualCylAt_cons_eq_of_mem (Φ : IFS N ε) (Ψ : IFS N ε') {Z : Fin N → Finset ℝ}
    (hZ : ∀ ℓ, ∀ z ∈ Z ℓ, AgreeAt (Φ.f ℓ) (Ψ.f ℓ) z) (k K : ℝ) {i : Fin N} {w : List (Fin N)}
    {t : ℝ} (ht : t ∈ I) (h0 : Ψ.f i t = Φ.f i t) (h1 : deriv (Ψ.f i) t = deriv (Φ.f i) t)
    (h : ∀ m (hm : m < w.length), (Φ.comp ((i :: w).take (m + 1)).reverse t).re ∈ Z w[m]) :
    Ψ.dualCylAt k K (i :: w) t =
      (· + (Ψ.nonlin i t - Φ.nonlin i t).re) '' Φ.dualCylAt k K (i :: w) t :=
  dualCylAt_cons_eq_of_agreeAt Φ Ψ k K h0 h1 fun m hm => by
    rw [comp_take_reverse_f]
    exact agreeAt_comp Φ Ψ hZ ht (h m hm)

/-- At a point of `I`, the change of `f_i''/f_i'` is real. -/
private theorem le_abs_re_nonlin_sub (Φ : IFS N ε) (Ψ : IFS N ε') (i : Fin N) {t : ℝ}
    (ht : t ∈ I) {δ : ℝ} (h : δ ≤ ‖Ψ.nonlin i t - Φ.nonlin i t‖) :
    δ ≤ |(Ψ.nonlin i t - Φ.nonlin i t).re| := by
  rwa [Complex.abs_re_eq_norm.2]
  rw [Complex.sub_im, Ψ.im_nonlin_ofReal i (ofReal_mem_nbhd Ψ.ε_pos ht),
    Φ.im_nonlin_ofReal i (ofReal_mem_nbhd Φ.ε_pos ht), sub_zero]

/-- The cylinders of a bad pair become disjoint after the shift. -/
private theorem disjoint_dualCylAt_of_not_disjoint (Φ : IFS N ε) (Ψ : IFS N ε')
    {Z : Fin N → Finset ℝ} (hZ : ∀ ℓ, ∀ z ∈ Z ℓ, AgreeAt (Φ.f ℓ) (Ψ.f ℓ) z) {k K δ : ℝ}
    (hkK : k ≤ K) {t : ℝ} (ht : t ∈ I) {i : Fin N} {u v : List (Fin N)}
    (hu : Φ.cmax ^ (u.length + 1) * (K - k) < δ / 3) (hv : Φ.cmax ^ v.length * (K - k) < δ / 3)
    (h0 : Ψ.f i t = Φ.f i t) (h1 : deriv (Ψ.f i) t = deriv (Φ.f i) t)
    (hτ : δ ≤ ‖Ψ.nonlin i t - Φ.nonlin i t‖)
    (hu' : ∀ m (hm : m < u.length), (Φ.comp ((i :: u).take (m + 1)).reverse t).re ∈ Z u[m])
    (hv' : ∀ m (hm : m < v.length), (Φ.comp (v.take m).reverse t).re ∈ Z v[m])
    (hbad : ¬ Disjoint (Φ.dualCylAt k K (i :: u) t) (Φ.dualCylAt k K v t)) :
    Disjoint (Ψ.dualCylAt k K (i :: u) t) (Ψ.dualCylAt k K v t) := by
  rw [dualCylAt_cons_eq_of_mem Φ Ψ hZ k K ht h0 h1 hu', dualCylAt_eq_of_mem Φ Ψ hZ k K ht hv']
  refine disjoint_image_add_of_abs_sub_lt (fun a ha a' ha' => ?_) (fun b hb b' hb' => ?_)
    (not_disjoint_iff_nonempty_inter.1 hbad) (le_abs_re_nonlin_sub Φ Ψ i ht hτ)
  · exact (Φ.abs_sub_le_cmax_pow_of_mem_dualCylAt hkK _ ht ha ha').trans_lt hu
  · exact (Φ.abs_sub_le_cmax_pow_of_mem_dualCylAt hkK _ ht hb hb').trans_lt hv

/-- The cylinders of `Ψ` of every pair of `ℬ_{n+1}` are disjoint, if `g_ℓ` agrees with `f_ℓ` to
second order on `𝒵_ℓ`, and to first order on `𝒴_ℓ` with a change of `f_ℓ''/f_ℓ'` by at least `δ`,
where the cylinder intervals are shorter than `δ / 3`. -/
private theorem IsPointChoice.dualCylDisjoint {Φ : IFS N ε} (Ψ : IFS N ε') {k K δ : ℝ}
    (hkK : k ≤ K) {n : ℕ} {x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ}
    (hx : IsPointChoice Φ k K n x) (hn : Φ.cmax ^ (n + 1) * (K - k) < δ / 3)
    (hY : ∀ ℓ, ∀ y ∈ Φ.badPoints k K n x ℓ, Ψ.f ℓ y = Φ.f ℓ y ∧
      deriv (Ψ.f ℓ) y = deriv (Φ.f ℓ) y ∧ δ ≤ ‖Ψ.nonlin ℓ y - Φ.nonlin ℓ y‖)
    (hZ : ∀ ℓ, ∀ z ∈ Φ.goodPoints k K n x ℓ, AgreeAt (Φ.f ℓ) (Ψ.f ℓ) z)
    {p : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N)} (hp : p ∈ pairs N (n + 1)) :
    Ψ.DualCylDisjoint k K (List.ofFn p.1) (List.ofFn p.2) := by
  have ht := hx.mem_I p hp
  refine ⟨x p, ht, ?_⟩
  -- the orbit of the second word, with its base point in `𝒵_{j₁}`
  have hsnd : x p ∈ Φ.goodPoints k K n x (p.2 0) →
      ∀ m (hm : m < (List.ofFn p.2).length),
        (Φ.comp ((List.ofFn p.2).take m).reverse (x p)).re ∈
          Φ.goodPoints k K n x (List.ofFn p.2)[m] := by
    intro h0 m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simpa using h0
    · exact hx.re_comp_snd_mem_goodPoints hp hm0 (by simpa using hm.le) _
  by_cases hb : Φ.Bad k K p
  · -- a bad pair: `x_{i,j} ∈ 𝒴_{i₁}` and `x_{i,j} ∈ 𝒵_{j₁}`
    obtain ⟨h0, h1, hτ⟩ := hY _ _ ((hx.mem_badPoints_iff hp _).2 ⟨hb, rfl⟩)
    have hZ0 : x p ∈ Φ.goodPoints k K n x (p.2 0) := by
      have hlt : p.1 0 < p.2 0 := by
        obtain ⟨_, h⟩ := hp
        exact h
      exact hx.self_mem_goodPoints hp fun h => hlt.ne h.2
    have hbad : ¬ Disjoint (Φ.dualCylAt k K (List.ofFn p.1) (x p))
        (Φ.dualCylAt k K (List.ofFn p.2) (x p)) := fun hd => hb ⟨x p, ht, hd⟩
    rw [List.ofFn_succ (f := p.1)] at hbad ⊢
    refine disjoint_dualCylAt_of_not_disjoint Φ Ψ hZ hkK ht (by simpa using hn)
      (by simpa using hn) h0 h1 hτ (fun m hm => ?_) (hsnd hZ0) hbad
    rw [← List.ofFn_succ]
    rw [List.length_ofFn] at hm
    exact hx.re_comp_fst_mem_goodPoints hp (Nat.succ_pos m) (by omega) _
  · -- a pair that is not bad: all orbit points lie in `𝒵`
    have hZ0 : ∀ ℓ, x p ∈ Φ.goodPoints k K n x ℓ :=
      fun ℓ => hx.self_mem_goodPoints hp fun h => hb h.1
    have hfst : ∀ m (hm : m < (List.ofFn p.1).length),
        (Φ.comp ((List.ofFn p.1).take m).reverse (x p)).re ∈
          Φ.goodPoints k K n x (List.ofFn p.1)[m] := by
      intro m hm
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simpa using hZ0 (List.ofFn p.1)[0]
      · exact hx.re_comp_fst_mem_goodPoints hp hm0 (by simpa using hm.le) _
    rw [dualCylAt_eq_of_mem Φ Ψ hZ k K ht hfst, dualCylAt_eq_of_mem Φ Ψ hZ k K ht (hsnd (hZ0 _))]
    exact hx.disjoint p hp (not_not.1 hb)

/-! ## Bounds for the perturbation -/

/-- A choice of `δ`. -/
private theorem exists_delta {a b C r : ℝ} (ha : 0 < a) (hb : 0 < b) (hC : 0 ≤ C) (hr : 0 < r) :
    ∃ δ > 0, δ ≤ 1 ∧ δ ≤ a ∧ δ ≤ b ∧ (C + 3) * δ < r := by
  have hr' : 0 < r / (2 * (C + 3)) := div_pos hr (by linarith)
  refine ⟨min (min 1 a) (min b (r / (2 * (C + 3)))), by positivity,
    (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
    (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  calc (C + 3) * min (min 1 a) (min b (r / (2 * (C + 3))))
      ≤ (C + 3) * (r / (2 * (C + 3))) :=
        mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
    _ = r / 2 := by field_simp
    _ < r := by linarith

/-- A bound for `b'/a'` when `a'` and `b'` are close to `a` and `b`, with `|a| ≥ m`. -/
private theorem norm_div_le_of_close {a b a' b' : ℂ} {m B C δ : ℝ} (hm : 0 < m) (ha : m ≤ ‖a‖)
    (hb : ‖b‖ ≤ B) (ha' : ‖a' - a‖ < δ) (hb' : ‖b' - b‖ < C * δ + δ) (hδm : δ ≤ m / 2)
    (hδ1 : δ ≤ 1) (hC : 0 ≤ C) : ‖b' / a'‖ ≤ 2 * (B + C + 1) / m := by
  have h1 : m / 2 ≤ ‖a'‖ := by
    have := norm_sub_norm_le a a'
    rw [norm_sub_rev] at this
    linarith
  have h2 : ‖b'‖ ≤ B + C + 1 := by
    have := norm_sub_norm_le b' b
    have : C * δ ≤ C := mul_le_of_le_one_right hC hδ1
    linarith
  rw [norm_div, div_le_div_iff₀ (by linarith) hm]
  nlinarith [norm_nonneg b']

/-- `|f_i''| ≤ B` on `cl B_ε` if `|f_i''/f_i'| ≤ B` there. -/
private theorem norm_deriv_deriv_le (Φ : IFS N ε) {B : ℝ}
    (hB : ∀ i, ∀ z ∈ closure (nbhd ε), ‖Φ.nonlin i z‖ ≤ B) (i : Fin N) {z : ℂ}
    (hz : z ∈ closure (nbhd ε)) : ‖deriv (deriv (Φ.f i)) z‖ ≤ B := by
  have hne := (Φ.inClass i).deriv_ne_zero z hz
  have h : deriv (deriv (Φ.f i)) z = Φ.nonlin i z * deriv (Φ.f i) z :=
    (div_mul_cancel₀ _ hne).symm
  have h1 := Φ.norm_deriv_le_cmax i hz
  have h2 := Φ.cmax_lt_one
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB i z hz)
  rw [h, norm_mul]
  calc ‖Φ.nonlin i z‖ * ‖deriv (Φ.f i) z‖ ≤ B * 1 :=
        mul_le_mul (hB i z hz) (by linarith) (norm_nonneg _) hB0
    _ = B := mul_one B

/-- The `d₂` distance from bounds on the three differences on `I`. -/
private theorem d2_le (hN : 0 < N) (Φ : IFS N ε) (Ψ : IFS N ε') {a b e : ℝ}
    (h0 : ∀ i, ∀ x ∈ I, ‖Ψ.f i x - Φ.f i x‖ ≤ a)
    (h1 : ∀ i, ∀ x ∈ I, ‖deriv (Ψ.f i) x - deriv (Φ.f i) x‖ ≤ b)
    (h2 : ∀ i, ∀ x ∈ I, ‖deriv (deriv (Ψ.f i)) x - deriv (deriv (Φ.f i)) x‖ ≤ e) :
    d2 Φ Ψ ≤ a + b + e := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : Nonempty I := ⟨⟨0, left_mem_Icc.2 zero_le_one⟩⟩
  refine ciSup_le fun i => add_le_add (add_le_add ?_ ?_) ?_
  · exact ciSup_le fun x => by rw [norm_sub_rev]; exact h0 i x x.2
  · exact ciSup_le fun x => by rw [norm_sub_rev]; exact h1 i x x.2
  · exact ciSup_le fun x => by rw [norm_sub_rev]; exact h2 i x x.2

/-! ## The density step -/

/-- The density step in the proof of Theorem 1.4. -/
theorem exists_dualSSC_near (hN : 0 < N) (Φ : IFS N ε)
    (hI : ∀ i, ∀ x ∈ I, (Φ.f i x).re ∈ Ioo 0 1) (hnc : Φ.NoCoincidence) {r : ℝ} (hr : 0 < r) :
    ∃ ε' : ℝ, ∃ Ψ : IFS N ε', d2 Φ Ψ < r ∧ Ψ.DualSSC := by
  -- the constants of Proposition 4.4 and their sum `C`
  choose C₀ hC₀ hbump using fun i => proposition_4_4 Φ.ε_pos (Φ.inClass i) (hI i)
  set C := ∑ i, C₀ i with hC_def
  have hCle : ∀ i, C₀ i ≤ C := fun i =>
    Finset.single_le_sum (f := C₀) (fun j _ => (hC₀ j).le) (Finset.mem_univ i)
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ => (hC₀ j).le
  -- the bounds `B` for `f_i''/f_i'` and `c_max`, `c_min` for `f_i'`
  obtain ⟨B, hB0, hB⟩ := Φ.exists_nonlin_bound
  have hc1 := Φ.cmax_lt_one
  have hc0 := Φ.cmax_nonneg
  have hm := Φ.cmin_pos hN
  obtain ⟨δ, hδ, hδ1, hδc, hδm, hδr⟩ :=
    exists_delta (a := (1 - Φ.cmax) / 2) (b := Φ.cmin / 2) (by linarith) (by linarith) hC hr
  -- the cylinder `(-K, K)`
  set M := 2 * (B + C + 1) / Φ.cmin with hM_def
  set c' := (1 + Φ.cmax) / 2 with hc'_def
  set K := M / (1 - c') + 1 with hK_def
  have hM0 : 0 ≤ M := div_nonneg (by linarith) hm.le
  have hc'1 : 0 < 1 - c' := by rw [hc'_def]; linarith
  have hK0 : 0 < K := by
    have : 0 ≤ M / (1 - c') := div_nonneg hM0 hc'1.le
    linarith
  have hK : c' * K + M < K := by
    have h1 : (1 - c') * (M / (1 - c')) = M := mul_div_cancel₀ M hc'1.ne'
    have h2 : c' * K + M = K - (1 - c') := by rw [hK_def]; linear_combination -h1
    linarith
  have hkK : -K ≤ K := by linarith
  -- the length `n + 1` of the words
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Φ.cmax ^ (n + 1) * (K - -K) < δ / 3 := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
      (show 0 < δ / 3 / (K - -K) from div_pos (by linarith) (by linarith)) hc1
    refine ⟨n, ?_⟩
    rw [lt_div_iff₀ (by linarith)] at hn
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hc0 hc1.le (Nat.le_succ n))
      (by linarith)).trans_lt hn
  -- the points of Lemma 4.3
  obtain ⟨x, hxI, hxd, hxo, hxs⟩ := Φ.lemma_4_3 (n + 1) (-K) K hnc
  have hx : IsPointChoice Φ (-K) K n x :=
    ⟨hxI, hxd, fun p hp => (hxo p hp).1, fun p hp => (hxo p hp).2.1, hxs⟩
  -- the perturbation of Proposition 4.4
  choose g hg using fun i => hbump i (Φ.badPoints (-K) K n x i) (Φ.goodPoints (-K) K n x i)
    (hx.badPoints_subset_I i) (hx.goodPoints_subset_I i)
    (Φ.disjoint_badPoints_goodPoints (-K) K n x i) δ hδ δ hδ
  obtain ⟨ε', hε', hgε'⟩ := exists_inClass_forall fun i => (hg i).1
  obtain ⟨Ψ, rfl⟩ : ∃ Ψ : IFS N ε', Ψ.f = g := ⟨⟨g, hε', hgε'⟩, rfl⟩
  refine ⟨ε', Ψ, ?_, ?_⟩
  · -- `d₂(Φ, Ψ) ≤ (C + 3) δ < r`
    refine lt_of_le_of_lt (d2_le hN Φ Ψ (a := δ) (b := δ) (e := C * δ + δ)
      (fun i y hy => ((hg i).2.2.2.2.1 y hy).le) (fun i y hy => ((hg i).2.2.2.2.2.1 y hy).le)
      (fun i y hy => ((hg i).2.2.2.2.2.2 y hy).le.trans ?_)) ?_
    · linarith [mul_le_mul_of_nonneg_right (hCle i) hδ.le]
    · linarith
  -- `Ψ*` satisfies the SSC by Lemma 2.5
  have hderiv : ∀ i, ∀ y ∈ I, ‖deriv (Ψ.f i) y‖ ≤ c' := by
    intro i y hy
    have h1 := Φ.norm_deriv_le_cmax i (subset_closure (ofReal_mem_nbhd Φ.ε_pos hy))
    have h2 := (hg i).2.2.2.2.2.1 y hy
    have h3 := norm_sub_norm_le (deriv (Ψ.f i) y) (deriv (Φ.f i) y)
    rw [hc'_def]
    linarith
  have hnonlin : ∀ i, ∀ y ∈ I, ‖Ψ.nonlin i y‖ ≤ M := by
    intro i y hy
    have hy' : (y : ℂ) ∈ closure (nbhd ε) := subset_closure (ofReal_mem_nbhd Φ.ε_pos hy)
    refine norm_div_le_of_close hm (Φ.cmin_le_norm_deriv i hy') (Φ.norm_deriv_deriv_le hB i hy')
      ((hg i).2.2.2.2.2.1 y hy) (((hg i).2.2.2.2.2.2 y hy).trans_le ?_) hδm hδ1 hC
    linarith [mul_le_mul_of_nonneg_right (hCle i) hδ.le]
  have hY : ∀ ℓ, ∀ y ∈ Φ.badPoints (-K) K n x ℓ, Ψ.f ℓ y = Φ.f ℓ y ∧
      deriv (Ψ.f ℓ) y = deriv (Φ.f ℓ) y ∧ δ ≤ ‖Ψ.nonlin ℓ y - Φ.nonlin ℓ y‖ :=
    fun ℓ y hy => ⟨((hg ℓ).2.1 y (Finset.mem_union_left _ hy)).1,
      ((hg ℓ).2.1 y (Finset.mem_union_left _ hy)).2, (hg ℓ).2.2.2.1 y hy⟩
  have hZ : ∀ ℓ, ∀ z ∈ Φ.goodPoints (-K) K n x ℓ, AgreeAt (Φ.f ℓ) (Ψ.f ℓ) z :=
    fun ℓ z hz => ⟨((hg ℓ).2.1 z (Finset.mem_union_right _ hz)).1,
      ((hg ℓ).2.1 z (Finset.mem_union_right _ hz)).2, (hg ℓ).2.2.1 z hz⟩
  refine (Ψ.lemma_2_5 hN).1.2 ⟨-K, K, by linarith, n,
    fun i => Ψ.mapsTo_dualOp_dualCylClosed_of_le hderiv hnonlin hK i, fun i j hij => ?_⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact hx.dualCylDisjoint Ψ hkK hn hY hZ (p := (i, j)) ⟨Nat.succ_pos n, h⟩
  · obtain ⟨t, ht, hd⟩ := hx.dualCylDisjoint Ψ hkK hn hY hZ (p := (j, i)) ⟨Nat.succ_pos n, h⟩
    exact ⟨t, ht, hd.symm⟩

end IFS

end AnalyticESC
