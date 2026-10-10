module

public import AnalyticESC.Dual.Attractor
public import AnalyticESC.Separation

@[expose] public section

/-!
# Lemma 4.1

For a system whose compositions along distinct finite words differ on `[0,1]`, a choice of
points `x_{i,j}`, `(i, j) ∈ ℬ_n`, at which the cylinders of pairs that are not bad are disjoint,
with orbits that are injective, meet only at the base point, and are disjoint for different
pairs. Systems without exact overlaps satisfy the hypothesis.

The points are chosen one pair at a time, by induction over finite sets of pairs. At each step
the admissible points form an infinite subset of `I` (all of `I` for a bad pair, a relative
neighbourhood of a point of disjointness otherwise), and the excluded points are finite: by the
identity theorem two distinct compositions agree at finitely many points of `I`, and each
composition is injective on `I`.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-! ## Compositions on `I` -/

/-- Two compositions along distinct words agree at finitely many points of `I`. -/
private theorem finite_eq_comp (h : Φ.NoCoincidence) {v w : List (Fin N)} (hvw : v ≠ w) :
    {t : ℝ | t ∈ I ∧ (Φ.comp v t).re = (Φ.comp w t).re}.Finite := by
  obtain ⟨x, hx, hne⟩ := h v w hvw
  refine (finite_zeros Φ.ε_pos ((Φ.differentiableOn_comp v).sub (Φ.differentiableOn_comp w))
    ⟨x, hx, sub_ne_zero.2 hne⟩).subset ?_
  rintro t ⟨ht, heq⟩
  refine ⟨ht, ?_⟩
  show Φ.comp v t - Φ.comp w t = 0
  rw [Φ.comp_ofReal v ht, Φ.comp_ofReal w ht, heq, sub_self]

/-- A composition takes each value at most once on `I`. -/
private theorem finite_comp_eq (w : List (Fin N)) (y : ℝ) :
    {t : ℝ | t ∈ I ∧ (Φ.comp w t).re = y}.Finite :=
  Set.Subsingleton.finite fun _ ha _ hb => Φ.injOn_re_comp w ha.1 hb.1 (ha.2.trans hb.2.symm)

/-- The exceptional points of `I`: two distinct compositions of length at most `n` agree there,
or one of them takes a value in the finite set `F`. -/
private theorem finite_exceptional (h : Φ.NoCoincidence) (n : ℕ) {F : Set ℝ}
    (hF : F.Finite) :
    {t : ℝ | t ∈ I ∧ ((∃ v w : List (Fin N), v.length ≤ n ∧ w.length ≤ n ∧ v ≠ w ∧
      (Φ.comp v t).re = (Φ.comp w t).re) ∨
      ∃ v : List (Fin N), v.length ≤ n ∧ (Φ.comp v t).re ∈ F)}.Finite := by
  have hW := List.finite_length_le (Fin N) n
  refine ((hW.biUnion fun v _ => hW.biUnion fun w _ =>
      Set.finite_iUnion fun hvw : v ≠ w => Φ.finite_eq_comp h hvw).union
    (hW.biUnion fun v _ => hF.biUnion fun y _ => Φ.finite_comp_eq v y)).subset ?_
  rintro t ⟨ht, ⟨v, w, hv, hw, hvw, heq⟩ | ⟨v, hv, hvF⟩⟩
  · exact Or.inl (mem_biUnion hv (mem_biUnion hw (mem_iUnion_of_mem hvw ⟨ht, heq⟩)))
  · exact Or.inr (mem_biUnion hv (mem_biUnion hvF ⟨ht, rfl⟩))

/-! ## Disjointness of the cylinders near a point -/

private theorem disjoint_uIcc_iff {a b c d : ℝ} :
    Disjoint (uIcc a b) (uIcc c d) ↔ max a b < min c d ∨ max c d < min a b := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    exact Set.disjoint_left.1 h
      (show max (min a b) (min c d) ∈ uIcc a b from ⟨le_max_left _ _, max_le min_le_max h1⟩)
      (show max (min a b) (min c d) ∈ uIcc c d from ⟨le_max_right _ _, max_le h2 min_le_max⟩)
  · rintro (h | h)
    · refine Set.disjoint_left.2 fun x hx hx' => ?_
      exact absurd (hx.2.trans_lt (h.trans_le hx'.1)) (lt_irrefl x)
    · refine Set.disjoint_left.2 fun x hx hx' => ?_
      exact absurd (hx'.2.trans_lt (h.trans_le hx.1)) (lt_irrefl x)

/-- The endpoints `(F_w c)(t)` of the cylinders depend continuously on `t ∈ I`. -/
private theorem continuousOn_dualComp_const (w : List (Fin N)) (c : ℝ) :
    ContinuousOn (fun t : ℝ => (Φ.dualComp w (fun _ => (c : ℂ)) t).re) I := by
  have hg : ContinuousOn (fun z => deriv (Φ.comp w.reverse) z * c + Φ.dualProj (.fin w) z)
      (nbhd ε) :=
    ((((Φ.differentiableOn_comp w.reverse).deriv (isOpen_nbhd ε)).continuousOn).mul
      continuousOn_const).add (Φ.differentiableOn_dualProj (.fin w)).continuousOn
  have hg' : ContinuousOn
      (fun t : ℝ => (deriv (Φ.comp w.reverse) t * c + Φ.dualProj (.fin w) t).re) I :=
    Complex.continuous_re.comp_continuousOn
      (hg.comp Complex.continuous_ofReal.continuousOn fun t ht => ofReal_mem_nbhd Φ.ε_pos ht)
  refine hg'.congr fun t ht => ?_
  simp only
  rw [Φ.dualComp_apply w _ (ofReal_mem_nbhd Φ.ε_pos ht)]

/-- A relative neighbourhood in `I` of a point of `I` is infinite. -/
private theorem infinite_of_mem_nhdsWithin_I {S : Set ℝ} {x : ℝ} (hx : x ∈ I)
    (hS : S ∈ 𝓝[I] x) : (S ∩ I).Infinite := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhdsWithin_iff.1 hS
  have hlt : max (x - r / 2) 0 < min (x + r / 2) 1 := by
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨by linarith, by linarith [hx.2]⟩, by linarith [hx.1], zero_lt_one⟩
  refine (Set.Icc_infinite hlt).mono fun t ht => ?_
  have h1 : t ∈ I := ⟨(le_max_right _ _).trans ht.1, ht.2.trans (min_le_right _ _)⟩
  refine ⟨hsub ⟨?_, h1⟩, h1⟩
  have := (le_max_left _ _).trans ht.1
  have := ht.2.trans (min_le_left _ _)
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- The points of `I` at which the cylinders are disjoint, if they are disjoint at some point,
form an infinite set. -/
private theorem infinite_good (k K : ℝ) (a b : List (Fin N)) :
    {t : ℝ | t ∈ I ∧ (Φ.DualCylDisjoint k K a b →
      Disjoint (Φ.dualCylAt k K a t) (Φ.dualCylAt k K b t))}.Infinite := by
  by_cases hd : Φ.DualCylDisjoint k K a b
  · obtain ⟨x, hx, hdx⟩ := hd
    have hc : ∀ (w : List (Fin N)) (c : ℝ),
        Tendsto (fun t : ℝ => (Φ.dualComp w (fun _ => (c : ℂ)) t).re) (𝓝[I] x)
          (𝓝 (Φ.dualComp w (fun _ => (c : ℂ)) x).re) :=
      fun w c => Φ.continuousOn_dualComp_const w c x hx
    have hev : ∀ᶠ t in 𝓝[I] x, Disjoint (Φ.dualCylAt k K a t) (Φ.dualCylAt k K b t) := by
      unfold dualCylAt at hdx ⊢
      simp_rw [disjoint_uIcc_iff] at hdx ⊢
      rcases hdx with h1 | h1
      · exact (((hc a k).max (hc a K)).eventually_lt ((hc b k).min (hc b K)) h1).mono
          fun t ht => Or.inl ht
      · exact (((hc b k).max (hc b K)).eventually_lt ((hc a k).min (hc a K)) h1).mono
          fun t ht => Or.inr ht
    exact (infinite_of_mem_nhdsWithin_I hx hev).mono fun t ht => ⟨ht.2, fun _ => ht.1⟩
  · exact (Set.Icc_infinite zero_lt_one).mono fun t ht => ⟨ht, fun h' => absurd h' hd⟩

/-! ## Orbits -/

private theorem mem_orbit {w : List (Fin N)} {t y : ℝ} :
    y ∈ Φ.orbit w t ↔ ∃ l ≤ w.length, (Φ.comp (w.take l).reverse t).re = y := by
  simp only [orbit, List.mem_map, List.mem_range, Nat.lt_succ_iff]

private theorem take_reverse_ne_of_ne {w : List (Fin N)} {l l' : ℕ} (hl : l ≤ w.length)
    (hl' : l' ≤ w.length) (hne : l ≠ l') : (w.take l).reverse ≠ (w.take l').reverse := by
  intro he
  have := congrArg List.length he
  simp only [List.length_reverse, List.length_take, min_eq_left hl, min_eq_left hl'] at this
  exact hne this

/-- Nonempty prefixes of the two words of a pair in `ℬ_n` differ in their first letter. -/
private theorem take_reverse_ne_of_mem_pairs {n : ℕ} {p : (Fin n → Fin N) × (Fin n → Fin N)}
    (hp : p ∈ pairs N n) {l l' : ℕ} (hl : 0 < l) (hl' : 0 < l') :
    ((List.ofFn p.1).take l).reverse ≠ ((List.ofFn p.2).take l').reverse := by
  obtain ⟨hn, hlt⟩ := hp
  intro he
  have := congrArg (fun v : List (Fin N) => v[0]?) (List.reverse_inj.1 he)
  simp only [List.getElem?_take_of_lt hl, List.getElem?_take_of_lt hl', List.getElem?_ofFn,
    hn, dite_true] at this
  exact hlt.ne (Option.some_inj.1 this)

/-- The properties of Lemma 4.1 (a) and (b) for one pair `p` and the point `t`. -/
private def Good (k K : ℝ) {n : ℕ} (p : (Fin n → Fin N) × (Fin n → Fin N)) (t : ℝ) : Prop :=
  t ∈ I ∧ (Φ.DualCylDisjoint k K (List.ofFn p.1) (List.ofFn p.2) →
      Disjoint (Φ.dualCylAt k K (List.ofFn p.1) t) (Φ.dualCylAt k K (List.ofFn p.2) t)) ∧
    (Φ.orbit (List.ofFn p.1) t).Nodup ∧ (Φ.orbit (List.ofFn p.2) t).Nodup ∧
    ∀ y ∈ Φ.orbit (List.ofFn p.1) t, y ∈ Φ.orbit (List.ofFn p.2) t → y = t

/-- One step of the induction in Lemma 4.1: a point for the pair `p` whose orbits avoid the
finite set `F`. -/
private theorem exists_point (h : Φ.NoCoincidence) (k K : ℝ) {n : ℕ}
    {p : (Fin n → Fin N) × (Fin n → Fin N)} (hp : p ∈ pairs N n) {F : Set ℝ} (hF : F.Finite) :
    ∃ t, Φ.Good k K p t ∧
      ∀ y ∈ Φ.orbit (List.ofFn p.1) t ++ Φ.orbit (List.ofFn p.2) t, y ∉ F := by
  obtain ⟨t, ⟨ht, hdisj⟩, hex⟩ := ((Φ.infinite_good k K (List.ofFn p.1)
    (List.ofFn p.2)).sdiff (Φ.finite_exceptional h n hF)).nonempty
  have hsep : ∀ v w : List (Fin N), v.length ≤ n → w.length ≤ n → v ≠ w →
      (Φ.comp v t).re ≠ (Φ.comp w t).re :=
    fun v w hv hw hvw heq => hex ⟨ht, Or.inl ⟨v, w, hv, hw, hvw, heq⟩⟩
  have havoid : ∀ v : List (Fin N), v.length ≤ n → (Φ.comp v t).re ∉ F :=
    fun v hv hvF => hex ⟨ht, Or.inr ⟨v, hv, hvF⟩⟩
  have hlen : ∀ (i : Fin n → Fin N) (l : ℕ), ((List.ofFn i).take l).reverse.length ≤ n := by
    intro i l
    simp
  have hnodup : ∀ i : Fin n → Fin N, (Φ.orbit (List.ofFn i) t).Nodup := by
    intro i
    refine List.Nodup.map_on ?_ List.nodup_range
    intro l hl l' hl' he
    by_contra hne
    rw [List.mem_range, List.length_ofFn] at hl hl'
    exact hsep _ _ (hlen i l) (hlen i l')
      (take_reverse_ne_of_ne (by simp; omega) (by simp; omega) hne) he
  refine ⟨t, ⟨ht, hdisj, hnodup p.1, hnodup p.2, ?_⟩, ?_⟩
  · intro y hy1 hy2
    obtain ⟨l, -, rfl⟩ := Φ.mem_orbit.1 hy1
    obtain ⟨l', -, he⟩ := Φ.mem_orbit.1 hy2
    rcases Nat.eq_zero_or_pos l with rfl | hl0
    · simp
    rcases Nat.eq_zero_or_pos l' with rfl | hl0'
    · simpa using he.symm
    exact absurd he.symm (hsep _ _ (hlen _ _) (hlen _ _) (take_reverse_ne_of_mem_pairs hp hl0 hl0'))
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · obtain ⟨l, -, rfl⟩ := Φ.mem_orbit.1 hy
      exact havoid _ (hlen _ _)
    · obtain ⟨l, -, rfl⟩ := Φ.mem_orbit.1 hy
      exact havoid _ (hlen _ _)

/-- The induction of Lemma 4.1 over finite sets of pairs. -/
private theorem exists_points_finset (h : Φ.NoCoincidence) (k K : ℝ) (n : ℕ)
    (S : Finset ((Fin n → Fin N) × (Fin n → Fin N))) :
    ∃ x : (Fin n → Fin N) × (Fin n → Fin N) → ℝ,
      (∀ p ∈ S, p ∈ pairs N n → Φ.Good k K p (x p)) ∧
      ∀ p ∈ S, ∀ q ∈ S, p ∈ pairs N n → q ∈ pairs N n → p ≠ q →
        ∀ y ∈ Φ.orbit (List.ofFn p.1) (x p) ++ Φ.orbit (List.ofFn p.2) (x p),
          y ∉ Φ.orbit (List.ofFn q.1) (x q) ++ Φ.orbit (List.ofFn q.2) (x q) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp, by simp⟩
  | insert a S ha ih =>
    obtain ⟨x, hgood, hsep⟩ := ih
    by_cases hpa : a ∈ pairs N n
    · let F : Set ℝ := ⋃ q ∈ S,
        {y | y ∈ Φ.orbit (List.ofFn q.1) (x q) ++ Φ.orbit (List.ofFn q.2) (x q)}
      have hF : F.Finite := S.finite_toSet.biUnion fun q _ => List.finite_toSet _
      obtain ⟨t, hgt, havoid⟩ := Φ.exists_point h k K hpa hF
      have hxS : ∀ q ∈ S, Function.update x a t q = x q :=
        fun q hq => Function.update_of_ne (ne_of_mem_of_not_mem hq ha) _ _
      refine ⟨Function.update x a t, ?_, ?_⟩
      · intro p hp hpp
        rcases Finset.mem_insert.1 hp with rfl | hp
        · rwa [Function.update_self]
        · rw [hxS p hp]
          exact hgood p hp hpp
      · intro p hp q hq hpp hqp hpq y hy
        rcases Finset.mem_insert.1 hp with rfl | hpS <;>
          rcases Finset.mem_insert.1 hq with rfl | hqS
        · exact absurd rfl hpq
        · rw [Function.update_self] at hy
          rw [hxS q hqS]
          exact fun hyq => havoid y hy (mem_biUnion hqS hyq)
        · rw [hxS p hpS] at hy
          rw [Function.update_self]
          exact fun hyq => havoid y hyq (mem_biUnion hpS hy)
        · rw [hxS p hpS] at hy
          rw [hxS q hqS]
          exact hsep p hpS q hqS hpp hqp hpq y hy
    · refine ⟨x, ?_, ?_⟩
      · intro p hp hpp
        rcases Finset.mem_insert.1 hp with rfl | hp
        · exact absurd hpp hpa
        · exact hgood p hp hpp
      · intro p hp q hq hpp hqp hpq
        rcases Finset.mem_insert.1 hp with rfl | hp
        · exact absurd hpp hpa
        rcases Finset.mem_insert.1 hq with rfl | hq
        · exact absurd hqp hpa
        exact hsep p hp q hq hpp hqp hpq

/-- Lemma 4.1. A pair `(i, j)` is not bad when `F_i(k, K) ∩ F_j(k, K) = ∅` in the sense of (2.2). -/
theorem lemma_4_1 (n : ℕ) (k K : ℝ) (h : Φ.NoCoincidence) :
    ∃ x : (Fin n → Fin N) × (Fin n → Fin N) → ℝ,
      (∀ p ∈ pairs N n, x p ∈ I) ∧
      (∀ p ∈ pairs N n, Φ.DualCylDisjoint k K (List.ofFn p.1) (List.ofFn p.2) →
        Disjoint (Φ.dualCylAt k K (List.ofFn p.1) (x p)) (Φ.dualCylAt k K (List.ofFn p.2) (x p))) ∧
      (∀ p ∈ pairs N n, (Φ.orbit (List.ofFn p.1) (x p)).Nodup ∧
        (Φ.orbit (List.ofFn p.2) (x p)).Nodup ∧
        ∀ y ∈ Φ.orbit (List.ofFn p.1) (x p), y ∈ Φ.orbit (List.ofFn p.2) (x p) → y = x p) ∧
      (∀ p ∈ pairs N n, ∀ q ∈ pairs N n, p ≠ q →
        ∀ y ∈ Φ.orbit (List.ofFn p.1) (x p) ++ Φ.orbit (List.ofFn p.2) (x p),
          y ∉ Φ.orbit (List.ofFn q.1) (x q) ++ Φ.orbit (List.ofFn q.2) (x q)) := by
  classical
  obtain ⟨x, hgood, hsep⟩ := Φ.exists_points_finset h k K n Finset.univ
  exact ⟨x, fun p hp => (hgood p (Finset.mem_univ _) hp).1,
    fun p hp => (hgood p (Finset.mem_univ _) hp).2.1,
    fun p hp => (hgood p (Finset.mem_univ _) hp).2.2,
    fun p hp q hq hpq => hsep p (Finset.mem_univ _) q (Finset.mem_univ _) hp hq hpq⟩

/-- A system without exact overlaps satisfies the hypothesis of Lemma 4.1. -/
theorem noCoincidence_of_not_hasExactOverlaps (h : ¬ Φ.HasExactOverlaps) : Φ.NoCoincidence :=
  fun _ _ hij => Φ.exists_comp_ne_of_not_hasExactOverlaps h hij

end IFS

end AnalyticESC
