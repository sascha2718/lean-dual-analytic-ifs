module

public import AnalyticESC.Defs

@[expose] public section

/-!
# Words

Finite and infinite words: prefixes, prepending, the longest common prefix `|i ∧ j|`,
convergence of words by prefixes and the compactness of `Σ_* ∪ Σ`, and the decomposition of two
distinct words of equal length at their last difference.
-/

namespace AnalyticESC

open Set Filter Topology

namespace Word

variable {N : ℕ}

@[simp] theorem length_fin (w : List (Fin N)) : (fin w).length = w.length := rfl

@[simp] theorem length_inf (w : ℕ → Fin N) : (inf w).length = ⊤ := rfl

@[simp] theorem get?_fin (w : List (Fin N)) (n : ℕ) : (fin w).get? n = w[n]? := rfl

@[simp] theorem get?_inf (w : ℕ → Fin N) (n : ℕ) : (inf w).get? n = some (w n) := rfl

@[simp] theorem take_fin (w : List (Fin N)) (n : ℕ) : (fin w).take n = w.take n := rfl

@[simp] theorem take_inf (w : ℕ → Fin N) (n : ℕ) :
    (inf w).take n = List.ofFn fun k : Fin n => w k := rfl

theorem length_take (w : Word N) (n : ℕ) : ((w.take n).length : ℕ∞) = min (n : ℕ∞) w.length := by
  cases w with
  | fin w => simpa [List.length_take] using Nat.mono_cast.map_min
  | inf w => simp

theorem isSome_get?_iff (w : Word N) (n : ℕ) : (w.get? n).isSome ↔ (n : ℕ∞) < w.length := by
  cases w with
  | fin w => simp [Option.isSome_iff_ne_none]
  | inf w => simp

/-- The letters of a prefix. -/
private theorem getElem?_take_word (w : Word N) (n k : ℕ) :
    (w.take n)[k]? = if k < n then w.get? k else none := by
  cases w with
  | fin w => simp [List.getElem?_take]
  | inf w =>
    simp only [take_inf, List.getElem?_ofFn, get?_inf]
    split_ifs <;> rfl

/-- Two prefixes of length `n` agree if and only if the first `n` letters agree. -/
private theorem take_eq_take_iff {v w : Word N} {n : ℕ} :
    v.take n = w.take n ↔ ∀ k < n, v.get? k = w.get? k := by
  constructor
  · intro h k hk
    have := congrArg (fun l : List (Fin N) => l[k]?) h
    simpa [getElem?_take_word, hk] using this
  · intro h
    refine List.ext_getElem? fun k => ?_
    rw [getElem?_take_word, getElem?_take_word]
    split_ifs with hk
    · exact h k hk
    · rfl

/-- A word is determined by its letters. -/
private theorem ext_get? {v w : Word N} (h : ∀ n, v.get? n = w.get? n) : v = w := by
  cases v with
  | fin v =>
    cases w with
    | fin w => exact congrArg fin (List.ext_getElem? h)
    | inf w => have := h v.length; simp at this
  | inf v =>
    cases w with
    | fin w => have := h w.length; simp at this
    | inf w => exact congrArg inf (funext fun n => Option.some_injective _ (h n))

private theorem get?_succ_eq_none {w : Word N} {n : ℕ} (h : w.get? n = none) :
    w.get? (n + 1) = none := by
  cases w with
  | fin w =>
    simp only [get?_fin, List.getElem?_eq_none_iff] at h ⊢
    omega
  | inf w => simp at h

private theorem get?_prepend (a : List (Fin N)) (w : Word N) (n : ℕ) :
    (w.prepend a).get? n = if n < a.length then a[n]? else w.get? (n - a.length) := by
  cases w with
  | fin w => simp [prepend, List.getElem?_append]
  | inf w =>
    simp only [prepend, get?_inf]
    split_ifs with hn <;> simp [hn]

private theorem length_take_of_le {w : Word N} {n : ℕ} (h : (n : ℕ∞) ≤ w.length) :
    (w.take n).length = n := by
  have := length_take w n
  rw [min_eq_left h] at this
  exact_mod_cast this

theorem take_succ {w : Word N} {n : ℕ} {i : Fin N} (h : w.get? n = some i) :
    w.take (n + 1) = w.take n ++ [i] := by
  have hlt : (n : ℕ∞) < w.length := (isSome_get?_iff w n).1 (by simp [h])
  have hlen := length_take_of_le hlt.le
  refine List.ext_getElem? fun k => ?_
  rw [getElem?_take_word, List.getElem?_append, hlen, getElem?_take_word]
  rcases lt_trichotomy k n with hk | rfl | hk
  · simp [hk, Nat.lt_succ_of_lt hk]
  · simp [h]
  · have h1 : ¬ k < n + 1 := by omega
    have h2 : ¬ k < n := by omega
    have h3 : k - n ≠ 0 := by omega
    simp [h1, h2, h3]

theorem take_of_length_le {w : Word N} {n : ℕ} (h : w.length ≤ n) : w = fin (w.take n) := by
  cases w with
  | fin w =>
    simp only [length_fin, Nat.cast_le] at h
    simp [List.take_of_length_le h]
  | inf w => simp at h

theorem length_prepend (a : List (Fin N)) (w : Word N) :
    (w.prepend a).length = a.length + w.length := by
  cases w with
  | fin w => simp [prepend]
  | inf w => simp [prepend]

theorem get?_prepend_of_lt (a : List (Fin N)) (w : Word N) {n : ℕ} (hn : n < a.length) :
    (w.prepend a).get? n = a[n]? := by
  simp [get?_prepend, hn]

theorem get?_prepend_add (a : List (Fin N)) (w : Word N) (n : ℕ) :
    (w.prepend a).get? (a.length + n) = w.get? n := by
  simp [get?_prepend]

theorem take_prepend_of_le (a : List (Fin N)) (w : Word N) {n : ℕ} (hn : n ≤ a.length) :
    (w.prepend a).take n = a.take n := by
  refine List.ext_getElem? fun k => ?_
  rw [getElem?_take_word, get?_prepend, List.getElem?_take]
  split_ifs <;> first | rfl | omega

theorem take_prepend_add (a : List (Fin N)) (w : Word N) (n : ℕ) :
    (w.prepend a).take (a.length + n) = a ++ w.take n := by
  refine List.ext_getElem? fun k => ?_
  rw [getElem?_take_word, get?_prepend, List.getElem?_append, getElem?_take_word]
  split_ifs <;> first | rfl | omega

theorem prepend_append (a b : List (Fin N)) (w : Word N) :
    w.prepend (a ++ b) = (w.prepend b).prepend a := by
  refine ext_get? fun n => ?_
  rw [get?_prepend, get?_prepend, get?_prepend, List.getElem?_append, List.length_append]
  split_ifs <;> first | rfl | omega | rw [Nat.sub_sub]

theorem commonPrefixLength_comm (i j : Word N) :
    i.commonPrefixLength j = j.commonPrefixLength i := by
  have key : ∀ i j : Word N, i.commonPrefixLength j ≤ j.commonPrefixLength i := by
    intro i j
    refine iSup₂_le fun n hn => ?_
    refine le_iSup₂ (f := fun (n : ℕ) (_ : ∀ k < n, (j.get? k).isSome ∧ j.get? k = i.get? k) =>
      (n : ℕ∞)) n fun k hk => ?_
    obtain ⟨h1, h2⟩ := hn k hk
    exact ⟨h2 ▸ h1, h2.symm⟩
  exact le_antisymm (key i j) (key j i)

theorem le_commonPrefixLength_iff {i j : Word N} {n : ℕ} :
    (n : ℕ∞) ≤ i.commonPrefixLength j ↔ ∀ k < n, (i.get? k).isSome ∧ i.get? k = j.get? k := by
  constructor
  · intro h
    by_contra hn
    simp only [not_forall] at hn
    obtain ⟨k, hk, hk'⟩ := hn
    have hle : i.commonPrefixLength j ≤ k := by
      refine iSup₂_le fun m hm => ?_
      by_contra hmk
      exact hk' (hm k (by exact_mod_cast not_le.1 hmk))
    have := h.trans hle
    norm_cast at this
    omega
  · intro h
    exact le_iSup₂ (f := fun (n : ℕ) (_ : ∀ k < n, (i.get? k).isSome ∧ i.get? k = j.get? k) =>
      (n : ℕ∞)) n h

theorem commonPrefixLength_le_length (i j : Word N) :
    i.commonPrefixLength j ≤ min i.length j.length := by
  have key : ∀ i j : Word N, i.commonPrefixLength j ≤ i.length := by
    intro i j
    refine iSup₂_le fun m hm => ?_
    cases m with
    | zero => simp
    | succ m =>
      have := (isSome_get?_iff i m).1 (hm m (Nat.lt_succ_self m)).1
      exact_mod_cast Order.add_one_le_of_lt this
  exact le_min (key i j) (commonPrefixLength_comm i j ▸ key j i)

theorem commonPrefixLength_lt_top {i j : Word N} (h : i ≠ j) : i.commonPrefixLength j < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  refine h (ext_get? fun k => ?_)
  have : ((k + 1 : ℕ) : ℕ∞) ≤ i.commonPrefixLength j := htop ▸ le_top
  exact (le_commonPrefixLength_iff.1 this k (Nat.lt_succ_self k)).2

theorem eq_prepend_take {w : Word N} {n : ℕ} (h : (n : ℕ∞) ≤ w.length) :
    ∃ w' : Word N, w = w'.prepend (w.take n) ∧ (w.take n).length = n := by
  have hlen := length_take_of_le h
  let w' : Word N := match w with
    | fin v => fin (v.drop n)
    | inf v => inf fun k => v (n + k)
  have hw' : ∀ k, w'.get? k = w.get? (n + k) := by
    intro k
    cases w with
    | fin v => simp [w', List.getElem?_drop]
    | inf v => rfl
  refine ⟨w', ext_get? fun k => ?_, hlen⟩
  rw [get?_prepend, hlen, getElem?_take_word, hw']
  split_ifs with hk
  · rfl
  · congr 1; omega

/-- Two words sharing a prefix of length `n` are obtained from one finite word of length `n`. -/
theorem exists_eq_prepend {i j : Word N} {n : ℕ} (h : (n : ℕ∞) ≤ i.commonPrefixLength j) :
    ∃ (a : List (Fin N)) (i' j' : Word N), a.length = n ∧ i = i'.prepend a ∧ j = j'.prepend a := by
  have hP := le_commonPrefixLength_iff.1 h
  have hi : (n : ℕ∞) ≤ i.length := h.trans ((commonPrefixLength_le_length i j).trans
    (min_le_left _ _))
  have hj : (n : ℕ∞) ≤ j.length := h.trans ((commonPrefixLength_le_length i j).trans
    (min_le_right _ _))
  obtain ⟨i', hi', hilen⟩ := eq_prepend_take hi
  obtain ⟨j', hj', -⟩ := eq_prepend_take hj
  have htake : i.take n = j.take n := take_eq_take_iff.2 fun k hk => (hP k hk).2
  exact ⟨i.take n, i', j', hilen, hi', htake ▸ hj'⟩

theorem commonPrefixLength_inf_eq_zero {i j : ℕ → Fin N} (h : i 0 ≠ j 0) :
    (inf i).commonPrefixLength (inf j) = 0 := by
  have h1 : ¬ ((1 : ℕ) : ℕ∞) ≤ (inf i).commonPrefixLength (inf j) := by
    rw [le_commonPrefixLength_iff]
    intro h'
    exact h (Option.some_injective _ (h' 0 one_pos).2)
  rw [not_le, Nat.cast_one] at h1
  exact Order.lt_one_iff.1 h1

/-! ## Convergence of words -/

/-- `w k → w₀` letter by letter: every prefix of `w₀` is eventually the prefix of `w k`. -/
def TendstoPrefix (w : ℕ → Word N) (w₀ : Word N) : Prop :=
  ∀ n, ∀ᶠ k in atTop, (w k).take n = w₀.take n

/-- A sequence of letters which stays `none` once `none` is the sequence of letters of a word. -/
private theorem exists_get?_eq (a : ℕ → Option (Fin N)) (ha : ∀ n, a n = none → a (n + 1) = none) :
    ∃ w : Word N, ∀ n, w.get? n = a n := by
  classical
  by_cases hex : ∃ n, a n = none
  · have hnone : ∀ n, Nat.find hex ≤ n → a n = none := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => exact Nat.find_spec hex
      | succ n _ ih => exact ha n ih
    have hsome : ∀ n < Nat.find hex, (a n).isSome := fun n hn =>
      Option.isSome_iff_ne_none.2 (Nat.find_min hex hn)
    refine ⟨fin (List.ofFn fun k : Fin (Nat.find hex) => (a k).get (hsome k k.2)), fun n => ?_⟩
    simp only [get?_fin, List.getElem?_ofFn]
    split_ifs with hn
    · simp
    · exact (hnone n (not_lt.1 hn)).symm
  · have hex' : ∀ n, a n ≠ none := fun n hn => hex ⟨n, hn⟩
    exact ⟨inf fun n => (a n).get (Option.isSome_iff_ne_none.2 (hex' n)), fun n => by simp⟩

/-- `Σ_* ∪ Σ` is sequentially compact. -/
theorem exists_subseq_tendstoPrefix (w : ℕ → Word N) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w₀ : Word N, TendstoPrefix (w ∘ φ) w₀ := by
  let _ : TopologicalSpace (Option (Fin N)) := ⊥
  have : DiscreteTopology (Option (Fin N)) := ⟨rfl⟩
  obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq fun k n => (w k).get? n
  have hcoord : ∀ n, ∀ᶠ k in atTop, (w (φ k)).get? n = a n := by
    intro n
    have := tendsto_pi_nhds.1 hlim n
    rwa [nhds_discrete, tendsto_pure] at this
  have ha : ∀ n, a n = none → a (n + 1) = none := by
    intro n hn
    obtain ⟨k, hk1, hk2⟩ := ((hcoord n).and (hcoord (n + 1))).exists
    rw [← hk2]
    exact get?_succ_eq_none (hk1.trans hn)
  obtain ⟨w₀, hw₀⟩ := exists_get?_eq a ha
  refine ⟨φ, hφ, w₀, fun n => ?_⟩
  have hall : ∀ᶠ k in atTop, ∀ m : Fin n, (w (φ k)).get? m = a m :=
    eventually_all.2 fun m => hcoord m
  filter_upwards [hall] with k hk
  exact take_eq_take_iff.2 fun m hm => (hk ⟨m, hm⟩).trans (hw₀ m).symm

theorem TendstoPrefix.comp {w : ℕ → Word N} {w₀ : Word N} (h : TendstoPrefix w w₀)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) : TendstoPrefix (w ∘ φ) w₀ :=
  fun n => hφ.tendsto_atTop.eventually (h n)

theorem TendstoPrefix.eventually_get?_eq {w : ℕ → Word N} {w₀ : Word N}
    (h : TendstoPrefix w w₀) (n : ℕ) : ∀ᶠ k in atTop, (w k).get? n = w₀.get? n :=
  (h (n + 1)).mono fun _ hk => take_eq_take_iff.1 hk n (Nat.lt_succ_self n)

theorem TendstoPrefix.eventually_eq {w : ℕ → Word N} {w₀ : Word N} (h : TendstoPrefix w w₀)
    (h₀ : w₀.length ≠ ⊤) : ∀ᶠ k in atTop, w k = w₀ := by
  obtain ⟨l, rfl⟩ : ∃ l, w₀ = fin l := by
    cases w₀ with
    | fin l => exact ⟨l, rfl⟩
    | inf _ => simp at h₀
  filter_upwards [h (l.length + 1)] with k hk
  have hlen := length_take (w k) (l.length + 1)
  rw [hk, take_fin, List.take_of_length_le (by omega)] at hlen
  have hle : (w k).length ≤ ((l.length + 1 : ℕ) : ℕ∞) := by
    by_contra hc
    rw [min_eq_left (not_le.1 hc).le] at hlen
    norm_cast at hlen
    omega
  rw [take_of_length_le hle, hk, take_fin, List.take_of_length_le (by omega)]

/-- A limit of words which eventually have length `L` has length `L`. -/
private theorem TendstoPrefix.length_eq_of_eventually {w : ℕ → Word N} {w₀ : Word N}
    (h : TendstoPrefix w w₀) {L : ℕ} (hL : ∀ᶠ k in atTop, (w k).length = L) : w₀.length = L := by
  obtain ⟨k, hk1, hk2⟩ := ((h (L + 1)).and hL).exists
  have h1 : min ((L + 1 : ℕ) : ℕ∞) w₀.length = L := by
    rw [← length_take, ← hk1, length_take, hk2]
    exact min_eq_right (by exact_mod_cast Nat.le_succ L)
  rcases le_or_gt w₀.length ((L + 1 : ℕ) : ℕ∞) with hc | hc
  · rwa [min_eq_right hc] at h1
  · rw [min_eq_left hc.le] at h1
    norm_cast at h1
    omega

theorem TendstoPrefix.length_eq {i j : ℕ → Word N} {i₀ j₀ : Word N} (hi : TendstoPrefix i i₀)
    (hj : TendstoPrefix j j₀) (hlen : ∀ k, (i k).length = (j k).length) :
    i₀.length = j₀.length := by
  have key : ∀ {i j : ℕ → Word N} {i₀ j₀ : Word N}, TendstoPrefix i i₀ → TendstoPrefix j j₀ →
      (∀ k, (i k).length = (j k).length) → i₀.length ≠ ⊤ → j₀.length = i₀.length := by
    intro i j i₀ j₀ hi hj hlen h₀
    obtain ⟨L, hL⟩ := ENat.ne_top_iff_exists.1 h₀
    rw [← hL]
    refine hj.length_eq_of_eventually ?_
    filter_upwards [hi.eventually_eq h₀] with k hk
    rw [← hlen, hk, hL]
  by_cases hi₀ : i₀.length = ⊤
  · by_cases hj₀ : j₀.length = ⊤
    · rw [hi₀, hj₀]
    · exact key hj hi (fun k => (hlen k).symm) hj₀
  · exact (key hi hj hlen hi₀).symm

theorem TendstoPrefix.eventually_le_commonPrefixLength {w : ℕ → Word N} {w₀ : Word N}
    (h : TendstoPrefix w w₀) (h₀ : w₀.length = ⊤) (n : ℕ) :
    ∀ᶠ k in atTop, (n : ℕ∞) ≤ (w k).commonPrefixLength w₀ := by
  filter_upwards [h n] with k hk
  rw [le_commonPrefixLength_iff]
  intro m hm
  have h1 : (w k).get? m = w₀.get? m := take_eq_take_iff.1 hk m hm
  refine ⟨?_, h1⟩
  rw [h1, isSome_get?_iff, h₀]
  exact ENat.natCast_lt_top m

theorem TendstoPrefix.tendsto_length {w : ℕ → Word N} {w₀ : Word N} (h : TendstoPrefix w w₀)
    (hlen : Tendsto (fun k => (w k).length) atTop (𝓝 ⊤)) : w₀.length = ⊤ := by
  by_contra h₀
  obtain ⟨L, hL⟩ := ENat.ne_top_iff_exists.1 h₀
  obtain ⟨k, hk1, hk2⟩ :=
    ((h.eventually_eq h₀).and (hlen.eventually_const_lt (ENat.natCast_lt_top L))).exists
  rw [hk1, ← hL] at hk2
  exact lt_irrefl _ hk2

theorem eq_inf_of_length_eq_top {w : Word N} (h : w.length = ⊤) : ∃ v : ℕ → Fin N, w = inf v := by
  cases w with
  | fin w => simp at h
  | inf v => exact ⟨v, rfl⟩

end Word

/-- Two distinct words of equal length split at their last difference: `i = a u`, `j = b u` with
`|a| = |b| ≥ 1` and different last letters of `a` and `b`. -/
theorem List.exists_decomp_of_ne {N : ℕ} {i j : List (Fin N)} (hlen : i.length = j.length)
    (hne : i ≠ j) :
    ∃ a b u : List (Fin N), i = a ++ u ∧ j = b ++ u ∧ a.length = b.length ∧ 0 < a.length ∧
      a.getLast? ≠ b.getLast? := by
  induction i using _root_.List.reverseRecOn generalizing j with
  | nil =>
    have : j = [] := _root_.List.eq_nil_of_length_eq_zero hlen.symm
    exact absurd this.symm hne
  | append_singleton i x ih =>
    have hj : j ≠ [] := by
      rintro rfl
      simp at hlen
    obtain ⟨j', y, rfl⟩ : ∃ j' y, j = j' ++ [y] :=
      ⟨j.dropLast, j.getLast hj, (_root_.List.dropLast_append_getLast hj).symm⟩
    simp only [_root_.List.length_append, _root_.List.length_singleton,
      Nat.add_right_cancel_iff] at hlen
    by_cases hxy : x = y
    · subst hxy
      have hne' : i ≠ j' := fun h => hne (h ▸ rfl)
      obtain ⟨a, b, u, rfl, rfl, hab, ha, hlast⟩ := ih hlen hne'
      exact ⟨a, b, u ++ [x], by simp, by simp, hab, ha, hlast⟩
    · exact ⟨i ++ [x], j' ++ [y], [], by simp, by simp, by simp [hlen], by simp, by simp [hxy]⟩

end AnalyticESC
