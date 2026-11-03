module

public import AnalyticESC.Literature.Rapaport.Analytic.Main.Action

@[expose] public section

/-!
# The decomposition of a fibre into pieces

The combinatorial part of the proof of Theorem 1.2 of A. Rapaport, *Dimension of self-conformal
measures associated to an exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2,
Section 4. The words of length `n` with derivative `|φ_v'(0)|` between `e^{-n(χ+δ)}` and
`e^{-n(χ-δ)}` (the set `𝒰_n`) are split into dyadic shells `𝒰_{n,j}` of comparable derivatives,
and a measure `ξ` on `(Fin N)^ℕ` is split into the pieces `F_{j,u} = [𝒰_{n,j}] ∩ σ^{-n}[u]`,
`u ∈ 𝒰_{n'}`, and a remainder. If `ξ` has entropy `> Δ n` on the first `n` letters and the
remainder is small, the pieces whose conditional entropy is `≥ Δ n / 6` carry mass
`> Δ / (6 log N)` (Rapaport's (4.4)).

All entropies are in nats.

## Main declarations

* `GoodWord φ χ δ u`: `u ∈ 𝒰_l`.
* `shellIdx`, `shell_ratio_le`: the shell of a good word, and comparability inside a shell.
* `pieceLabel`: the label `(j, u)` of the piece containing `η`, with the last value of `j` for the
  remainder.
* `mass_highEntropy_pieces_gt`: the mass bound (4.4).

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Main.Pieces`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic.SectionFour

open MeasureTheory ProbabilityTheory Set Filter Topology FractalGeometry.SelfConformal
open FractalGeometry.Rapaport.Analytic
open scoped ENNReal

variable {N : ℕ} {φ : Fin N → ℝ → ℝ}

/-! ### Good words and shells -/

/-- Rapaport's `𝒰_l`: the words `u` of length `l` with
`e^{-l(χ+δ)} ≤ |φ_u'(0)| ≤ e^{-l(χ-δ)}`. -/
def GoodWord (φ : Fin N → ℝ → ℝ) (χ δ : ℝ) {l : ℕ} (u : Fin l → Fin N) : Prop :=
  Real.exp (-(l * (χ + δ))) ≤ |deriv (wordMap φ u) 0| ∧
    |deriv (wordMap φ u) 0| ≤ Real.exp (-(l * (χ - δ)))

/-- The shell `⌊(log |φ_v'(0)| + n (χ + δ)) / log 2⌋` of a word `v` of length `n`. -/
noncomputable def shellIdx (φ : Fin N → ℝ → ℝ) (χ δ : ℝ) {n : ℕ} (v : Fin n → Fin N) : ℕ :=
  ⌊(Real.log |deriv (wordMap φ v) 0| + n * (χ + δ)) / Real.log 2⌋₊

/-- The shell parameter of a good word lies in `[0, 2 n δ / log 2]`. -/
theorem shellParam_mem {χ δ : ℝ} {n : ℕ} {v : Fin n → Fin N} (hv : GoodWord φ χ δ v) :
    0 ≤ (Real.log |deriv (wordMap φ v) 0| + n * (χ + δ)) / Real.log 2 ∧
      (Real.log |deriv (wordMap φ v) 0| + n * (χ + δ)) / Real.log 2 ≤
        2 * n * δ / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : 0 < |deriv (wordMap φ v) 0| := (Real.exp_pos _).trans_le hv.1
  have h1 := Real.log_le_log (Real.exp_pos _) hv.1
  have h2 := Real.log_le_log hpos hv.2
  rw [Real.log_exp] at h1 h2
  constructor
  · exact div_nonneg (by linarith) hlog2.le
  · rw [div_le_div_iff_of_pos_right hlog2]
    linarith

/-- The shell of a good word is at most `⌊2 n δ / log 2⌋`. -/
theorem shellIdx_le {χ δ : ℝ} {n : ℕ} {v : Fin n → Fin N} (hv : GoodWord φ χ δ v) :
    shellIdx φ χ δ v ≤ ⌊2 * n * δ / Real.log 2⌋₊ :=
  Nat.floor_le_floor (shellParam_mem hv).2

/-- Good words in the same shell have derivatives within a factor `2`. -/
theorem shell_ratio_le {χ δ : ℝ} {n : ℕ} {v₁ v₂ : Fin n → Fin N} (h₁ : GoodWord φ χ δ v₁)
    (h₂ : GoodWord φ χ δ v₂) (h : shellIdx φ χ δ v₁ = shellIdx φ χ δ v₂) :
    |deriv (wordMap φ v₁) 0| ≤ 2 * |deriv (wordMap φ v₂) 0| := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp₁ : 0 < |deriv (wordMap φ v₁) 0| := (Real.exp_pos _).trans_le h₁.1
  have hp₂ : 0 < |deriv (wordMap φ v₂) 0| := (Real.exp_pos _).trans_le h₂.1
  set t₁ := (Real.log |deriv (wordMap φ v₁) 0| + n * (χ + δ)) / Real.log 2 with ht₁
  set t₂ := (Real.log |deriv (wordMap φ v₂) 0| + n * (χ + δ)) / Real.log 2 with ht₂
  have hlt : t₁ < t₂ + 1 := by
    have a := Nat.lt_floor_add_one t₁
    have b := Nat.floor_le (shellParam_mem h₂).1
    unfold shellIdx at h
    rw [← ht₁, ← ht₂] at h
    rw [h] at a
    linarith
  have hlog : Real.log |deriv (wordMap φ v₁) 0| <
      Real.log 2 + Real.log |deriv (wordMap φ v₂) 0| := by
    rw [ht₁, ht₂, div_lt_iff₀ hlog2, add_mul, div_mul_cancel₀ _ hlog2.ne'] at hlt
    linarith
  rw [← Real.log_mul (by norm_num) hp₂.ne'] at hlog
  exact (Real.log_lt_log_iff hp₁ (by positivity)).1 hlog |>.le

/-! ### Pieces -/

open Classical in
/-- The label of a pair of words `(v, u)`: the shell of `v` when `v` and `u` are good, and the
last shell index `S + 1` otherwise; together with `u`. -/
noncomputable def pairLabel (φ : Fin N → ℝ → ℝ) (χ δ : ℝ) (n n' S : ℕ)
    (z : (Fin n → Fin N) × (Fin n' → Fin N)) : Fin (S + 2) × (Fin n' → Fin N) :=
  (if GoodWord φ χ δ z.1 ∧ GoodWord φ χ δ z.2 then
      Fin.castSucc ⟨min (shellIdx φ χ δ z.1) S, Nat.lt_succ_of_le (min_le_right _ _)⟩
    else Fin.last (S + 1), z.2)

/-- The label of the piece of `η`: the shell of `η|_n` and the word `(σ^n η)|_{n'}` when both are
good, and the last shell index `S + 1` (the remainder) otherwise. -/
noncomputable def pieceLabel (φ : Fin N → ℝ → ℝ) (χ δ : ℝ) (n n' S : ℕ) (η : ℕ → Fin N) :
    Fin (S + 2) × (Fin n' → Fin N) :=
  pairLabel φ χ δ n n' S (pre n η, pre n' (shift^[n] η))

/-- The piece labelling is measurable: it depends on finitely many coordinates. -/
theorem measurable_pieceLabel (χ δ : ℝ) (n n' S : ℕ) :
    Measurable (pieceLabel φ χ δ n n' S) :=
  (measurable_of_countable _).comp
    ((measurable_pre n).prodMk ((measurable_pre n').comp (measurable_shift.iterate n)))

/-- A label with a shell index below `S + 1` is a good piece: its points have good prefixes. -/
theorem good_of_pieceLabel {χ δ : ℝ} {n n' S : ℕ} {η : ℕ → Fin N}
    (h : (pieceLabel φ χ δ n n' S η).1 ≠ Fin.last (S + 1)) :
    GoodWord φ χ δ (pre n η) ∧ GoodWord φ χ δ (pre n' (shift^[n] η)) := by
  by_contra hc
  apply h
  simp [pieceLabel, pairLabel, hc]

/-- The shell index of a point of a good piece, for `S ≥ ⌊2 n δ / log 2⌋`. -/
theorem shellIdx_of_pieceLabel {χ δ : ℝ} {n n' S : ℕ} (hS : ⌊2 * n * δ / Real.log 2⌋₊ ≤ S)
    {η : ℕ → Fin N} (h : (pieceLabel φ χ δ n n' S η).1 ≠ Fin.last (S + 1)) :
    ((pieceLabel φ χ δ n n' S η).1 : ℕ) = shellIdx φ χ δ (pre n η) := by
  have hg := good_of_pieceLabel h
  simp only [pieceLabel, pairLabel, hg, and_self, ite_true, Fin.val_castSucc]
  exact min_eq_left ((shellIdx_le hg.1).trans hS)

/-- The second component of the label is the word `(σ^n η)|_{n'}`. -/
theorem pieceLabel_snd (χ δ : ℝ) (n n' S : ℕ) (η : ℕ → Fin N) :
    (pieceLabel φ χ δ n n' S η).2 = pre n' (shift^[n] η) := rfl

/-! ### The mass of the high-entropy pieces -/

/-- The sum of the masses of the fibres over a finset of labels is the mass of its preimage. -/
theorem sum_measureReal_preimage {X L : Type*} [MeasurableSpace X] [MeasurableSpace L]
    [MeasurableSingletonClass L] {θ : Measure X} [IsFiniteMeasure θ] {g : X → L}
    (hg : Measurable g) (s : Finset L) :
    ∑ b ∈ s, θ.real (g ⁻¹' {b}) = θ.real (g ⁻¹' ↑s) := by
  have he : g ⁻¹' (↑s : Set L) = ⋃ b ∈ s, g ⁻¹' {b} := by
    ext x
    simp
  rw [he, measureReal_biUnion_finset]
  · intro b _ c _ hbc
    exact (Set.disjoint_singleton.2 hbc).preimage g
  · exact fun b _ => hg (measurableSet_singleton b)

/-- The good labels whose piece has conditional entropy at least `Δ n / 6` on the first `n`
letters: Rapaport's set `𝒬`. -/
noncomputable def highLabels (ξ : Measure (ℕ → Fin N)) (φ : Fin N → ℝ → ℝ) (χ δ Δ : ℝ)
    (n n' S : ℕ) : Finset (Fin (S + 2) × (Fin n' → Fin N)) :=
  letI := Classical.dec
  Finset.univ.filter fun b => b.1 ≠ Fin.last (S + 1) ∧
    Δ / 6 * n ≤ ent (ξ[|pieceLabel φ χ δ n n' S ⁻¹' {b}]) (pre n)

/-- The entropy of the first `n` letters is at most `n log N`. -/
theorem ent_pre_le (ζ : Measure (ℕ → Fin N)) [IsProbabilityMeasure ζ] (n : ℕ) :
    ent ζ (pre n) ≤ n * Real.log N := by
  refine (ent_le_log_card (measurable_pre n) Finset.univ fun b _ => Finset.mem_univ b).trans ?_
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow,
    le_refl]

/-- Rapaport's (4.4): if `H(ξ, 𝒞_n) > Δ n`, the remainder has mass at most `2δ` and the number of
labels is small, then the high-entropy pieces carry mass `> Δ / (6 log N)`. -/
theorem mass_highLabels_gt (ξ : Measure (ℕ → Fin N)) [IsProbabilityMeasure ξ] {χ δ Δ : ℝ}
    {n n' S : ℕ} (hN : 0 < Real.log N) (hΔ : 0 < Δ) (hent : Δ * n < ent ξ (pre n))
    (hbad : ξ.real {η | ¬ (GoodWord φ χ δ (pre n η) ∧ GoodWord φ χ δ (pre n' (shift^[n] η)))} ≤
      2 * δ)
    (hcount : Real.log ((S + 2) * N ^ n') + 2 * δ * (n * Real.log N) ≤ 2 / 3 * (Δ * n)) :
    Δ / (6 * Real.log N) <
      ∑ b ∈ highLabels ξ φ χ δ Δ n n' S, ξ.real (pieceLabel φ χ δ n n' S ⁻¹' {b}) := by
  classical
  set g := pieceLabel φ χ δ n n' S with hg_def
  have hg : Measurable g := measurable_pieceLabel χ δ n n' S
  have hf : Measurable (pre (N := N) n) := measurable_pre n
  have hfinf : FiniteLabels ξ (pre (N := N) n) := Set.toFinite _
  have hfing : FiniteLabels ξ g := Set.toFinite _
  set w : Fin (S + 2) × (Fin n' → Fin N) → ℝ := fun b => ξ.real (g ⁻¹' {b}) with hw
  set H : Fin (S + 2) × (Fin n' → Fin N) → ℝ := fun b => ent (comp ξ g b) (pre n) with hH
  have hn : 0 < (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      have := ent_pre_le ξ 0
      simp at hent this
      linarith
    · exact_mod_cast h0
  -- the chain rule
  have h1 : ent ξ (pre n) ≤ ent ξ g + ∑ b, w b * H b := by
    have := ent_le_ent_pair_left hf hg hfinf hfing
    rw [ent_pair_eq_add_cent, cent_eq_cavg hf hg hfinf hfing,
      cavg_eq_sum_of_subset Finset.univ (fun b _ => Finset.mem_univ b)] at this
    exact this
  have h2 : ent ξ g ≤ Real.log ((S + 2) * N ^ n') := by
    refine (ent_le_log_card hg Finset.univ fun b _ => Finset.mem_univ b).trans_eq ?_
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
    push_cast
    ring_nf
  have hw0 : ∀ b, 0 ≤ w b := fun b => measureReal_nonneg
  have hwH : ∀ b, w b * H b ≤ w b * (n * Real.log N) := by
    intro b
    by_cases hb : ξ (g ⁻¹' {b}) = 0
    · simp [hw, measureReal_def, hb]
    · have := comp_isProbabilityMeasure (θ := ξ) (f := g) hb
      exact mul_le_mul_of_nonneg_left (ent_pre_le _ n) (hw0 b)
  set Q := highLabels ξ φ χ δ Δ n n' S with hQ
  set B : Finset (Fin (S + 2) × (Fin n' → Fin N)) :=
    Finset.univ.filter fun b => b.1 = Fin.last (S + 1) with hB
  -- the labels outside `Q`
  have hout : ∀ b ∉ Q, w b * H b ≤ (if b ∈ B then w b * (n * Real.log N) else 0) +
      w b * (Δ / 6 * n) := by
    intro b hbQ
    have h3 : 0 ≤ w b * (Δ / 6 * n) := mul_nonneg (hw0 b) (by positivity)
    by_cases hbB : b ∈ B
    · simp only [hbB, ite_true]
      linarith [hwH b]
    · simp only [hbB, ite_false, zero_add]
      have hlast : b.1 ≠ Fin.last (S + 1) := by
        simpa [hB] using hbB
      have hlt : H b < Δ / 6 * n := by
        by_contra hc
        refine hbQ ?_
        simp only [hQ, highLabels, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hlast, not_lt.1 hc⟩
      exact mul_le_mul_of_nonneg_left hlt.le (hw0 b)
  have hsum1 : ∑ b, w b = 1 :=
    sum_measureReal_fiber hg Finset.univ fun b _ => Finset.mem_univ b
  have hBmass : ∑ b ∈ B, w b ≤ 2 * δ := by
    rw [sum_measureReal_preimage hg B]
    refine (measureReal_mono ?_).trans hbad
    intro η hη
    simp only [mem_preimage, Finset.coe_filter, Finset.mem_univ, true_and, mem_ofPred_eq,
      hB] at hη ⊢
    intro hgood
    simp only [hg_def, pieceLabel, pairLabel, hgood, and_self, ite_true] at hη
    exact Fin.castSucc_ne_last _ hη
  have hsplit : ∑ b, w b * H b ≤ (n * Real.log N) * ∑ b ∈ Q, w b +
      (n * Real.log N) * ∑ b ∈ B, w b + Δ / 6 * n := by
    rw [← Finset.sum_add_sum_compl Q]
    have hA : ∑ b ∈ Q, w b * H b ≤ (n * Real.log N) * ∑ b ∈ Q, w b := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun b _ => by linarith [hwH b]
    have hC : ∑ b ∈ Qᶜ, w b * H b ≤ (n * Real.log N) * ∑ b ∈ B, w b + Δ / 6 * n := by
      calc ∑ b ∈ Qᶜ, w b * H b
          ≤ ∑ b ∈ Qᶜ, ((if b ∈ B then w b * (n * Real.log N) else 0) + w b * (Δ / 6 * n)) :=
            Finset.sum_le_sum fun b hb => hout b (Finset.mem_compl.1 hb)
        _ ≤ ∑ b, ((if b ∈ B then w b * (n * Real.log N) else 0) + w b * (Δ / 6 * n)) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun b _ _ => ?_
            have := hw0 b
            split_ifs <;> positivity
        _ = (n * Real.log N) * ∑ b ∈ B, w b + Δ / 6 * n := by
            rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum1, one_mul, Finset.sum_ite,
              Finset.sum_const_zero, add_zero, Finset.mul_sum]
            congr 1
            refine Finset.sum_congr ?_ fun b _ => by ring
            ext b
            simp [hB]
    linarith
  have hnΛ : 0 < n * Real.log N := mul_pos hn hN
  have key : Δ / 6 * n < (n * Real.log N) * ∑ b ∈ Q, w b := by
    have := mul_le_mul_of_nonneg_left hBmass hnΛ.le
    nlinarith
  rw [div_lt_iff₀ (by positivity)]
  have : Δ / 6 * n = (Δ / (6 * Real.log N)) * (n * Real.log N) := by
    field_simp
  rw [this] at key
  have := (mul_lt_mul_iff_of_pos_right hnΛ).1 (by linarith : Δ / (6 * Real.log N) *
    (n * Real.log N) < (∑ b ∈ Q, w b) * (n * Real.log N))
  rw [div_lt_iff₀ (by positivity)] at this
  linarith

end FractalGeometry.Rapaport.Analytic.SectionFour
