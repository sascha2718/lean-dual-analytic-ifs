module

public import AnalyticESC.Literature.Rapaport.Attractor.Basic

@[expose] public section

/-!
# The iterated system

For `n ≥ 1`, the iterated system `Φ^n = (φ_u)_{|u| = n}` of A. Rapaport, *Dimension of
self-conformal measures associated to an exponentially separated analytic IFS on ℝ*,
arXiv:2412.16753v2, proof of Corollary 1.3, indexed by `Fin (N ^ n)` through
`finFunctionFinEquiv`. If `φ` satisfies `AnalyticESC.RapaportHyp`, so does `Φ^n`: analyticity and
the derivative bounds pass to compositions, a common fixed point of `Φ^n` is a common fixed point
of `φ`, and exponential separation of `φ` at length `m` gives exponential separation of `Φ^n` at
length `⌊m / n⌋`.

Main declarations:

* `block`, `iter`: the words of length `n` and the iterated system;
* `realComp_iter`: `Φ^n`-compositions are `φ`-compositions of the concatenated words;
* `rapaportHyp_iter`: `RapaportHyp (iter φ n)` for `n ≥ 1`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Attractor.Iterate`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Attractor

open Set Filter Topology AnalyticESC FractalGeometry.SelfConformal

variable {N : ℕ} {φ : Fin N → ℝ → ℝ}

/-- The word of length `n` encoded by `j : Fin (N ^ n)`. -/
def block (n : ℕ) (j : Fin (N ^ n)) : List (Fin N) := List.ofFn (finFunctionFinEquiv.symm j)

/-- The iterated system `Φ^n = (φ_u)_{|u| = n}`, indexed by `Fin (N ^ n)`. -/
def iter (φ : Fin N → ℝ → ℝ) (n : ℕ) : Fin (N ^ n) → ℝ → ℝ := fun j => realComp φ (block n j)

/-- Blocks have length `n`. -/
@[simp] theorem length_block (n : ℕ) (j : Fin (N ^ n)) : (block n j).length = n := by
  simp [block]

/-- Distinct indices encode distinct words. -/
theorem block_injective (n : ℕ) : Function.Injective (block (N := N) n) :=
  List.ofFn_injective.comp finFunctionFinEquiv.symm.injective

/-- `Φ^n`-compositions are `φ`-compositions of the concatenated words. -/
theorem realComp_iter (φ : Fin N → ℝ → ℝ) (n : ℕ) (l : List (Fin (N ^ n))) :
    realComp (iter φ n) l = realComp φ (l.flatMap (block n)) := by
  induction l with
  | nil => rfl
  | cons j l ih => rw [realComp_cons, ih, List.flatMap_cons, realComp_append]; rfl

/-- The concatenation of `k` blocks has length `n k`. -/
theorem length_flatMap_block (n : ℕ) (l : List (Fin (N ^ n))) :
    (l.flatMap (block n)).length = n * l.length := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.flatMap_cons, List.length_append, ih, length_block, List.length_cons]
    ring

/-- Concatenation of blocks is injective on lists of equal length. -/
theorem flatMap_block_inj {n : ℕ} :
    ∀ {l₁ l₂ : List (Fin (N ^ n))}, l₁.length = l₂.length →
      l₁.flatMap (block n) = l₂.flatMap (block n) → l₁ = l₂
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | a :: l₁, b :: l₂, hl, h => by
    rw [List.flatMap_cons, List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [length_block, length_block])
    rw [block_injective n h1, flatMap_block_inj (by simpa using hl) h2]

/-- A list of length `m` is `List.ofFn` of a function on `Fin m`. -/
theorem exists_ofFn_eq {α : Type*} (l : List α) {m : ℕ} (hl : l.length = m) :
    ∃ u : Fin m → α, List.ofFn u = l := by
  subst hl
  exact ⟨fun k => l[k], List.ofFn_getElem⟩

/-- Precomposing with a self-map of `I` does not increase `sup_{x ∈ I} |f(x) - g(x)|`. -/
theorem iSup_comp_le {f g h : ℝ → ℝ} (hf : MapsTo f I I) (hg : MapsTo g I I)
    (hh : MapsTo h I I) :
    ⨆ x : I, |f (h x) - g (h x)| ≤ ⨆ x : I, |f x - g x| := by
  have hbdd : BddAbove (range fun x : I => |f x - g x|) :=
    ⟨1, by rintro _ ⟨y, rfl⟩; exact abs_sub_le_one_of_mem_I (hf y.2) (hg y.2)⟩
  exact ciSup_le fun x => le_ciSup (f := fun x : I => |f x - g x|) hbdd ⟨h x, hh x.2⟩

/-- If `φ` satisfies Rapaport's hypotheses, so does the iterated system `Φ^n` for `n ≥ 1`. -/
theorem rapaportHyp_iter (hφ : RapaportHyp φ) (hN : 0 < N) {n : ℕ} (hn : 0 < n) :
    RapaportHyp (iter φ n) := by
  have hlt : cmax φ ^ n < 1 := pow_lt_one₀ cmax_nonneg (cmax_lt_one hφ) hn.ne'
  refine ⟨fun j => mapsTo_realComp hφ _, fun j => analyticOnNhd_realComp hφ _,
    fun j x hx => abs_pos.2 (deriv_realComp_ne_zero hφ _ hx), fun j x hx => ?_, ?_, ?_⟩
  · have := abs_deriv_realComp_le_cmax_pow hφ (block n j) hx
    rw [length_block] at this
    exact this.trans_lt hlt
  · -- a common fixed point of `Φ^n` is fixed by `φ_i^n` and hence by `φ_i`
    rintro ⟨x, hx, hfix⟩
    apply hφ.no_common_fixed_point
    refine ⟨x, hx, fun i => ?_⟩
    set w := List.replicate n i with hw_def
    have hw : realComp φ w x = x := by
      have := hfix (finFunctionFinEquiv fun _ => i)
      simpa [iter, block, w, List.ofFn_const] using this
    have hcomm : realComp φ w (φ i x) = φ i (realComp φ w x) := by
      have e : w ++ [i] = i :: w := by
        rw [hw_def, ← List.replicate_succ', List.replicate_succ]
      have := congrFun (congrArg (realComp φ) e) x
      simpa [realComp_append, realComp_cons] using this
    have hlip := abs_realComp_sub_le hφ w (hφ.mapsTo i hx) hx
    rw [hcomm, hw, List.length_replicate] at hlip
    have h0 : |φ i x - x| = 0 := le_antisymm (by nlinarith [abs_nonneg (φ i x - x)])
      (abs_nonneg _)
    exact sub_eq_zero.1 (abs_eq_zero.1 h0)
  · -- exponential separation at length `m` gives exponential separation at length `⌊m / n⌋`
    obtain ⟨c, hc, hfreq⟩ := hφ.exp_separated
    set c' := min c 1 with hc'_def
    have hc'0 : 0 < c' := lt_min hc one_pos
    have hc'1 : c' ≤ 1 := min_le_right _ _
    refine ⟨c' ^ (2 * n), pow_pos hc'0 _, ?_⟩
    rw [frequently_atTop] at hfreq ⊢
    intro a
    obtain ⟨m, hm, hgood⟩ := hfreq (n * (a + 1))
    have ham : a ≤ m / n := (Nat.le_div_iff_mul_le hn).2 (by nlinarith)
    have hm1 : 1 ≤ m / n := (Nat.le_div_iff_mul_le hn).2 (by nlinarith)
    have hkm : n * (m / n) ≤ m := Nat.mul_div_le m n
    have hmk : m < n * (m / n + 1) := Nat.lt_mul_div_succ m hn
    refine ⟨m / n, ham, ?_⟩
    generalize m / n = k at hm1 hkm hmk ⊢
    intro u v huv
    set L₁ := (List.ofFn u).flatMap (block n) with hL₁
    set L₂ := (List.ofFn v).flatMap (block n) with hL₂
    set w := List.replicate (m - n * k) (⟨0, hN⟩ : Fin N) with hw
    have hlen₁ : (L₁ ++ w).length = m := by
      rw [List.length_append, hL₁, length_flatMap_block, List.length_ofFn, hw,
        List.length_replicate]
      omega
    have hlen₂ : (L₂ ++ w).length = m := by
      rw [List.length_append, hL₂, length_flatMap_block, List.length_ofFn, hw,
        List.length_replicate]
      omega
    obtain ⟨U, hU⟩ := exists_ofFn_eq _ hlen₁
    obtain ⟨V, hV⟩ := exists_ofFn_eq _ hlen₂
    have hUV : U ≠ V := by
      rintro rfl
      apply huv
      have h12 : L₁ = L₂ := List.append_cancel_right (hU.symm.trans hV)
      exact List.ofFn_injective (flatMap_block_inj (by simp) h12)
    have hsep := hgood U V hUV
    rw [hU, hV] at hsep
    simp only [realComp_append, Function.comp_apply] at hsep
    have hsup := iSup_comp_le (h := realComp φ w) (mapsTo_realComp hφ L₁)
      (mapsTo_realComp hφ L₂) (mapsTo_realComp hφ w)
    rw [realComp_iter, realComp_iter, ← hL₁, ← hL₂]
    refine le_trans ?_ (hsep.trans hsup)
    calc (c' ^ (2 * n)) ^ k = c' ^ (2 * n * k) := (pow_mul _ _ _).symm
      _ ≤ c' ^ m := pow_le_pow_of_le_one hc'0.le hc'1 (by nlinarith)
      _ ≤ c ^ m := pow_le_pow_left₀ hc'0.le (min_le_left _ _) m

end FractalGeometry.Rapaport.Attractor
