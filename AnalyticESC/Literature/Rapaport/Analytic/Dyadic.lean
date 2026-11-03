module

public import AnalyticESC.Literature.Rapaport.Analytic.Entropy
public import AnalyticESC.Literature.Rapaport.Analytic.Poly

@[expose] public section

/-!
# Dyadic entropy: cells as fibres and commensurability

Dyadic partitions of `ℝ` and of `𝒫_k ≅ ℝ^{k+1}` as labellings, and the commensurability bounds
behind Lemmas 2.2 and 2.3 of A. Rapaport, *Dimension of self-conformal measures associated to an
exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2: the dyadic entropy changes by
`O(1 + log C)` under maps that are `C`-bi-Lipschitz on the support, and by `O(1)` under maps that
are uniformly `2^{-n}`-close.

## Main declarations

* `cell_eq_preimage`, `dyadicEntropy_eq_ent`, `dyadicEntropyVec_eq_ent`, `component_eq_comp`,
  `componentVec_eq_comp`: the dyadic vocabulary in terms of `ent` and `comp`.
* `cellIdx_eq_ediv`: the level-`n` cell index is a function of the level-`(n+m)` one.
* `ent_le_ent_add_log_of_fiber_card_on`: commensurability on a set of full measure.
* `ent_cellIdx_comp_le`, `ent_cellIdxVec_comp_le`: if `g x = g x'` forces `|F x - F x'| ≤ r` on a
  set of full measure, then `H(θ, F⁻¹ 𝒟_n) ≤ H(θ, g) + log (2^{n+1} r + 2)` (coordinatewise for
  `𝒫_k`, with the factor `k + 1`).
* `cent_cellIdx_comp_le`: the conditional form of `ent_cellIdx_comp_le`.
* `finiteLabels_cellIdx_comp`, `ent_cellIdx_comp_le_log`, and their vector forms: finiteness and
  the cardinality bound for labellings with bounded values.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Dyadic`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic

open MeasureTheory ProbabilityTheory Set FractalGeometry.SelfConformal
open scoped ENNReal

/-! ### Cells as fibres -/

/-- The cell index `x ↦ ⌊2^n x⌋` is measurable. -/
theorem measurable_cellIdx (n : ℕ) : Measurable (cellIdx n) := by
  unfold cellIdx
  exact Int.measurable_floor.comp (measurable_const.mul measurable_id)

/-- `0 < 2^n` in `ℝ`. -/
theorem two_pow_pos' (n : ℕ) : (0 : ℝ) < 2 ^ n := by positivity

/-- `⌊2^n x⌋ ≤ 2^n x`. -/
theorem cellIdx_le (n : ℕ) (x : ℝ) : (cellIdx n x : ℝ) ≤ 2 ^ n * x := Int.floor_le _

/-- `2^n x < ⌊2^n x⌋ + 1`. -/
theorem lt_cellIdx_add_one (n : ℕ) (x : ℝ) : 2 ^ n * x < (cellIdx n x : ℝ) + 1 :=
  Int.lt_floor_add_one _

/-- The cell index is monotone. -/
theorem cellIdx_mono (n : ℕ) : Monotone (cellIdx n) := fun _ _ h =>
  Int.floor_mono (mul_le_mul_of_nonneg_left h (two_pow_pos' n).le)

/-- A point lies in the cell `k` exactly when its cell index is `k`. -/
theorem mem_cell_iff (n : ℕ) (k : ℤ) (x : ℝ) : x ∈ cell n k ↔ cellIdx n x = k := by
  have h2 := two_pow_pos' n
  rw [cell, mem_Ico, cellIdx, Int.floor_eq_iff, div_le_iff₀ h2, lt_div_iff₀ h2]
  constructor <;> rintro ⟨h1, h3⟩ <;> constructor <;> linarith

/-- The cell `k` is the fibre of the cell index over `k`. -/
theorem cell_eq_preimage (n : ℕ) (k : ℤ) : cell n k = cellIdx n ⁻¹' {k} := by
  ext x
  rw [mem_cell_iff]
  rfl

/-- The cell of `x` is the fibre of the cell index over the index of `x`. -/
theorem cellOf_eq_preimage (n : ℕ) (x : ℝ) : cellOf n x = cellIdx n ⁻¹' {cellIdx n x} :=
  cell_eq_preimage n _

/-- Dyadic cells are measurable. -/
theorem measurableSet_cell (n : ℕ) (k : ℤ) : MeasurableSet (cell n k) := by
  rw [cell_eq_preimage]
  exact measurable_cellIdx n (measurableSet_singleton k)

/-- The dyadic entropy is the entropy of the cell index, in bits. -/
theorem dyadicEntropy_eq_ent (θ : Measure ℝ) (n : ℕ) :
    dyadicEntropy θ n = ent θ (cellIdx n) / Real.log 2 := by
  simp only [dyadicEntropy, ent, cell_eq_preimage]

/-- The dyadic entropy on `𝒫_k` is the entropy of the cell index, in bits. -/
theorem dyadicEntropyVec_eq_ent {k : ℕ} (ν : Measure (Poly k)) (n : ℕ) :
    dyadicEntropyVec ν n = ent ν (cellIdxVec n) / Real.log 2 := rfl

/-- The component `θ_{x,n}` is the component of `θ` for the cell index of `x`. -/
theorem component_eq_comp (θ : Measure ℝ) (n : ℕ) (x : ℝ) :
    component θ n x = comp θ (cellIdx n) (cellIdx n x) := by
  rw [component, comp, cellOf_eq_preimage]
  rfl

/-- The component `ν_{q,n}` is the component of `ν` for the cell index of `q`. -/
theorem componentVec_eq_comp {k : ℕ} (ν : Measure (Poly k)) (n : ℕ) (q : Poly k) :
    componentVec ν n q = comp ν (cellIdxVec n) (cellIdxVec n q) := rfl

/-- Points with the same level-`n` cell index are `2^{-n}`-close. -/
theorem abs_sub_lt_of_cellIdx_eq {n : ℕ} {x y : ℝ} (h : cellIdx n x = cellIdx n y) :
    |x - y| < 1 / 2 ^ n := by
  have h2 := two_pow_pos' n
  have hx1 := cellIdx_le n x
  have hx2 := lt_cellIdx_add_one n x
  have hy1 := cellIdx_le n y
  have hy2 := lt_cellIdx_add_one n y
  rw [h] at hx1 hx2
  rw [lt_div_iff₀ h2]
  have he : |x - y| * 2 ^ n = |2 ^ n * x - 2 ^ n * y| := by
    rw [← mul_sub, abs_mul, abs_of_pos h2, mul_comm]
  rw [he, abs_lt]
  constructor <;> linarith

/-- The level-`n` cell index is the integer quotient of the level-`(n+m)` one by `2^m`. -/
theorem cellIdx_eq_ediv (n m : ℕ) (x : ℝ) :
    cellIdx n x = cellIdx (n + m) x / ((2 : ℤ) ^ m) := by
  unfold cellIdx
  have h : ((2 : ℤ) ^ m : ℤ) = ((2 ^ m : ℕ) : ℤ) := by push_cast; ring
  rw [h, ← Int.floor_div_natCast]
  congr 1
  push_cast
  rw [pow_add]
  field_simp

/-- The coarse labelling is a function of the fine one. -/
theorem cellIdx_factor (n m : ℕ) :
    cellIdx n = (fun c : ℤ => c / (2 : ℤ) ^ m) ∘ cellIdx (n + m) := by
  funext x
  exact cellIdx_eq_ediv n m x

/-- The cell indices of the points of `[a, b]` lie in `[cellIdx n a, cellIdx n b]`. -/
theorem cellIdx_mem_Icc {n : ℕ} {a b x : ℝ} (hx : x ∈ Icc a b) :
    cellIdx n x ∈ Finset.Icc (cellIdx n a) (cellIdx n b) :=
  Finset.mem_Icc.2 ⟨cellIdx_mono n hx.1, cellIdx_mono n hx.2⟩

/-- The number of level-`n` cells meeting `[a, b]`. -/
theorem card_Icc_cellIdx_le (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    (Finset.Icc (cellIdx n a) (cellIdx n b)).card ≤ ⌊2 ^ n * (b - a)⌋₊ + 2 := by
  rw [Int.card_Icc]
  have h1 := cellIdx_le n b
  have h2 := lt_cellIdx_add_one n a
  have hnn : (0 : ℝ) ≤ 2 ^ n * (b - a) := mul_nonneg (two_pow_pos' n).le (by linarith)
  have h3 : ((cellIdx n b - cellIdx n a - 1 : ℤ) : ℝ) < 2 ^ n * (b - a) := by
    push_cast
    nlinarith
  have h4 : cellIdx n b - cellIdx n a - 1 < (⌊2 ^ n * (b - a)⌋₊ : ℤ) + 1 := by
    have h5 : ((cellIdx n b - cellIdx n a - 1 : ℤ) : ℝ) < (⌊2 ^ n * (b - a)⌋₊ : ℝ) + 1 :=
      h3.trans (Nat.lt_floor_add_one _)
    exact_mod_cast h5
  omega

/-- The cardinality bound of `card_Icc_cellIdx_le` as a real number. -/
theorem card_bound_le (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ((⌊2 ^ n * r⌋₊ + 2 : ℕ) : ℝ) ≤ 2 ^ n * r + 2 := by
  push_cast
  have := Nat.floor_le (mul_nonneg (two_pow_pos' n).le hr)
  linarith

/-! ### Commensurability on a set of full measure -/

section Commensurable

variable {X : Type*} [MeasurableSpace X] {θ : Measure X}
variable {L L' : Type*}

/-- Labellings that agree almost everywhere have the same labels of positive mass. -/
theorem FiniteLabels.congr_ae {f g : X → L} (hf : FiniteLabels θ f) (h : f =ᵐ[θ] g) :
    FiniteLabels θ g := by
  refine hf.subset fun b hb => ?_
  simp only [Function.mem_support] at hb ⊢
  rwa [measure_congr (h.preimage {b})]

/-- A set whose complement is null holds almost everywhere. -/
theorem ae_mem_of_compl_null {S : Set X} (hS : θ Sᶜ = 0) : ∀ᵐ x ∂θ, x ∈ S := by
  rw [ae_iff]
  exact hS

variable [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L]
variable [MeasurableSpace L'] [MeasurableSingletonClass L'] [Countable L']
variable [IsProbabilityMeasure θ]

/-- Commensurability on a set `S` of full measure: if, for every label `c` of `g`, the points of
`S` with label `c` carry at most `N` labels of `f`, then `H(θ, f) ≤ H(θ, g) + log N`. -/
theorem ent_le_ent_add_log_of_fiber_card_on {f : X → L} {g : X → L'} (hf : Measurable f)
    (hg : Measurable g) (hfinf : FiniteLabels θ f) (hfing : FiniteLabels θ g) {S : Set X}
    (hS : MeasurableSet S) (hSθ : θ Sᶜ = 0) {N : ℕ}
    (h : ∀ c, ∃ s : Finset L, s.card ≤ N ∧ ∀ x ∈ S, g x = c → f x ∈ s) :
    ent θ f ≤ ent θ g + Real.log N := by
  classical
  have hSne : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.compl_empty, measure_univ] at hSθ
    exact one_ne_zero hSθ
  obtain ⟨x₀, hx₀⟩ := hSne
  set f' : X → L := S.piecewise f fun _ => f x₀
  set g' : X → L' := S.piecewise g fun _ => g x₀
  have hS' := ae_mem_of_compl_null hSθ
  have hff : f' =ᵐ[θ] f := by
    filter_upwards [hS'] with x hx
    simp [f', hx]
  have hgg : g' =ᵐ[θ] g := by
    filter_upwards [hS'] with x hx
    simp [g', hx]
  have hf' : Measurable f' := hf.piecewise hS measurable_const
  have hg' : Measurable g' := hg.piecewise hS measurable_const
  have key := ent_le_ent_add_log_of_fiber_card hf' hg' (hfinf.congr_ae hff.symm)
    (hfing.congr_ae hgg.symm) (N := N) fun c => by
      obtain ⟨s, hs, hsub⟩ := h c
      refine ⟨s, hs, fun x hx => ?_⟩
      by_cases hxS : x ∈ S
      · simp only [f', g', Set.piecewise_eq_of_mem _ _ _ hxS] at hx ⊢
        exact hsub x hxS hx
      · simp only [f', g', Set.piecewise_eq_of_notMem _ _ _ hxS] at hx ⊢
        exact hsub x₀ hx₀ hx
  rwa [ent_congr_ae hff, ent_congr_ae hgg] at key

end Commensurable

/-! ### Real-valued labellings -/

section RealLabels

variable {X : Type*} [MeasurableSpace X] {θ : Measure X}

/-- A labelling `cellIdx n ∘ F` with `F` almost surely in `[a, b]` has finite labels. -/
theorem finiteLabels_cellIdx_comp {F : X → ℝ} {a b : ℝ} (n : ℕ)
    (h : ∀ᵐ x ∂θ, F x ∈ Icc a b) : FiniteLabels θ (cellIdx n ∘ F) :=
  finiteLabels_of_ae_mem_finset (Finset.Icc (cellIdx n a) (cellIdx n b)) (by
    filter_upwards [h] with x hx
    exact cellIdx_mem_Icc hx)

variable [IsProbabilityMeasure θ]

/-- The cardinality bound: if `F` is almost surely in `[a, b]`, then
`H(θ, F⁻¹ 𝒟_n) ≤ log (2^n (b - a) + 2)`. -/
theorem ent_cellIdx_comp_le_log {F : X → ℝ} (hF : Measurable F) {a b : ℝ} (hab : a ≤ b)
    (n : ℕ) (h : ∀ᵐ x ∂θ, F x ∈ Icc a b) :
    ent θ (cellIdx n ∘ F) ≤ Real.log (2 ^ n * (b - a) + 2) := by
  refine (ent_le_log_of_ae_mem ((measurable_cellIdx n).comp hF)
    (Finset.Icc (cellIdx n a) (cellIdx n b)) ?_).trans ?_
  · filter_upwards [h] with x hx
    exact cellIdx_mem_Icc hx
  · have hc := card_Icc_cellIdx_le n hab
    have hpos : (0 : ℝ) < (Finset.Icc (cellIdx n a) (cellIdx n b)).card := by
      have : cellIdx n a ∈ Finset.Icc (cellIdx n a) (cellIdx n b) :=
        Finset.mem_Icc.2 ⟨le_rfl, cellIdx_mono n hab⟩
      exact_mod_cast Finset.card_pos.2 ⟨_, this⟩
    refine Real.log_le_log hpos ?_
    calc ((Finset.Icc (cellIdx n a) (cellIdx n b)).card : ℝ)
        ≤ ((⌊2 ^ n * (b - a)⌋₊ + 2 : ℕ) : ℝ) := by exact_mod_cast hc
      _ ≤ 2 ^ n * (b - a) + 2 := card_bound_le n (by linarith)

variable {L : Type*} [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L]

/-- The basic commensurability bound for real-valued labellings: if on a set `S` of full measure
`g x = g x'` forces `|F x - F x'| ≤ r`, then `H(θ, F⁻¹ 𝒟_n) ≤ H(θ, g) + log (2^n (2r) + 2)`. -/
theorem ent_cellIdx_comp_le {F : X → ℝ} {g : X → L} (hF : Measurable F) (hg : Measurable g)
    (n : ℕ) (hfinF : FiniteLabels θ (cellIdx n ∘ F)) (hfing : FiniteLabels θ g) {S : Set X}
    (hS : MeasurableSet S) (hSθ : θ Sᶜ = 0) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ x ∈ S, ∀ x' ∈ S, g x = g x' → |F x - F x'| ≤ r) :
    ent θ (cellIdx n ∘ F) ≤ ent θ g + Real.log (2 ^ n * (2 * r) + 2) := by
  classical
  have key := ent_le_ent_add_log_of_fiber_card_on ((measurable_cellIdx n).comp hF) hg hfinF
    hfing hS hSθ (N := ⌊2 ^ n * (2 * r)⌋₊ + 2) fun c => by
      by_cases hc : ∃ x₀ ∈ S, g x₀ = c
      · obtain ⟨x₀, hx₀S, hx₀⟩ := hc
        refine ⟨Finset.Icc (cellIdx n (F x₀ - r)) (cellIdx n (F x₀ + r)), ?_, fun x hxS hx => ?_⟩
        · have := card_Icc_cellIdx_le n (a := F x₀ - r) (b := F x₀ + r) (by linarith)
          rwa [show F x₀ + r - (F x₀ - r) = 2 * r by ring] at this
        · have hd := h x hxS x₀ hx₀S (hx.trans hx₀.symm)
          rw [abs_le] at hd
          exact cellIdx_mem_Icc ⟨by linarith, by linarith⟩
      · refine ⟨∅, by simp, fun x hxS hx => absurd ⟨x, hxS, hx⟩ hc⟩
  refine key.trans (add_le_add le_rfl ?_)
  have hpos : (0 : ℝ) < ((⌊2 ^ n * (2 * r)⌋₊ + 2 : ℕ) : ℝ) := by positivity
  exact Real.log_le_log hpos (card_bound_le n (by linarith))

/-- The conditional form of `ent_cellIdx_comp_le`: if on a set `S` of full measure `g x = g x'`
forces `|F x - F x'| ≤ r`, then `H(θ, F⁻¹ 𝒟_n ∣ g) ≤ log (2^n (2r) + 2)`. -/
theorem cent_cellIdx_comp_le {F : X → ℝ} {g : X → L} (hF : Measurable F) (hg : Measurable g)
    (n : ℕ) (hfinF : FiniteLabels θ (cellIdx n ∘ F)) (hfing : FiniteLabels θ g) {S : Set X}
    (hS : MeasurableSet S) (hSθ : θ Sᶜ = 0) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ x ∈ S, ∀ x' ∈ S, g x = g x' → |F x - F x'| ≤ r) :
    cent θ (cellIdx n ∘ F) g ≤ Real.log (2 ^ n * (2 * r) + 2) := by
  classical
  have key := ent_le_ent_add_log_of_fiber_card_on
    (f := fun x => ((cellIdx n ∘ F) x, g x)) (g := g)
    (((measurable_cellIdx n).comp hF).prodMk hg) hg (hfinF.pair hfing) hfing hS hSθ
    (N := ⌊2 ^ n * (2 * r)⌋₊ + 2) fun c => by
      by_cases hc : ∃ x₀ ∈ S, g x₀ = c
      · obtain ⟨x₀, hx₀S, hx₀⟩ := hc
        refine ⟨Finset.Icc (cellIdx n (F x₀ - r)) (cellIdx n (F x₀ + r)) ×ˢ {c}, ?_,
          fun x hxS hx => ?_⟩
        · rw [Finset.card_product, Finset.card_singleton, mul_one]
          have := card_Icc_cellIdx_le n (a := F x₀ - r) (b := F x₀ + r) (by linarith)
          rwa [show F x₀ + r - (F x₀ - r) = 2 * r by ring] at this
        · have hd := h x hxS x₀ hx₀S (hx.trans hx₀.symm)
          rw [abs_le] at hd
          refine Finset.mem_product.2 ⟨cellIdx_mem_Icc ⟨by linarith, by linarith⟩, ?_⟩
          exact Finset.mem_singleton.2 hx
      · refine ⟨∅, by simp, fun x hxS hx => absurd ⟨x, hxS, hx⟩ hc⟩
  have hpos : (0 : ℝ) < ((⌊2 ^ n * (2 * r)⌋₊ + 2 : ℕ) : ℝ) := by positivity
  have hlog := Real.log_le_log hpos (card_bound_le n (by linarith : 0 ≤ 2 * r))
  unfold cent
  linarith

end RealLabels

/-! ### Labellings with values in `𝒫_k` -/

section VecLabels

variable {X : Type*} [MeasurableSpace X] {θ : Measure X} {k : ℕ}

/-- The cell indices of the points of a box lie in the box of indices. -/
theorem cellIdxVec_mem_piFinset {n : ℕ} {a b : Fin (k + 1) → ℝ} {q : Poly k}
    (hq : ∀ j, q j ∈ Icc (a j) (b j)) :
    cellIdxVec n q ∈ Fintype.piFinset fun j => Finset.Icc (cellIdx n (a j)) (cellIdx n (b j)) :=
  Fintype.mem_piFinset.2 fun j => cellIdx_mem_Icc (hq j)

/-- A labelling `cellIdxVec n ∘ F` with `F` almost surely in a box has finite labels. -/
theorem finiteLabels_cellIdxVec_comp {F : X → Poly k} {a b : Fin (k + 1) → ℝ} (n : ℕ)
    (h : ∀ᵐ x ∂θ, ∀ j, F x j ∈ Icc (a j) (b j)) : FiniteLabels θ (cellIdxVec n ∘ F) :=
  finiteLabels_of_ae_mem_finset _ (by
    filter_upwards [h] with x hx
    exact cellIdxVec_mem_piFinset hx)

/-- The coordinates of `q` are bounded by its norm. -/
theorem abs_apply_le_norm (q : Poly k) (j : Fin (k + 1)) : |q j| ≤ ‖q‖ := by
  have := PiLp.norm_apply_le q j
  rwa [Real.norm_eq_abs] at this

/-- A labelling `cellIdxVec n ∘ F` with `‖F‖` almost surely at most `R` has finite labels. -/
theorem finiteLabels_cellIdxVec_comp_of_norm_le {F : X → Poly k} {R : ℝ} (n : ℕ)
    (h : ∀ᵐ x ∂θ, ‖F x‖ ≤ R) : FiniteLabels θ (cellIdxVec n ∘ F) :=
  finiteLabels_cellIdxVec_comp (a := fun _ => -R) (b := fun _ => R) n (by
    filter_upwards [h] with x hx j
    have := (abs_apply_le_norm (F x) j).trans hx
    rw [abs_le] at this
    exact ⟨this.1, this.2⟩)

/-- The cell index on `𝒫_k` is measurable. -/
theorem measurable_cellIdxVec' (n : ℕ) : Measurable (cellIdxVec (k := k) n) :=
  measurable_cellIdxVec n

variable [IsProbabilityMeasure θ]

/-- The basic commensurability bound for labellings with values in `𝒫_k`: if on a set `S` of full
measure `g x = g x'` forces `|F x j - F x' j| ≤ r` for all `j`, then
`H(θ, F⁻¹ 𝒟_n) ≤ H(θ, g) + (k + 1) log (2^n (2r) + 2)`. -/
theorem ent_cellIdxVec_comp_le {L : Type*} [MeasurableSpace L] [MeasurableSingletonClass L]
    [Countable L] {F : X → Poly k} {g : X → L} (hF : Measurable F) (hg : Measurable g)
    (n : ℕ) (hfinF : FiniteLabels θ (cellIdxVec n ∘ F)) (hfing : FiniteLabels θ g) {S : Set X}
    (hS : MeasurableSet S) (hSθ : θ Sᶜ = 0) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ x ∈ S, ∀ x' ∈ S, g x = g x' → ∀ j, |F x j - F x' j| ≤ r) :
    ent θ (cellIdxVec n ∘ F) ≤ ent θ g + (k + 1) * Real.log (2 ^ n * (2 * r) + 2) := by
  classical
  set N : ℕ := ⌊2 ^ n * (2 * r)⌋₊ + 2
  have key := ent_le_ent_add_log_of_fiber_card_on ((measurable_cellIdxVec n).comp hF) hg hfinF
    hfing hS hSθ (N := N ^ (k + 1)) fun c => by
      by_cases hc : ∃ x₀ ∈ S, g x₀ = c
      · obtain ⟨x₀, hx₀S, hx₀⟩ := hc
        refine ⟨Fintype.piFinset fun j =>
          Finset.Icc (cellIdx n (F x₀ j - r)) (cellIdx n (F x₀ j + r)), ?_, fun x hxS hx => ?_⟩
        · rw [Fintype.card_piFinset]
          calc ∏ j, (Finset.Icc (cellIdx n (F x₀ j - r)) (cellIdx n (F x₀ j + r))).card
              ≤ ∏ _j : Fin (k + 1), N := Finset.prod_le_prod fun j _ => by
                have := card_Icc_cellIdx_le n (a := F x₀ j - r) (b := F x₀ j + r) (by linarith)
                rwa [show F x₀ j + r - (F x₀ j - r) = 2 * r by ring] at this
            _ = N ^ (k + 1) := by simp
        · refine cellIdxVec_mem_piFinset fun j => ?_
          have hd := h x hxS x₀ hx₀S (hx.trans hx₀.symm) j
          rw [abs_le] at hd
          exact ⟨by linarith, by linarith⟩
      · refine ⟨∅, by simp, fun x hxS hx => absurd ⟨x, hxS, hx⟩ hc⟩
  refine key.trans (add_le_add le_rfl ?_)
  have hpos : (0 : ℝ) < (N : ℝ) := by positivity
  rw [Nat.cast_pow, Real.log_pow]
  push_cast
  exact mul_le_mul_of_nonneg_left (Real.log_le_log hpos (card_bound_le n (by linarith)))
    (by positivity)

/-- The cardinality bound for labellings with values in `𝒫_k`: if every coordinate of `F` lies
almost surely in an interval of length `ℓ`, then `H(θ, F⁻¹ 𝒟_n) ≤ (k + 1) log (2^n ℓ + 2)`. -/
theorem ent_cellIdxVec_comp_le_log {F : X → Poly k} (hF : Measurable F) {a : Fin (k + 1) → ℝ}
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (n : ℕ) (h : ∀ᵐ x ∂θ, ∀ j, F x j ∈ Icc (a j) (a j + ℓ)) :
    ent θ (cellIdxVec n ∘ F) ≤ (k + 1) * Real.log (2 ^ n * ℓ + 2) := by
  classical
  refine (ent_le_log_of_ae_mem ((measurable_cellIdxVec n).comp hF)
    (Fintype.piFinset fun j => Finset.Icc (cellIdx n (a j)) (cellIdx n (a j + ℓ))) ?_).trans ?_
  · filter_upwards [h] with x hx
    exact cellIdxVec_mem_piFinset hx
  · rw [Fintype.card_piFinset]
    set N : ℕ := ⌊2 ^ n * ℓ⌋₊ + 2
    have hc : ∏ j, (Finset.Icc (cellIdx n (a j)) (cellIdx n (a j + ℓ))).card ≤ N ^ (k + 1) :=
      calc ∏ j, (Finset.Icc (cellIdx n (a j)) (cellIdx n (a j + ℓ))).card
          ≤ ∏ _j : Fin (k + 1), N := Finset.prod_le_prod fun j _ => by
            have := card_Icc_cellIdx_le n (a := a j) (b := a j + ℓ) (by linarith)
            rwa [show a j + ℓ - a j = ℓ by ring] at this
        _ = N ^ (k + 1) := by simp
    have hpos : 0 < ∏ j, (Finset.Icc (cellIdx n (a j)) (cellIdx n (a j + ℓ))).card :=
      Finset.prod_pos fun j _ => Finset.card_pos.2
        ⟨cellIdx n (a j), Finset.mem_Icc.2 ⟨le_rfl, cellIdx_mono n (by linarith)⟩⟩
    have hN : (0 : ℝ) < N := by positivity
    calc Real.log ((∏ j, (Finset.Icc (cellIdx n (a j)) (cellIdx n (a j + ℓ))).card : ℕ) : ℝ)
        ≤ Real.log ((N ^ (k + 1) : ℕ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hc)
      _ = (k + 1) * Real.log N := by rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
      _ ≤ (k + 1) * Real.log (2 ^ n * ℓ + 2) :=
          mul_le_mul_of_nonneg_left (Real.log_le_log hN (card_bound_le n hℓ)) (by positivity)

end VecLabels

end FractalGeometry.Rapaport.Analytic
