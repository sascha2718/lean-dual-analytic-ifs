module

public import AnalyticESC.Literature.Rapaport.Analytic.Dyadic

@[expose] public section

/-!
# Entropy as an average of the entropies of components

M. Hochman, *On self-similar sets with overlaps and inverse theorems for entropy*, Ann. of Math.
180 (2014), Lemma 3.4, as used in Section 3 of A. Rapaport, *Dimension of self-conformal measures
associated to an exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2: for a measure of
bounded support and `n ≥ m ≥ 1`,
`H(θ, 𝒟_n) / n = 𝔼_{0 ≤ i < n} (H(θ_{x,i}, 𝒟_{i+m}) / m) + O(m / n)`.

The argument is a telescoping of the chain rule along a refining sequence of labellings with
bounded conditional entropy per step.

## Main declarations

* `Refining θ f B`: the labellings `f i` refine each other, have finite labels, and
  `H(θ, f (i+1) ∣ f i) ≤ B`.
* `Refining.ent_add_eq`, `Refining.cent_add_eq_sum`: telescoping of the chain rule.
* `abs_sum_sum_shift_sub_le`, `Refining.abs_sum_cent_sub_le`: the averaging identity behind
  Hochman's Lemma 3.4.
* `refining_cellIdx_comp`, `refining_cellIdxVec_comp`: dyadic partitions of `ℝ` and of `𝒫_k`
  pulled back by a map with bounded values.
* `abs_ent_cellIdx_sub_avg_le`, `abs_ent_cellIdxVec_sub_avg_le`: Hochman's Lemma 3.4 on `ℝ`
  and on `𝒫_k`, in nats.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Multiscale`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic

open MeasureTheory ProbabilityTheory Set FractalGeometry.SelfConformal
open scoped ENNReal

/-! ### An averaging identity for sequences -/

/-- For `0 ≤ c ≤ B`, `|∑_{i<n} ∑_{j<m} c (i + j) - m ∑_{i<n} c i| ≤ m² B`. -/
theorem abs_sum_sum_shift_sub_le {c : ℕ → ℝ} {B : ℝ} (hc0 : ∀ i, 0 ≤ c i) (hcB : ∀ i, c i ≤ B)
    (n m : ℕ) :
    |∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, c (i + j) -
        m * ∑ i ∈ Finset.range n, c i| ≤ m * m * B := by
  have hB : 0 ≤ B := (hc0 0).trans (hcB 0)
  have hj : ∀ j, |∑ i ∈ Finset.range n, c (i + j) - ∑ i ∈ Finset.range n, c i| ≤ j * B := by
    intro j
    have e1 := Finset.sum_range_add c j n
    have e2 := Finset.sum_range_add c n j
    rw [add_comm j n] at e1
    have hsum1 : ∑ i ∈ Finset.range n, c (i + j) = ∑ i ∈ Finset.range n, c (j + i) :=
      Finset.sum_congr rfl fun i _ => by rw [add_comm]
    have h1 : 0 ≤ ∑ i ∈ Finset.range j, c (n + i) := Finset.sum_nonneg fun i _ => hc0 _
    have h2 : ∑ i ∈ Finset.range j, c (n + i) ≤ j * B := by
      calc ∑ i ∈ Finset.range j, c (n + i) ≤ ∑ _i ∈ Finset.range j, B :=
            Finset.sum_le_sum fun i _ => hcB _
        _ = j * B := by simp
    have h3 : 0 ≤ ∑ i ∈ Finset.range j, c i := Finset.sum_nonneg fun i _ => hc0 _
    have h4 : ∑ i ∈ Finset.range j, c i ≤ j * B := by
      calc ∑ i ∈ Finset.range j, c i ≤ ∑ _i ∈ Finset.range j, B :=
            Finset.sum_le_sum fun i _ => hcB _
        _ = j * B := by simp
    rw [hsum1, abs_le]
    constructor <;> linarith
  rw [Finset.sum_comm]
  have hm : (m : ℝ) * ∑ i ∈ Finset.range n, c i =
      ∑ _j ∈ Finset.range m, ∑ i ∈ Finset.range n, c i := by simp
  rw [hm, ← Finset.sum_sub_distrib]
  calc |∑ j ∈ Finset.range m, (∑ i ∈ Finset.range n, c (i + j) - ∑ i ∈ Finset.range n, c i)|
      ≤ ∑ j ∈ Finset.range m, |∑ i ∈ Finset.range n, c (i + j) - ∑ i ∈ Finset.range n, c i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range m, (m : ℝ) * B := Finset.sum_le_sum fun j hj' => by
        refine (hj j).trans ?_
        have : (j : ℝ) ≤ m := by exact_mod_cast (Finset.mem_range.1 hj').le
        exact mul_le_mul_of_nonneg_right this hB
    _ = m * m * B := by simp; ring

/-! ### Refining sequences of labellings -/

section Refining

variable {X : Type*} [MeasurableSpace X] {θ : Measure X}
variable {L : Type*} [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L]

/-- A refining sequence of labellings with conditional entropy at most `B` per step: each `f i`
is measurable with finite labels, is a function of `f (i + 1)`, and
`H(θ, f (i + 1) ∣ f i) ≤ B`. -/
structure Refining (θ : Measure X) (f : ℕ → X → L) (B : ℝ) : Prop where
  meas : ∀ i, Measurable (f i)
  fin : ∀ i, FiniteLabels θ (f i)
  factor : ∀ i j, i ≤ j → ∃ φ : L → L, f i = φ ∘ f j
  step_le : ∀ i, cent θ (f (i + 1)) (f i) ≤ B

namespace Refining

variable {f : ℕ → X → L} {B : ℝ}

omit [MeasurableSingletonClass L] [Countable L] in
/-- `H(θ, f j ∣ f i) = H(θ, f j) - H(θ, f i)` for `i ≤ j`. -/
theorem cent_eq_sub (hf : Refining θ f B) {i j : ℕ} (hij : i ≤ j) :
    cent θ (f j) (f i) = ent θ (f j) - ent θ (f i) := by
  obtain ⟨φ, hφ⟩ := hf.factor i j hij
  have h : ent θ (fun x => (f j x, f i x)) = ent θ (f j) :=
    ent_eq_of_injective (φ := fun c => (c, φ c)) (fun _ _ h => (Prod.mk.inj h).1)
      (by rw [hφ]; rfl)
  unfold cent
  rw [h]

omit [MeasurableSingletonClass L] [Countable L] in
/-- Telescoping of the chain rule:
`H(θ, f (i + m)) = H(θ, f i) + ∑_{j<m} H(θ, f_{i+j+1} ∣ f_{i+j})`. -/
theorem ent_add_eq (hf : Refining θ f B) (i m : ℕ) :
    ent θ (f (i + m)) =
      ent θ (f i) + ∑ j ∈ Finset.range m, cent θ (f (i + j + 1)) (f (i + j)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, hf.cent_eq_sub (Nat.le_succ _), ← add_assoc i m 1]
    linarith

omit [MeasurableSingletonClass L] [Countable L] in
/-- `H(θ, f (i + m) ∣ f i) = ∑_{j<m} H(θ, f_{i+j+1} ∣ f_{i+j})`. -/
theorem cent_add_eq_sum (hf : Refining θ f B) (i m : ℕ) :
    cent θ (f (i + m)) (f i) = ∑ j ∈ Finset.range m, cent θ (f (i + j + 1)) (f (i + j)) := by
  rw [hf.cent_eq_sub (Nat.le_add_right i m), hf.ent_add_eq i m]
  ring

variable [IsProbabilityMeasure θ]

/-- The conditional entropy of one refinement step is nonnegative. -/
theorem step_nonneg (hf : Refining θ f B) (i : ℕ) : 0 ≤ cent θ (f (i + 1)) (f i) :=
  cent_nonneg (hf.meas _) (hf.meas _) (hf.fin _) (hf.fin _)

/-- The averaging identity behind Hochman's Lemma 3.4:
`|∑_{i<n} H(θ, f (i + m) ∣ f i) - m (H(θ, f n) - H(θ, f 0))| ≤ m² B`. -/
theorem abs_sum_cent_sub_le (hf : Refining θ f B) (n m : ℕ) :
    |∑ i ∈ Finset.range n, cent θ (f (i + m)) (f i) - m * (ent θ (f n) - ent θ (f 0))| ≤
      m * m * B := by
  set c : ℕ → ℝ := fun j => cent θ (f (j + 1)) (f j)
  have h1 : ∀ i, cent θ (f (i + m)) (f i) = ∑ j ∈ Finset.range m, c (i + j) :=
    fun i => hf.cent_add_eq_sum i m
  have h2 : ent θ (f n) - ent θ (f 0) = ∑ i ∈ Finset.range n, c i := by
    have := hf.ent_add_eq 0 n
    simp only [zero_add] at this
    rw [this]
    ring
  simp_rw [h1]
  rw [h2]
  exact abs_sum_sum_shift_sub_le hf.step_nonneg hf.step_le n m

end Refining

end Refining

/-! ### Dyadic partitions as refining sequences -/

section Dyadic

variable {X : Type*} [MeasurableSpace X] {θ : Measure X} [IsProbabilityMeasure θ]

/-- The dyadic partitions pulled back by a measurable map with values almost surely in
`[a, b]` form a refining sequence with conditional entropy at most `log 6` per step. -/
theorem refining_cellIdx_comp {F : X → ℝ} (hF : Measurable F) {a b : ℝ}
    (h : ∀ᵐ x ∂θ, F x ∈ Icc a b) :
    Refining θ (fun i => cellIdx i ∘ F) (Real.log 6) where
  meas i := (measurable_cellIdx i).comp hF
  fin i := finiteLabels_cellIdx_comp i h
  factor i j hij := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hij
    exact ⟨fun c => c / (2 : ℤ) ^ m, by rw [cellIdx_factor i m]; rfl⟩
  step_le i := by
    have hfin := fun j => finiteLabels_cellIdx_comp (θ := θ) (F := F) j h
    have hle := ent_cellIdx_comp_le (θ := θ) hF ((measurable_cellIdx i).comp hF) (i + 1)
      (hfin _) (hfin i) MeasurableSet.univ (by simp) (r := 1 / 2 ^ i) (by positivity)
      fun x _ x' _ hxx' => (abs_sub_lt_of_cellIdx_eq hxx').le
    have h6 : (2 : ℝ) ^ (i + 1) * (2 * (1 / 2 ^ i)) + 2 = 6 := by
      rw [pow_succ]
      field_simp
      norm_num
    rw [h6] at hle
    have h : ent θ (fun x => ((cellIdx (i + 1) ∘ F) x, (cellIdx i ∘ F) x)) =
        ent θ (cellIdx (i + 1) ∘ F) :=
      ent_eq_of_injective (φ := fun c => (c, c / (2 : ℤ) ^ 1))
        (fun _ _ h => (Prod.mk.inj h).1) (by
          funext x
          simp only [Function.comp_apply]
          rw [cellIdx_eq_ediv i 1])
    unfold cent
    rw [h]
    linarith

/-- The dyadic partitions of `𝒫_k` pulled back by a measurable map with coordinates almost
surely in intervals form a refining sequence with conditional entropy at most `(k + 1) log 6`
per step. -/
theorem refining_cellIdxVec_comp {k : ℕ} {F : X → Poly k} (hF : Measurable F)
    {a b : Fin (k + 1) → ℝ} (h : ∀ᵐ x ∂θ, ∀ j, F x j ∈ Icc (a j) (b j)) :
    Refining θ (fun i => cellIdxVec i ∘ F) ((k + 1) * Real.log 6) where
  meas i := (measurable_cellIdxVec i).comp hF
  fin i := finiteLabels_cellIdxVec_comp i h
  factor i j hij := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hij
    refine ⟨fun c l => c l / (2 : ℤ) ^ m, ?_⟩
    funext x
    funext l
    exact cellIdx_eq_ediv i m _
  step_le i := by
    have hfin := fun j => finiteLabels_cellIdxVec_comp (θ := θ) (F := F) j h
    have hle := ent_cellIdxVec_comp_le (θ := θ) hF ((measurable_cellIdxVec i).comp hF) (i + 1)
      (hfin _) (hfin i) MeasurableSet.univ (by simp) (r := 1 / 2 ^ i) (by positivity)
      fun x _ x' _ hxx' l => (abs_sub_lt_of_cellIdx_eq (congrFun hxx' l)).le
    have h6 : (2 : ℝ) ^ (i + 1) * (2 * (1 / 2 ^ i)) + 2 = 6 := by
      rw [pow_succ]
      field_simp
      norm_num
    rw [h6] at hle
    have h : ent θ (fun x => ((cellIdxVec (i + 1) ∘ F) x, (cellIdxVec i ∘ F) x)) =
        ent θ (cellIdxVec (i + 1) ∘ F) :=
      ent_eq_of_injective (φ := fun c => (c, fun l => c l / (2 : ℤ) ^ 1))
        (fun _ _ h => (Prod.mk.inj h).1) (by
          funext x
          simp only [Function.comp_apply]
          congr 1
          funext l
          exact cellIdx_eq_ediv i 1 _)
    unfold cent
    rw [h]
    linarith

end Dyadic

/-! ### Hochman's Lemma 3.4 -/

section Lemma34

variable {X : Type*} [MeasurableSpace X] {θ : Measure X} [IsProbabilityMeasure θ]

/-- Hochman's Lemma 3.4 for a real-valued map with values in `[a, b]`, in nats:
`|∑_{i<n} 𝔼(H(θ_{F, i}, F⁻¹ 𝒟_{i+m})) - m (H(θ, F⁻¹𝒟_n) - H(θ, F⁻¹ 𝒟_0))| ≤ m² log 6`, where
the expectation is over the components of `θ` for `F⁻¹ 𝒟_i`. -/
theorem abs_sum_cavg_cellIdx_sub_le {F : X → ℝ} (hF : Measurable F) {a b : ℝ}
    (h : ∀ᵐ x ∂θ, F x ∈ Icc a b) (n m : ℕ) :
    |∑ i ∈ Finset.range n, cavg θ (cellIdx i ∘ F) (fun ρ => ent ρ (cellIdx (i + m) ∘ F)) -
        m * (ent θ (cellIdx n ∘ F) - ent θ (cellIdx 0 ∘ F))| ≤ m * m * Real.log 6 := by
  have hr := refining_cellIdx_comp hF h
  have key := hr.abs_sum_cent_sub_le n m
  have he : ∀ i, cent θ (cellIdx (i + m) ∘ F) (cellIdx i ∘ F) =
      cavg θ (cellIdx i ∘ F) (fun ρ => ent ρ (cellIdx (i + m) ∘ F)) := fun i =>
    cent_eq_cavg (hr.meas _) (hr.meas _) (hr.fin _) (hr.fin _)
  simp_rw [he] at key
  exact key

/-- Hochman's Lemma 3.4 for a map with values in `𝒫_k` with coordinates in intervals, in nats. -/
theorem abs_sum_cavg_cellIdxVec_sub_le {k : ℕ} {F : X → Poly k} (hF : Measurable F)
    {a b : Fin (k + 1) → ℝ} (h : ∀ᵐ x ∂θ, ∀ j, F x j ∈ Icc (a j) (b j)) (n m : ℕ) :
    |∑ i ∈ Finset.range n,
        cavg θ (cellIdxVec i ∘ F) (fun ρ => ent ρ (cellIdxVec (i + m) ∘ F)) -
        m * (ent θ (cellIdxVec n ∘ F) - ent θ (cellIdxVec 0 ∘ F))| ≤
      m * m * ((k + 1) * Real.log 6) := by
  have hr := refining_cellIdxVec_comp hF h
  have key := hr.abs_sum_cent_sub_le n m
  have he : ∀ i, cent θ (cellIdxVec (i + m) ∘ F) (cellIdxVec i ∘ F) =
      cavg θ (cellIdxVec i ∘ F) (fun ρ => ent ρ (cellIdxVec (i + m) ∘ F)) := fun i =>
    cent_eq_cavg (hr.meas _) (hr.meas _) (hr.fin _) (hr.fin _)
  simp_rw [he] at key
  exact key

end Lemma34

end FractalGeometry.Rapaport.Analytic
