module

public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.StrongLaw

set_option maxSynthPendingDepth 3

/-!
The one-sided Bernoulli probability space and the laws of its consecutive
finite blocks. Disjoint blocks are genuinely independent, including when
some alphabet symbols have zero probability.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.BernoulliBlocks`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace ExactOverlaps.Bernoulli

variable {A : Type*} [MeasurableSpace A]

noncomputable def sequenceLaw (p : Measure A) [IsProbabilityMeasure p] : Measure (ℕ → A) :=
  Measure.infinitePi (fun _ : ℕ ↦ p)

instance (p : Measure A) [IsProbabilityMeasure p] : IsProbabilityMeasure (sequenceLaw p) := by
  unfold sequenceLaw
  infer_instance

def shift (ω : ℕ → A) : ℕ → A := fun k ↦ ω (k + 1)

theorem measurable_shift : Measurable (shift : (ℕ → A) → (ℕ → A)) := by
  fun_prop [shift]

omit [MeasurableSpace A] in
theorem shift_iterate (n : ℕ) (ω : ℕ → A) (k : ℕ) :
    shift^[n] ω k = ω (k + n) := by
  induction n generalizing ω k with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', shift, ih]
      congr 1
      omega

theorem measurePreserving_shift (p : Measure A) [IsProbabilityMeasure p] :
    MeasurePreserving shift (sequenceLaw p) (sequenceLaw p) where
  measurable := measurable_shift
  map_eq := Measure.map_infinitePi_infinitePi_of_inj (fun _ _ h ↦ Nat.add_right_cancel h)

/-- A block of length `m` beginning at coordinate `a`. -/
def block (m a : ℕ) (ω : ℕ → A) : Fin m → A := fun k ↦ ω (a + k)

theorem measurable_block (m a : ℕ) : Measurable (block (A := A) m a) := by
  fun_prop [block]

theorem block_map (p : Measure A) [IsProbabilityMeasure p] (m a : ℕ) :
    (sequenceLaw p).map (block m a) = Measure.pi (fun _ : Fin m ↦ p) := by
  have hi : Function.Injective (fun k : Fin m ↦ a + (k : ℕ)) := by
    intro k l h
    exact Fin.ext (Nat.add_left_cancel h)
  change (Measure.infinitePi (fun _ : ℕ ↦ p)).map
    (fun (ω : ℕ → A) (k : Fin m) ↦ ω (a + (k : ℕ))) = _
  rw [Measure.map_infinitePi_infinitePi_of_inj hi, Measure.infinitePi_eq_pi]

theorem block_coordinates_injective {m : ℕ} (hm : 0 < m) (r : ℕ) :
    Function.Injective (fun z : ℕ × Fin m ↦ z.1 * m + r + (z.2 : ℕ)) := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ h
  change j * m + r + (k : ℕ) = j' * m + r + (k' : ℕ) at h
  have h' : (k : ℕ) + j * m = (k' : ℕ) + j' * m := by omega
  have hd := congrArg (fun n ↦ n / m) h'
  simp only [Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt k.isLt,
    Nat.div_eq_of_lt k'.isLt, zero_add] at hd
  subst j'
  have hk : k = k' := Fin.ext (by omega)
  subst k'
  rfl

theorem disjoint_blocks_map (p : Measure A) [IsProbabilityMeasure p]
    {m : ℕ} (hm : 0 < m) (r : ℕ) :
    (sequenceLaw p).map (fun ω j ↦ block m (j * m + r) ω) =
      Measure.infinitePi (fun _ : ℕ ↦ Measure.pi (fun _ : Fin m ↦ p)) := by
  have hcoord := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ ↦ p) (block_coordinates_injective hm r)
  have h := congrArg (Measure.map (MeasurableEquiv.curry ℕ (Fin m) A)) hcoord
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
  have hc := Measure.infinitePi_map_curry (fun _ : ℕ ↦ fun _ : Fin m ↦ p)
  have hh := h.trans hc
  simp only [Measure.infinitePi_eq_pi] at hh
  exact hh

theorem independent_disjoint_blocks (p : Measure A) [IsProbabilityMeasure p]
    {m : ℕ} (hm : 0 < m) (r : ℕ) :
    iIndepFun (fun j ↦ block m (j * m + r)) (sequenceLaw p) := by
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map (fun j ↦ measurable_block m (j * m + r))).2
  simp only [block_map]
  exact disjoint_blocks_map p hm r

/-- The strong law along disjoint translates of a fixed finite block. -/
theorem strongLaw_block (p : Measure A) [IsProbabilityMeasure p]
    {m : ℕ} (hm : 0 < m) (r : ℕ) (g : (Fin m → A) → ℝ)
    (hgm : Measurable g) (hg : Integrable g (Measure.pi (fun _ : Fin m ↦ p))) :
    ∀ᵐ ω ∂sequenceLaw p, Tendsto
      (fun n : ℕ ↦ (∑ j ∈ Finset.range n, g (block m (j * m + r) ω)) / n)
      atTop (𝓝 (∫ y, g y ∂Measure.pi (fun _ : Fin m ↦ p))) := by
  let X : ℕ → (ℕ → A) → ℝ := fun j ω ↦ g (block m (j * m + r) ω)
  have hblock (j : ℕ) : MeasurePreserving (block m (j * m + r)) (sequenceLaw p)
      (Measure.pi (fun _ : Fin m ↦ p)) :=
    ⟨measurable_block _ _, block_map p _ _⟩
  have hint : Integrable (X 0) (sequenceLaw p) := by
    simpa only [X, Function.comp_def] using (hblock 0).integrable_comp_of_integrable hg
  have hind : iIndepFun X (sequenceLaw p) :=
    (independent_disjoint_blocks p hm r).comp (fun _ ↦ g) (fun _ ↦ hgm)
  have hident (j : ℕ) : IdentDistrib (X j) (X 0) (sequenceLaw p) (sequenceLaw p) := by
    refine ⟨(hgm.comp (measurable_block _ _)).aemeasurable,
      (hgm.comp (measurable_block _ _)).aemeasurable, ?_⟩
    change (sequenceLaw p).map (g ∘ block m (j * m + r)) =
      (sequenceLaw p).map (g ∘ block m (0 * m + r))
    rw [← Measure.map_map hgm (measurable_block _ _),
      ← Measure.map_map hgm (measurable_block _ _), block_map, block_map]
  have heq : (∫ ω, X 0 ω ∂sequenceLaw p) =
      ∫ y, g y ∂Measure.pi (fun _ : Fin m ↦ p) := by
    have hmap : AEStronglyMeasurable g ((sequenceLaw p).map (block m (0 * m + r))) := by
      rw [block_map]
      exact hg.aestronglyMeasurable
    rw [← (hblock 0).map_eq, integral_map (measurable_block _ _).aemeasurable hmap]
  simpa only [X, heq] using strong_law_ae_real X hint (fun _ _ hij ↦ hind.indepFun hij) hident

end ExactOverlaps.Bernoulli
