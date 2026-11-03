module

public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option maxSynthPendingDepth 3

/-!
Real affine similarities retain their signed multiplier. The absolute value
of this multiplier is the metric contraction ratio. Keeping the sign is
necessary when conditioning random compositions on their linear part.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.Similarity`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

namespace ExactOverlaps

/-- An invertible affine similarity of the real line. -/
structure RealSimilarity where
  ratio : ℝ
  ratio_ne_zero : ratio ≠ 0
  shift : ℝ

namespace RealSimilarity

instance : CoeFun RealSimilarity (fun _ ↦ ℝ → ℝ) :=
  ⟨fun g x ↦ g.ratio * x + g.shift⟩

@[simp] theorem apply_def (g : RealSimilarity) (x : ℝ) :
    g x = g.ratio * x + g.shift := rfl

/-- The identity similarity. -/
def identity : RealSimilarity := ⟨1, one_ne_zero, 0⟩

/-- Composition is ordered as function composition: `g.comp h x = g (h x)`. -/
def comp (g h : RealSimilarity) : RealSimilarity where
  ratio := g.ratio * h.ratio
  ratio_ne_zero := mul_ne_zero g.ratio_ne_zero h.ratio_ne_zero
  shift := g.ratio * h.shift + g.shift

@[simp] theorem identity_apply (x : ℝ) : identity x = x := by
  simp [identity]

@[simp] theorem comp_apply (g h : RealSimilarity) (x : ℝ) :
    g.comp h x = g (h x) := by
  simp only [comp]
  ring

@[simp] theorem comp_ratio (g h : RealSimilarity) :
    (g.comp h).ratio = g.ratio * h.ratio := rfl

@[simp] theorem comp_shift (g h : RealSimilarity) :
    (g.comp h).shift = g.ratio * h.shift + g.shift := rfl

@[ext] theorem ext {g h : RealSimilarity} (hr : g.ratio = h.ratio)
    (hb : g.shift = h.shift) : g = h := by
  cases g
  cases h
  simp_all

theorem comp_assoc (f g h : RealSimilarity) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  ext <;> simp only [comp_ratio, comp_shift] <;> ring

@[simp] theorem identity_comp (g : RealSimilarity) : identity.comp g = g := by
  ext <;> simp [identity]

@[simp] theorem comp_identity (g : RealSimilarity) : g.comp identity = g := by
  ext <;> simp [identity]

@[fun_prop] theorem continuous (g : RealSimilarity) : Continuous g :=
  (continuous_const.mul continuous_id).add continuous_const

@[fun_prop] theorem measurable (g : RealSimilarity) : Measurable g :=
  g.continuous.measurable

theorem abs_ratio_pos (g : RealSimilarity) : 0 < |g.ratio| :=
  abs_pos.mpr g.ratio_ne_zero

theorem dist_eq (g : RealSimilarity) (x y : ℝ) :
    dist (g x) (g y) = |g.ratio| * dist x y := by
  rw [Real.dist_eq, Real.dist_eq, ← abs_mul]
  congr 1
  ring

theorem abs_apply_le (g : RealSimilarity) (x : ℝ) :
    |g x| ≤ |g.ratio| * |x| + |g.shift| := by
  simpa only [apply_def, abs_mul] using abs_add_le (g.ratio * x) g.shift

theorem injective (g : RealSimilarity) : Function.Injective g := by
  intro x y h
  have hmul : g.ratio * x = g.ratio * y := add_right_cancel h
  exact mul_left_cancel₀ g.ratio_ne_zero hmul

end RealSimilarity
end ExactOverlaps
