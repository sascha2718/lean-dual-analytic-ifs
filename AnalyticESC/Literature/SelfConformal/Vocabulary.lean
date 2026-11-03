module

public import AnalyticESC.Dimension.Defs
public import AnalyticESC.Literature.Dimension.Exact
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.MeasureTheory.Group.Convolution

@[expose] public section

/-!
# Shared vocabulary for self-conformal measures on the line

Definitions shared by the formalisations of Bowen's theorem, Feng–Hu exact dimensionality,
Hochman's entropy growth theorem and Rapaport's dimension theorem for analytic IFSs on `I = [0,1]`.
The IFS is a family `φ : Fin N → ℝ → ℝ` of real maps, with the hypotheses `AnalyticESC.RapaportHyp φ`
of `AnalyticESC.Dimension.Defs`; `AnalyticESC.realComp φ u` is the composition `φ_u`, outermost
letter first, and `AnalyticESC.I` is the unit interval.

Conventions. Shannon entropy of weight vectors (`AnalyticESC.entropy`), the Lyapunov exponent and
cylinder entropies use natural logarithms. Dyadic entropies `H(θ, 𝒟_n)` use base `2`, so that a
measure on an interval of length `2^{-n}` has `H(θ, 𝒟_{n+m}) ≤ m + O(1)`. The level `𝒟_t` for a
real `t ≥ 0` is `𝒟_{⌊t⌋}`.

Copied from the library `FractalGeometry` (module `FractalGeometry.SelfConformal.Vocabulary`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.SelfConformal

open MeasureTheory Set Filter Topology

/-! ### Dyadic partitions of the line, dyadic entropy and components -/

/-- The index `⌊2^n x⌋` of the level-`n` dyadic cell containing `x`. -/
noncomputable def cellIdx (n : ℕ) (x : ℝ) : ℤ := ⌊(2 : ℝ) ^ n * x⌋

/-- The level-`n` dyadic cell `[k 2^{-n}, (k+1) 2^{-n})`. -/
def cell (n : ℕ) (k : ℤ) : Set ℝ := Ico ((k : ℝ) / 2 ^ n) (((k : ℝ) + 1) / 2 ^ n)

/-- The level-`n` dyadic cell of `x`, Rapaport's `𝒟_n(x)`. -/
def cellOf (n : ℕ) (x : ℝ) : Set ℝ := cell n (cellIdx n x)

/-- The dyadic entropy `H(θ, 𝒟_n) = -∑_k θ(D_k) log₂ θ(D_k)` in bits. -/
noncomputable def dyadicEntropy (θ : Measure ℝ) (n : ℕ) : ℝ :=
  (∑' k : ℤ, Real.negMulLog (θ.real (cell n k))) / Real.log 2

/-- The level-`n` component `θ_{x,n}` of `θ` at `x`: `θ` conditioned on the dyadic cell of `x`.
It is the zero measure when the cell has measure zero or infinity. -/
noncomputable def component (θ : Measure ℝ) (n : ℕ) (x : ℝ) : Measure ℝ :=
  (θ (cellOf n x))⁻¹ • θ.restrict (cellOf n x)

/-- The probability `ℙ_{i ≤ j ≤ i+n} (P j x)` that a property holds for a uniformly random level
`j ∈ {i, …, i + n}` and a `θ`-random point `x`. -/
noncomputable def levelProb (θ : Measure ℝ) (i n : ℕ) (P : ℕ → ℝ → Prop) : ℝ :=
  (∑ j ∈ Finset.Icc i (i + n), θ.real {x | P j x}) / ((n : ℝ) + 1)

/-- The dyadic level `⌊t⌋₊` of a real scale parameter `t`, so that `𝒟_t = 𝒟_{lvl t}`. -/
noncomputable def lvl (t : ℝ) : ℕ := ⌊t⌋₊

/-! ### The symbolic space, Bernoulli measures and the coding map -/

variable {N : ℕ}

/-- The one-step law `∑_i p_i δ_i` on `Fin N` of a weight vector `p`. -/
noncomputable def step (p : Fin N → ℝ) : Measure (Fin N) :=
  ∑ i, ENNReal.ofReal (p i) • Measure.dirac i

theorem isProbabilityMeasure_step {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p) :
    IsProbabilityMeasure (step p) := by
  refine ⟨?_⟩
  simp only [step, Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => (hp.1 i).le, hp.2, ENNReal.ofReal_one]

/-- The Bernoulli measure `β = p^ℕ` on the one-sided shift `(Fin N)^ℕ`. -/
noncomputable def bernoulli (p : Fin N → ℝ) (hp : AnalyticESC.IsProbVec p) :
    Measure (ℕ → Fin N) :=
  haveI := isProbabilityMeasure_step hp
  Measure.infinitePi fun _ : ℕ => step p

instance isProbabilityMeasure_bernoulli {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p) :
    IsProbabilityMeasure (bernoulli p hp) := by
  have := isProbabilityMeasure_step hp
  unfold bernoulli
  infer_instance

/-- The level-`n` cylinder `[u] = {ω : ω|_n = u}`. -/
def cylinder {n : ℕ} (u : Fin n → Fin N) : Set (ℕ → Fin N) := {ω | ∀ k : Fin n, ω k = u k}

/-- The prefix `ω|_n` of `ω` as a word, outermost letter first. -/
def word (ω : ℕ → Fin N) (n : ℕ) : List (Fin N) := List.ofFn fun k : Fin n => ω k

/-- The entropy `H(ν, 𝒞_n)` (nats) of the partition into level-`n` cylinders. -/
noncomputable def cylEntropy (ν : Measure (ℕ → Fin N)) (n : ℕ) : ℝ :=
  ∑ u : Fin n → Fin N, Real.negMulLog (ν.real (cylinder u))

/-- The coding map `Π(ω) = lim_n φ_{ω|_n}(0)` of the system `φ`. -/
noncomputable def coding (φ : Fin N → ℝ → ℝ) (ω : ℕ → Fin N) : ℝ :=
  limUnder atTop fun n => AnalyticESC.realComp φ (word ω n) 0

/-- The self-conformal measure `μ = Π β` of `φ` and `p`, the image of the Bernoulli measure under
the coding map. -/
noncomputable def selfConformal (φ : Fin N → ℝ → ℝ) (p : Fin N → ℝ) (hp : AnalyticESC.IsProbVec p) :
    Measure ℝ :=
  (bernoulli p hp).map (coding φ)

/-- The Bernoulli measure together with its coding, as a measure on `ℝ × (Fin N)^ℕ`. -/
noncomputable def graphMeasure (φ : Fin N → ℝ → ℝ) (p : Fin N → ℝ) (hp : AnalyticESC.IsProbVec p) :
    Measure (ℝ × (ℕ → Fin N)) :=
  (bernoulli p hp).map fun ω => (coding φ ω, ω)

instance isProbabilityMeasure_graphMeasure (φ : Fin N → ℝ → ℝ) {p : Fin N → ℝ}
    (hp : AnalyticESC.IsProbVec p) : IsFiniteMeasure (graphMeasure φ p hp) := by
  unfold graphMeasure
  infer_instance

/-- The disintegration `x ↦ β_x` of the Bernoulli measure along the coding map: the conditional
kernel of `graphMeasure`, so that `β = ∫ β_x dμ(x)` and `β_x` is carried by `Π⁻¹{x}` for
`μ`-a.e. `x`. Rapaport's `β_ω` is `fibre (Π ω)`. -/
noncomputable def fibre [NeZero N] (φ : Fin N → ℝ → ℝ) (p : Fin N → ℝ)
    (hp : AnalyticESC.IsProbVec p) (x : ℝ) : Measure (ℕ → Fin N) :=
  (graphMeasure φ p hp).condKernel x

end FractalGeometry.SelfConformal
