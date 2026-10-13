module

public import Mathlib
public import AnalyticESC.Main.Example
public import AnalyticESC.Conjugation.PeriodicPoints
public import AnalyticESC.Generic.OpenDense
public import AnalyticESC.Dimension.NaturalMeasure
public import AnalyticESC.Dimension.OpenDense
public import AnalyticESC.Dimension.Example
public import AnalyticESC.Dimension.Lq

@[expose] public section

/-!
# Proofs of the audited statements

Proofs of the theorems stated in `Challenge.lean`, for B. Bárány, I. Kolossváry and
S. Troscheit, *On exponential separation of analytic self-conformal sets on the real line*,
as stated in `../analytic.tex`. This module repeats the challenge vocabulary with
the same names, types and values, without importing `Challenge.lean`, and proves each audited theorem from
the `AnalyticESC` library. The lemmas below identify the neighbourhood, finite sums, guarded
quotients and restricted limits with the library's versions.
-/

namespace Challenge

open Set Metric

/-- The unit interval `I = [0,1]`. -/
abbrev I : Set ℝ := Icc 0 1

/-- The open `δ`-neighbourhood `B_δ = {z ∈ ℂ : ∃ x ∈ I, |z - x| < δ}` of `I` in `ℂ`. -/
def nbhd (δ : ℝ) : Set ℂ := {z | ∃ x ∈ I, ‖z - (x : ℂ)‖ < δ}

/-- The class `S^ω_ε(I)` of Section 1.1, for a map given by its holomorphic extension:
(A) `f` is complex analytic on `B_{2ε}` and real at the real points of `B_{2ε}`;
(B) `f(I) ⊆ I` and `f(cl B_ε) ⊆ B_ε`; (C) `0 < |f'(z)| < 1` for `z ∈ cl B_ε`. -/
structure InClass (ε : ℝ) (f : ℂ → ℂ) : Prop where
  differentiableOn : DifferentiableOn ℂ f (nbhd (2 * ε))
  im_eq_zero : ∀ x : ℝ, (x : ℂ) ∈ nbhd (2 * ε) → (f x).im = 0
  re_mem_I : ∀ x ∈ I, (f x).re ∈ I
  mapsTo : ∀ z ∈ closure (nbhd ε), f z ∈ nbhd ε
  deriv_ne_zero : ∀ z ∈ closure (nbhd ε), deriv f z ≠ 0
  norm_deriv_lt_one : ∀ z ∈ closure (nbhd ε), ‖deriv f z‖ < 1

variable {N : ℕ}

/-- `f_w = f_{w₁} ∘ ⋯ ∘ f_{w_k}` for a finite word `w`, with `f_∅ = id`. -/
def comp (f : Fin N → ℂ → ℂ) (w : List (Fin N)) : ℂ → ℂ := w.foldr (fun i g => f i ∘ g) id

/-- `sup_{x ∈ [0,1]} |f_i(x) - f_j(x)|` for finite words `i` and `j`. -/
noncomputable def supDist (f : Fin N → ℂ → ℂ) (i j : List (Fin N)) : ℝ :=
  ⨆ x : I, ‖comp f i x - comp f j x‖

/-- The strong exponential separation condition (Definition 1.2): there is `c > 0` with
`sup_{x ∈ [0,1]} |f_i(x) - f_j(x)| ≥ c^n` for all distinct `i, j ∈ Σ_n` and all `n`. -/
def SESC (f : Fin N → ℂ → ℂ) : Prop :=
  ∃ c > 0, ∀ n, ∀ i j : Fin n → Fin N, i ≠ j → c ^ n ≤ supDist f (List.ofFn i) (List.ofFn j)

/-- Nonvanishing of the derivatives at every finite orbit of a point of `I`. -/
def NonzeroDerivatives (f : Fin N → ℂ → ℂ) : Prop :=
  ∀ (i : Fin N) (w : List (Fin N)) (x : I), deriv (f i) (comp f w x) ≠ 0

/-- The distortion `f''/f'`. -/
noncomputable def nonlin (g : ℂ → ℂ) (z : ℂ) (_h : deriv g z ≠ 0) : ℂ :=
  deriv (deriv g) z / deriv g z

/-- The dual natural projection `H_w` of (1.4) for a finite word `w`. The term with index `n`
(from `0`) is `(f_i''/f_i')(f_{v^←}(z)) · f_{v^←}'(z)`, where `v` is the prefix of the first `n`
letters, `i` the next letter and `f_{v^←} = f_{v_n} ∘ ⋯ ∘ f_{v_1}`. -/
noncomputable def dualProjFin (f : Fin N → ℂ → ℂ) (hd : NonzeroDerivatives f)
    (w : List (Fin N)) (x : I) : ℂ :=
  ∑ n : Fin w.length,
    nonlin (f (w.get n)) (comp f (w.take n).reverse x) (hd (w.get n) (w.take n).reverse x) *
      deriv (comp f (w.take n).reverse) x

/-- The dual natural projection `H_w` of (1.4) for an infinite word `w`. -/
noncomputable def dualProjInf (f : Fin N → ℂ → ℂ) (hd : NonzeroDerivatives f)
    (w : ℕ → Fin N) (x : I) : ℂ :=
  ∑' n, nonlin (f (w n)) (comp f (List.ofFn fun k : Fin n => w k).reverse x)
    (hd (w n) (List.ofFn fun k : Fin n => w k).reverse x) *
      deriv (comp f (List.ofFn fun k : Fin n => w k).reverse) x

/-- The constant `c_max` of (1.7): the supremum of `|f_i'|` over `cl B_ε` and `i`. -/
noncomputable def cmax (ε : ℝ) (f : Fin N → ℂ → ℂ) : ℝ :=
  ⨆ (i : Fin N) (z : closure (nbhd ε)), ‖deriv (f i) z‖

/-- `β = sup_{x ∈ [0,1], i} |f_i''/f_i'(x)|` (Proposition 1.8). -/
noncomputable def beta (f : Fin N → ℂ → ℂ) (hd : NonzeroDerivatives f) : ℝ :=
  ⨆ (x : I) (i : Fin N), ‖nonlin (f i) x (hd i [] x)‖

/-- The maps `f₁(x) = x/8`, `f₂(x) = x/8 + x²/32`, `f₃(x) = x/16 + x²/32 + 29/32` of the example in
Section 1.2.2. -/
noncomputable def exampleMaps : Fin 3 → ℂ → ℂ :=
  ![fun z => z / 8, fun z => z / 8 + z ^ 2 / 32, fun z => z / 16 + z ^ 2 / 32 + 29 / 32]

/-- The natural projection `π(w) = lim_{n → ∞} f_{w₁ ⋯ wₙ}(0)` of (1.3). -/
noncomputable def natProj (f : Fin N → ℂ → ℂ) (w : ℕ → Fin N) : ℝ :=
  Filter.limUnder Filter.atTop fun n => (comp f (List.ofFn fun k : Fin n => w k) 0).re

/-- The attractor `Λ = π(Σ)`. -/
def attractor (f : Fin N → ℂ → ℂ) : Set ℝ := range (natProj f)

/-- `g` is an analytic, invertible map on `[0,1]` (Definition 1.9): analytic on a neighbourhood
of each point of `[0,1]` and injective on `[0,1]`. -/
def IsAnalyticCoord (g : ℝ → ℝ) : Prop := AnalyticOnNhd ℝ g I ∧ InjOn g I

/-- The maps `F_j` of `[0,1]` are conjugated to a self-similar IFS (Definition 1.9): for an
analytic invertible `g`, `g ∘ F_j ∘ g⁻¹` is the similarity `y ↦ λ_j y + t_j` with
`λ_j ∈ (-1,1) \ {0}`, that is, `g(F_j(x)) = λ_j g(x) + t_j` on `[0,1]`. -/
def ConjSelfSimilar {M : ℕ} (F : Fin M → ℝ → ℝ) : Prop :=
  ∃ g, IsAnalyticCoord g ∧ ∃ lam t : Fin M → ℝ, ∀ j,
    lam j ≠ 0 ∧ |lam j| < 1 ∧ ∀ x ∈ I, g (F j x) = lam j * g x + t j

/-- The infinite word `w w w ⋯` for a nonempty finite word `w`. -/
def periodic {m : ℕ} (hm : 0 < m) (w : Fin m → Fin N) : ℕ → Fin N :=
  fun n => w ⟨n % m, Nat.mod_lt n hm⟩

/-- The `𝒞²` distance: the maximum over maps of the sum of the uniform distances
between their values, first derivatives and second derivatives on `[0,1]` (Section 1.1). -/
noncomputable def d2 (f g : Fin N → ℂ → ℂ) : ℝ :=
  ⨆ i, (⨆ x : I, ‖f i x - g i x‖) +
    (⨆ x : I, ‖deriv (f i) x - deriv (g i) x‖) +
    (⨆ x : I, ‖deriv (deriv (f i)) x - deriv (deriv (g i)) x‖)

/-- The space `𝔖_N` of Section 1.1: IFSs whose maps lie in `S^ω_ε(I)` for some `ε > 0`, which may
depend on the system. -/
def InUnionClass (f : Fin N → ℂ → ℂ) : Prop := ∃ ε > 0, ∀ i, InClass ε (f i)

section Dimension

open MeasureTheory Filter Topology

/-- Division with a proof that the denominator is nonzero. -/
noncomputable def divide (a b : ℝ) (_hb : b ≠ 0) : ℝ := a / b

/-- The scales `0 < r < 1`, on which `log r` is nonzero. -/
abbrev Scale := {r : ℝ // 0 < r ∧ r < 1}

/-- Scales tending to zero from above. -/
def scaleZero : Filter Scale := comap Subtype.val (𝓝[>] (0 : ℝ))

/-- The logarithmic ratio at a scale in `(0,1)`. -/
noncomputable def logRatio (a : ℝ) (r : Scale) : ℝ :=
  divide (Real.log a) (Real.log r) (Real.log_neg r.2.1 r.2.2).ne

/-! ### Dimension theory (Sections 1.2.1 and 1.2.2) -/

/-- The exponential separation condition (ESC): there is `c > 0` with
`sup_{x ∈ [0,1]} |f_i(x) - f_j(x)| ≥ c^n` for all distinct `i, j ∈ Σ_n`, for infinitely many
`n`. -/
def ESC (f : Fin N → ℂ → ℂ) : Prop :=
  ∃ c > 0, ∃ᶠ n in atTop, ∀ i j : Fin n → Fin N, i ≠ j →
    c ^ n ≤ supDist f (List.ofFn i) (List.ofFn j)

/-- The sum `∑_{w ∈ Σ_n} (sup_{x ∈ I} |f_w'(x)|)^t`. The pressure is
`P(t) = lim_n log(pressureSum f t n) / n`; its zero is `s(Φ)` (Section 1.2.1). -/
noncomputable def pressureSum (f : Fin N → ℂ → ℂ) (t : ℝ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → Fin N, (⨆ x : I, ‖deriv (comp f (List.ofFn w)) x‖) ^ t

/-- The normalized logarithmic pressure sum, at positive word length `n + 1`. -/
noncomputable def pressureRatio (f : Fin N → ℂ → ℂ) (t : ℝ) (n : ℕ) : ℝ :=
  divide (Real.log (pressureSum f t (n + 1))) ((n + 1 : ℕ) : ℝ)
    (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))

/-- The entropy `H(p) = -∑_i p_i log p_i` of a probability vector. -/
noncomputable def entropy (p : Fin N → ℝ) : ℝ := -∑ i, p i * Real.log (p i)

/-- `p` is a positive probability vector. -/
def IsProbVec (p : Fin N → ℝ) : Prop := (∀ i, 0 < p i) ∧ ∑ i, p i = 1

/-- The Lyapunov exponent `χ(Φ, p) = -∑_i p_i ∫ log|f_i'| dμ` of Section 1.2.1, for the measure
`μ`, with the derivatives of the real maps `x ↦ f_i(x)`. -/
noncomputable def lyapunov (f : Fin N → ℂ → ℂ) (p : Fin N → ℝ) (μ : Measure ℝ) : ℝ :=
  -∑ i, p i * ∫ x, Real.log |deriv (fun y : ℝ => (f i y).re) x| ∂μ

/-- `μ` is the self-conformal measure of `Φ` and `p`, (1.2): a Borel probability measure on
`[0,1]` with `μ = ∑_i p_i μ ∘ f_i⁻¹`. -/
def IsSelfConformal (f : Fin N → ℂ → ℂ) (p : Fin N → ℝ) (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ Iᶜ = 0 ∧
    μ = ∑ i, ENNReal.ofReal (p i) • μ.map (fun x : ℝ => (f i x).re)

/-- Equality in (1.6): the pressure has a unique zero `s(Φ)`, the attractor has Hausdorff
dimension `min{1, s(Φ)}`, and for every positive probability vector `p` the self-conformal measure
`μ_p` has local dimension `min{1, H(p)/χ}` at `μ_p`-almost every point. -/
def DimEquality (f : Fin N → ℂ → ℂ) : Prop :=
  (∃ s : ℝ, (∀ t, Tendsto (pressureRatio f t) atTop (𝓝 0) ↔ t = s) ∧
      dimH (attractor f) = ENNReal.ofReal (min 1 s)) ∧
    ∀ p : Fin N → ℝ, IsProbVec p → ∀ μ : Measure ℝ, IsSelfConformal f p μ →
      ∀ hχ : lyapunov f p μ ≠ 0,
      ∀ᵐ x ∂μ, Tendsto (fun r : Scale => logRatio (μ.real (closedBall x r)) r) scaleZero
        (𝓝 (min 1 (divide (entropy p) (lyapunov f p μ) hχ)))

/-- The potential `φ_s(ω) = s log|f'_{ω₀}(π(σω))|` on `Σ = (Fin N)^ℕ`, where `σ` is the left
shift. -/
noncomputable def potential (f : Fin N → ℂ → ℂ) (s : ℝ) (ω : ℕ → Fin N) : ℝ :=
  s * Real.log ‖deriv (f (ω 0)) (natProj f fun i => ω (i + 1))‖

/-- `ν` is a Gibbs measure for the potential `φ` on `Σ = (Fin N)^ℕ` in Bowen's sense: there are
`c₁, c₂ > 0` and `P` with `c₁ ≤ ν[x₀ ⋯ x_{m-1}] / exp(-P m + ∑_{k<m} φ(σ^k x)) ≤ c₂` for every
`x ∈ Σ` and `m ≥ 0`, where `σ` is the left shift. -/
def IsGibbsMeasure (φ : (ℕ → Fin N) → ℝ) (ν : Measure (ℕ → Fin N)) : Prop :=
  ∃ c₁ > 0, ∃ c₂ > 0, ∃ P : ℝ, ∀ (x : ℕ → Fin N) (m : ℕ),
    c₁ * Real.exp (-P * m + ∑ k ∈ Finset.range m, φ (fun i => x (i + k))) ≤
        ν.real {y | ∀ i < m, y i = x i} ∧
      ν.real {y | ∀ i < m, y i = x i} ≤
        c₂ * Real.exp (-P * m + ∑ k ∈ Finset.range m, φ (fun i => x (i + k)))

/-- The `L^q` dimension `D_μ(q) = τ_μ(q)/(q - 1)` of Section 1.2.2, where
`τ_μ(q) = liminf_{r → 0} log(∑_{k ∈ ℤ} μ([kr, (k+1)r))^q) / log r`. -/
noncomputable def lqDim (μ : Measure ℝ) (q : ℝ) (hq : q - 1 ≠ 0) : ℝ :=
  divide (liminf (fun r : Scale =>
    logRatio (∑' k : ℤ, μ.real (Ico (k * (r : ℝ)) ((k + 1) * (r : ℝ))) ^ q) r)
    scaleZero) (q - 1) hq

/-! ### Cited results

The results that the paper cites are stated as in their sources and are explicit hypotheses of
the theorems that use them. Rapaport's results are stated, as in his paper, for real maps `φ_i`
of `I = [0,1]`. -/

/-- `φ_u = φ_{u₁} ∘ ⋯ ∘ φ_{uₙ}` for real maps and a finite word `u`, with `φ_∅ = id`. -/
def realComp (φ : Fin N → ℝ → ℝ) (u : List (Fin N)) : ℝ → ℝ := u.foldr (fun i g => φ i ∘ g) id

/-- The hypotheses of Rapaport's Theorem 1.2 and Corollary 1.3: `φ_i(I) ⊆ I`, each `φ_i` is real
analytic on a neighbourhood of each point of `I`, `0 < |φ_i'(x)| < 1` for `x ∈ I`, the maps have no
common fixed point in `I`, and the system is exponentially separated: there is `c > 0` such that
for infinitely many `n`, `sup_{x ∈ I} |φ_u(x) - φ_v(x)| ≥ c^n` for all distinct `u, v` of length
`n`. -/
structure RapaportHyp (φ : Fin N → ℝ → ℝ) : Prop where
  mapsTo : ∀ i, MapsTo (φ i) I I
  analytic : ∀ i, AnalyticOnNhd ℝ (φ i) I
  deriv_pos : ∀ i, ∀ x ∈ I, 0 < |deriv (φ i) x|
  deriv_lt_one : ∀ i, ∀ x ∈ I, |deriv (φ i) x| < 1
  no_common_fixed_point : ¬ ∃ x ∈ I, ∀ i, φ i x = x
  exp_separated : ∃ c > 0, ∃ᶠ n in atTop, ∀ u v : Fin n → Fin N, u ≠ v →
    c ^ n ≤ ⨆ x : I, |realComp φ (List.ofFn u) x - realComp φ (List.ofFn v) x|

/-- **Cited result.** R. Bowen, *Equilibrium states and the ergodic theory of Anosov
diffeomorphisms*, Lecture Notes in Mathematics 470, Springer, 1975, Theorem 1.4, for the one-sided
full shift on `N ≥ 1` symbols: a potential `φ` with
`sup{|φ(x) - φ(y)| : x_i = y_i for i < k} ≤ b α^k` for all `k`, where `b > 0` and `0 < α < 1`, has a
Gibbs measure. Bowen states the theorem for two-sided mixing subshifts of finite type; a potential
of the coordinates `i ≥ 0` has the same variations, and the image of the two-sided Gibbs measure
under `x ↦ (x_i)_{i ≥ 0}` has the same cylinder measures. -/
def BowenGibbsStatement : Prop :=
  ∀ {N : ℕ}, 0 < N → ∀ (φ : (ℕ → Fin N) → ℝ) {b α : ℝ}, 0 < b → 0 < α → α < 1 →
    (∀ (k : ℕ) (x y : ℕ → Fin N), (∀ i < k, x i = y i) → |φ x - φ y| ≤ b * α ^ k) →
    ∃ ν : Measure (ℕ → Fin N), IsProbabilityMeasure ν ∧ IsGibbsMeasure φ ν

/-- **Cited result.** A. Rapaport, *Dimension of self-conformal measures associated to an
exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2, Theorem 1.2, together with the exact
dimensionality of self-conformal measures, D.-J. Feng and H. Hu, *Dimension theory of iterated
function systems*, Comm. Pure Appl. Math. 62 (2009): under `RapaportHyp`, for a positive
probability vector `p`, the self-conformal measure `μ = ∑_i p_i φ_i μ` on `I` satisfies
`lim_{δ → 0} log μ(B(x,δ)) / log δ = min{1, H(p)/χ}` for `μ`-almost every `x`, where
`H(p) = -∑ p_i log p_i` and `χ = -∑ p_i ∫ log|φ_i'| dμ`. -/
def RapaportMeasureStatement : Prop :=
  ∀ {N : ℕ} (φ : Fin N → ℝ → ℝ), RapaportHyp φ →
    ∀ p : Fin N → ℝ, (∀ i, 0 < p i) → ∑ i, p i = 1 →
    ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ Iᶜ = 0 →
      μ = ∑ i, ENNReal.ofReal (p i) • μ.map (φ i) →
      ∀ hχ : (-∑ i, p i * ∫ y, Real.log |deriv (φ i) y| ∂μ) ≠ 0,
      ∀ᵐ x ∂μ, Tendsto (fun r : Scale => logRatio (μ.real (closedBall x r)) r) scaleZero
        (𝓝 (min 1 (divide (-∑ i, p i * Real.log (p i))
          (-∑ i, p i * ∫ y, Real.log |deriv (φ i) y| ∂μ) hχ)))

/-- **Cited result.** A. Rapaport, *Dimension of self-conformal measures associated to an
exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2, Corollary 1.3: under `RapaportHyp`,
the attractor `K`, the nonempty compact set `K ⊆ I` with `K = ⋃_i φ_i(K)`, has Hausdorff dimension
`min{1, s(Φ)}`, where `s(Φ)` is the zero of the pressure
`P(t) = lim_n (1/n) log ∑_{u ∈ Σ_n} (sup_{x ∈ I} |φ_u'(x)|)^t`. -/
def RapaportSetStatement : Prop :=
  ∀ {N : ℕ} (φ : Fin N → ℝ → ℝ), RapaportHyp φ →
    ∀ K : Set ℝ, K.Nonempty → IsCompact K → K ⊆ I → K = ⋃ i, φ i '' K →
    ∀ s : ℝ, Tendsto (fun n : ℕ => divide (Real.log (∑ u : Fin (n + 1) → Fin N,
        (⨆ x : I, |deriv (realComp φ (List.ofFn u)) x|) ^ s)) ((n + 1 : ℕ) : ℝ)
        (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))) atTop (𝓝 0) →
      dimH K = ENNReal.ofReal (min 1 s)

end Dimension

theorem nbhd_eq_lib (δ : ℝ) : nbhd δ = AnalyticESC.nbhd δ := by
  ext z
  simp [nbhd, AnalyticESC.nbhd, mem_thickening_iff, dist_eq_norm]

theorem inClass_iff_lib {ε : ℝ} {f : ℂ → ℂ} :
    InClass ε f ↔ AnalyticESC.InClass ε f := by
  constructor <;> rintro ⟨h1, h2, h3, h4, h5, h6⟩ <;> constructor <;>
    (try simp only [nbhd_eq_lib] at *) <;> assumption

theorem dualProjFin_eq_lib {ε : ℝ} (Φ : AnalyticESC.IFS N ε) (hd : NonzeroDerivatives Φ.f)
    (w : List (Fin N)) (x : I) : dualProjFin Φ.f hd w x = Φ.dualProj (.fin w) x := by
  rw [dualProjFin, Φ.dualProj_fin_eq_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n _
  simp [AnalyticESC.IFS.dualTerm, AnalyticESC.Word.get?, AnalyticESC.Word.take, n.isLt,
    nonlin, comp, AnalyticESC.IFS.nonlin, AnalyticESC.IFS.comp]

/-- The system `(f_i)` as an IFS of the library. -/
noncomputable def toIFS {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i)) :
    AnalyticESC.IFS N ε where
  f := f
  ε_pos := hε
  inClass i := inClass_iff_lib.mp (hf i)

/-- The explicit derivative guard follows from the original class hypotheses. -/
theorem nonzeroDerivatives_of_inClass {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ)
    (hf : ∀ i, InClass ε (f i)) : NonzeroDerivatives f := by
  intro i w x
  exact ((toIFS hε f hf).inClass i).deriv_ne_zero _
    ((toIFS hε f hf).mapsTo_comp_closure w
      (subset_closure (AnalyticESC.ofReal_mem_nbhd hε x.2)))

/-- The contraction bound supplies the other denominator in Proposition 1.8. -/
theorem one_sub_cmax_ne_zero {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ)
    (hf : ∀ i, InClass ε (f i)) : 1 - cmax ε f ≠ 0 := by
  have hc : cmax ε f = (toIFS hε f hf).cmax := by
    unfold cmax
    rw [nbhd_eq_lib]
    rfl
  rw [hc]
  exact (sub_pos.mpr (toIFS hε f hf).cmax_lt_one).ne'

/-- Theorem 1.4. The IFSs in `𝔖_N` that satisfy the strong exponential separation condition
contain a subset `U` of `𝔖_N` that is open and dense in `𝔖_N` for the `𝒞²` metric `d₂`. -/
theorem audit_sesc_open_dense (N : ℕ) :
    ∃ U : Set (Fin N → ℂ → ℂ), (∀ f ∈ U, InUnionClass f ∧ SESC f) ∧
      (∀ f ∈ U, ∃ r > 0, ∀ g, InUnionClass g → d2 f g < r → g ∈ U) ∧
      (∀ f, InUnionClass f → ∀ r > 0, ∃ g ∈ U, d2 f g < r) := by
  have hlib : ∀ f : Fin N → ℂ → ℂ, InUnionClass f → AnalyticESC.InUnionClass f :=
    fun f ⟨ε, hε, hf⟩ => ⟨ε, hε, fun i => inClass_iff_lib.mp (hf i)⟩
  obtain ⟨U, hS, hO, hD⟩ := AnalyticESC.theorem_1_4 N
  refine ⟨U, fun f hf => ?_, fun f hf => ?_, fun f hf r hr => hD f (hlib f hf) r hr⟩
  · obtain ⟨ε, ⟨g, hε, hg⟩, rfl, hSE⟩ := hS f hf
    exact ⟨⟨ε, hε, fun i => inClass_iff_lib.mpr (hg i)⟩, hSE⟩
  · obtain ⟨r, hr, h⟩ := hO f hf
    exact ⟨r, hr, fun g hg hd => h g (hlib g hg) hd⟩

/-- Theorem 1.5. Let `Φ = (f_i)_{i ∈ Fin N}` be an analytic IFS in `𝔖_N`. If
`sup_{x ∈ [0,1]} |H_i(x) - H_j(x)| > 0` for all distinct `i, j ∈ Σ ∪ Σ_*` with `|i| = |j|`, then `Φ`
satisfies the strong exponential separation condition. Words of equal length are either both
finite of the same length or both infinite. -/
theorem audit_sesc_of_dualProj {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ)
    (hf : ∀ i, InClass ε (f i)) (hd : NonzeroDerivatives f)
    (hfin : ∀ n, ∀ i j : Fin n → Fin N, i ≠ j →
      0 < ⨆ x : I, ‖dualProjFin f hd (List.ofFn i) x -
        dualProjFin f hd (List.ofFn j) x‖)
    (hinf : ∀ i j : ℕ → Fin N, i ≠ j →
      0 < ⨆ x : I, ‖dualProjInf f hd i x - dualProjInf f hd j x‖) :
    SESC f := by
  refine (toIFS hε f hf).theorem_1_5 ?_
  intro i j hij hlen
  cases i with
  | fin u =>
    cases j with
    | fin v =>
      have huv : u ≠ v := fun h => hij (h ▸ rfl)
      have hl : u.length = v.length := by
        have h' : (u.length : ℕ∞) = v.length := hlen
        exact_mod_cast h'
      have := hfin u.length u.get (fun k => v.get (Fin.cast hl k)) (by
        intro h
        apply huv
        apply List.ext_get hl
        intro k hk _
        exact congrFun h ⟨k, hk⟩)
      rw [List.ofFn_get] at this
      have hv : List.ofFn (fun k : Fin u.length => v.get (Fin.cast hl k)) = v := by
        apply List.ext_get (by simp [hl])
        intro k _ _
        simp
      rw [hv] at this
      simp only [← dualProjFin_eq_lib (toIFS hε f hf) hd]
      exact this
    | inf w => exact absurd hlen (by simp [AnalyticESC.Word.length])
  | inf w =>
    cases j with
    | fin v => exact absurd hlen (by simp [AnalyticESC.Word.length])
    | inf w' =>
      exact hinf w w' (fun h => hij (h ▸ rfl))

/-- Proposition 1.8. Let `Φ = (f_i)_{i ∈ Fin N}` be an analytic IFS in `𝔖_N` with `N ≥ 2` maps.
Suppose that there is `α > 0` such that for all `i ≠ j` there is `x ∈ [0,1]` with
`|f_i''/f_i'(x) - f_j''/f_j'(x)| ≥ α`. Then `β > 0`, and if `α > 2β c_max/(1 - c_max)`, then
`sup_{x ∈ [0,1]} |H_i(x) - H_j(x)| > 0` for all distinct `i, j ∈ Σ ∪ Σ_*` with `|i| = |j|`, and `Φ`
satisfies the strong exponential separation condition. The hypothesis `N ≥ 2` ensures `β > 0`,
which can fail for a singleton IFS. -/
theorem audit_example_criterion {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ)
    (hf : ∀ i, InClass ε (f i)) (hd : NonzeroDerivatives f) (hN : 2 ≤ N) {α : ℝ} (hα : 0 < α)
    (hc : 1 - cmax ε f ≠ 0)
    (hsep : ∀ i j : Fin N, i ≠ j → ∃ x : I, α ≤ ‖nonlin (f i) x (hd i [] x) - nonlin (f j) x (hd j [] x)‖) :
    0 < beta f hd ∧ (divide (2 * beta f hd * cmax ε f) (1 - cmax ε f) hc < α →
      (∀ n, ∀ i j : Fin n → Fin N, i ≠ j →
        0 < ⨆ x : I, ‖dualProjFin f hd (List.ofFn i) x -
          dualProjFin f hd (List.ofFn j) x‖) ∧
      (∀ i j : ℕ → Fin N, i ≠ j →
        0 < ⨆ x : I, ‖dualProjInf f hd i x - dualProjInf f hd j x‖) ∧
      SESC f) := by
  have hsep' : ∀ i j : Fin N, i ≠ j → ∃ x ∈ AnalyticESC.I,
      α ≤ ‖(toIFS hε f hf).nonlin i x - (toIFS hε f hf).nonlin j x‖ := by
    intro i j hij
    obtain ⟨x, hx⟩ := hsep i j hij
    exact ⟨x, x.2, hx⟩
  obtain ⟨hβ, h⟩ := (toIFS hε f hf).proposition_1_8 hN hα hsep'
  refine ⟨hβ, fun hα' => ?_⟩
  have hc_eq : (toIFS hε f hf).cmax = cmax ε f := by
    unfold cmax
    rw [nbhd_eq_lib]
    rfl
  obtain ⟨hne, hS⟩ := h (by rw [hc_eq]; exact hα')
  refine ⟨fun n i j hij => ?_, fun i j hij => hne (.inf i) (.inf j) (fun h => hij (by cases h; rfl)) rfl, hS⟩
  have hfin := hne (.fin (List.ofFn i)) (.fin (List.ofFn j))
    (fun h => hij (List.ofFn_injective (AnalyticESC.Word.fin.inj h))) (by simp)
  simp only [← dualProjFin_eq_lib (toIFS hε f hf) hd] at hfin
  exact hfin

/-- The polynomial example of Section 1.2.2: the system `x/8`, `x/8 + x²/32`, `x/16 + x²/32 + 29/32` lies in
`𝔖_3` for some `ε > 0` and satisfies the strong exponential separation condition. -/
theorem audit_example_sesc : ∃ ε > 0, (∀ i, InClass ε (exampleMaps i)) ∧ SESC exampleMaps := by
  obtain ⟨ε, hε, Φ, hΦ, hS⟩ := AnalyticESC.example_sesc
  obtain ⟨g, gpos, hg⟩ := Φ
  change g = _ at hΦ
  subst hΦ
  exact ⟨ε, hε, fun i => inClass_iff_lib.mpr (hg i), hS⟩

/-- Individual-map linearisation for Theorem 1.12: an analytic coordinate with nonvanishing
derivative conjugates the chosen map `f_i` to a contracting similarity. -/
theorem audit_conj_similarity {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ)
    (hf : ∀ i, InClass ε (f i)) (i : Fin N) :
    ∃ g, IsAnalyticCoord g ∧ (∀ x ∈ I, deriv g x ≠ 0) ∧
      ∃ lam t : ℝ, lam ≠ 0 ∧ |lam| < 1 ∧ ∀ x ∈ I, g (f i x).re = lam * g x + t := by
  exact (toIFS hε f hf).theorem_1_12_similarity i

/-- Theorem 1.12 (a). If the attractor of `Φ` is not a singleton, then `Φ` is conjugated to a
self-similar IFS if and only if `H_i ≡ H_j` on `[0,1]` for all `i, j ∈ Σ`. -/
theorem audit_conj_iff {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i)) (hd : NonzeroDerivatives f)
    (hnd : ¬ ∃ x, attractor f = {x}) :
    ConjSelfSimilar (fun i (x : ℝ) => (f i x).re) ↔
      ∀ i j : ℕ → Fin N, ∀ x : I, dualProjInf f hd i x = dualProjInf f hd j x := by
  constructor
  · intro h i j x
    exact (((toIFS hε f hf).theorem_1_12 hnd).1.mp h) i j x x.2
  · intro h
    apply ((toIFS hε f hf).theorem_1_12 hnd).1.mpr
    intro i j x hx
    exact h i j ⟨x, hx⟩

/-- Theorem 1.12 (b). If the attractor of `Φ` is not a singleton, then `Φ` is sub-conjugated to a
self-similar IFS, that is, `(f_i, f_j)` is conjugated to a self-similar IFS for some distinct
`i, j ∈ Σ_*` of the same length, if and only if `H_{(i)^∞} ≡ H_{(j)^∞}` on `[0,1]` for some distinct
`i, j ∈ Σ_*` of the same length. -/
theorem audit_subconj_iff {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i)) (hd : NonzeroDerivatives f)
    (hnd : ¬ ∃ x, attractor f = {x}) :
    (∃ (m : ℕ) (i j : Fin m → Fin N), i ≠ j ∧
      ConjSelfSimilar ![fun x : ℝ => (comp f (List.ofFn i) x).re,
        fun x : ℝ => (comp f (List.ofFn j) x).re]) ↔
      ∃ (m : ℕ) (hm : 0 < m) (i j : Fin m → Fin N), i ≠ j ∧
        ∀ x : I, dualProjInf f hd (periodic hm i) x = dualProjInf f hd (periodic hm j) x := by
  constructor
  · intro h
    obtain ⟨m, hm, i, j, hij, heq⟩ := ((toIFS hε f hf).theorem_1_12 hnd).2.mp h
    exact ⟨m, hm, i, j, hij, fun x => heq x x.2⟩
  · rintro ⟨m, hm, i, j, hij, heq⟩
    apply ((toIFS hε f hf).theorem_1_12 hnd).2.mpr
    exact ⟨m, hm, i, j, hij, fun x hx => heq ⟨x, hx⟩⟩

section DimensionProofs

open MeasureTheory Filter Topology

theorem pressureRatio_tendsto_iff (f : Fin N → ℂ → ℂ) (t : ℝ) :
    Tendsto (pressureRatio f t) atTop (𝓝 0) ↔
      Tendsto (fun n : ℕ => Real.log (pressureSum f t n) / n) atTop (𝓝 0) :=
  AnalyticESC.positive_length_tendsto_iff (fun n => Real.log (pressureSum f t n))

theorem logRatio_tendsto_iff (mass : ℝ → ℝ) (s : ℝ) :
    Tendsto (fun r : Scale => logRatio (mass r) r) scaleZero (𝓝 s) ↔
      Tendsto (fun r : ℝ => Real.log (mass r) / Real.log r) (𝓝[>] 0) (𝓝 s) :=
  AnalyticESC.scale_tendsto_iff (fun r => Real.log (mass r) / Real.log r) (𝓝 s)

theorem lqDim_eq_lib (μ : Measure ℝ) (q : ℝ) (hq : q - 1 ≠ 0) :
    lqDim μ q hq = AnalyticESC.lqDim μ q :=
  congrArg (fun t : ℝ => t / (q - 1))
    (AnalyticESC.scale_liminf (AnalyticESC.lqRatio μ q))

theorem dimEquality_of_lib {ε : ℝ} (Φ : AnalyticESC.IFS N ε)
    (h : Φ.DimEquality) : DimEquality Φ.f := by
  obtain ⟨⟨s, hs, hset⟩, hm⟩ := h
  refine ⟨⟨s, fun t => (pressureRatio_tendsto_iff Φ.f t).trans (hs t), hset⟩, ?_⟩
  intro p hp μ hμ hχ
  filter_upwards [hm p hp μ hμ] with x hx
  exact (logRatio_tendsto_iff _ _).mpr hx

theorem dimEquality_iff_lib {ε : ℝ} (Φ : AnalyticESC.IFS N ε) (hN : 0 < N) :
    DimEquality Φ.f ↔ Φ.DimEquality := by
  refine ⟨?_, dimEquality_of_lib Φ⟩
  rintro ⟨⟨s, hs, hset⟩, hm⟩
  refine ⟨⟨s, fun t => (pressureRatio_tendsto_iff Φ.f t).symm.trans (hs t), hset⟩, ?_⟩
  intro p hp μ hμ
  have hχ : lyapunov Φ.f p μ ≠ 0 := (Φ.lyapunov_pos hN hp hμ).ne'
  filter_upwards [hm p hp μ hμ hχ] with x hx
  exact (logRatio_tendsto_iff _ _).mp hx

/-- `BowenGibbsStatement` in the form used by the library. -/
theorem bowenGibbs_lib (hB : BowenGibbsStatement) : AnalyticESC.BowenGibbsStatement := by
  intro N hN φ b α hb hα₀ hα₁ hφ
  exact hB hN φ hb hα₀ hα₁ hφ

/-- `RapaportMeasureStatement` in the form used by the library. -/
theorem rapaportMeasure_lib (hM : RapaportMeasureStatement) :
    AnalyticESC.RapaportMeasureStatement := by
  intro N φ hφ p hp hp1 μ hμ hμI hμφ
  exact hM φ ⟨hφ.1, hφ.2, hφ.3, hφ.4, hφ.5, hφ.6⟩ p hp hp1 μ hμ hμI hμφ

/-- `RapaportSetStatement` in the form used by the library. -/
theorem rapaportSet_lib (hS : RapaportSetStatement) : AnalyticESC.RapaportSetStatement := by
  intro N φ hφ K hK hKc hKI hKφ s hs
  exact hS φ ⟨hφ.1, hφ.2, hφ.3, hφ.4, hφ.5, hφ.6⟩ K hK hKc hKI hKφ s hs

/-- Theorem 1.6 (Rapaport), from Rapaport's Theorem 1.2 and Corollary 1.3. Let
`Φ = (f_i)_{i ∈ Fin N}`, `N ≥ 1`, be an analytic IFS in `𝔖_N` whose attractor is not a singleton.
If `Φ` satisfies the ESC, then there is equality in (1.6). -/
theorem audit_dim_of_esc (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) {ε : ℝ}
    (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i))
    (hN : 0 < N) (hnd : ¬ ∃ x, attractor f = {x}) (hesc : ESC f) : DimEquality f := by
  exact dimEquality_of_lib (toIFS hε f hf)
    ((toIFS hε f hf).theorem_1_6 (rapaportMeasure_lib hM) (rapaportSet_lib hS) hN hnd hesc)

/-- Corollary 1.7, from Rapaport's Theorem 1.2 and Corollary 1.3. For `N ≥ 2`, the IFSs in `𝔖_N`
with equality in (1.6) contain a subset `U` of `𝔖_N` that is open and dense in `𝔖_N` for the `𝒞²`
metric `d₂`. Corollary 1.7 is stated for every `N`; its `N = 1` case is omitted here. -/
theorem audit_dim_open_dense (hM : RapaportMeasureStatement) (hS : RapaportSetStatement)
    (hN : 2 ≤ N) :
    ∃ U : Set (Fin N → ℂ → ℂ), (∀ f ∈ U, InUnionClass f ∧ DimEquality f) ∧
      (∀ f ∈ U, ∃ r > 0, ∀ g, InUnionClass g → d2 f g < r → g ∈ U) ∧
      (∀ f, InUnionClass f → ∀ r > 0, ∃ g ∈ U, d2 f g < r) := by
  have hlib : ∀ f : Fin N → ℂ → ℂ, InUnionClass f → AnalyticESC.InUnionClass f :=
    fun f ⟨ε, hε, hf⟩ => ⟨ε, hε, fun i => inClass_iff_lib.mp (hf i)⟩
  obtain ⟨U, hE, hO, hD⟩ :=
    AnalyticESC.corollary_1_7 (rapaportMeasure_lib hM) (rapaportSet_lib hS) hN
  refine ⟨U, fun f hf => ?_, fun f hf => ?_, fun f hf r hr => hD f (hlib f hf) r hr⟩
  · obtain ⟨ε, ⟨g, hε, hg⟩, rfl, hDE⟩ := hE f hf
    exact ⟨⟨ε, hε, fun i => inClass_iff_lib.mpr (hg i)⟩,
      dimEquality_of_lib ⟨g, hε, hg⟩ hDE⟩
  · obtain ⟨r, hr, h⟩ := hO f hf
    exact ⟨r, hr, fun g hg hd => h g (hlib g hg) hd⟩

/-- The polynomial example of Section 1.2.2, from Rapaport's Theorem 1.2 and Corollary 1.3:
`dim_H Λ = s(Φ) < 1`, where `s(Φ)` is the unique zero of the pressure, and `dim μ_p = H(p)/χ < 1` at
`μ_p`-almost every point, for every positive probability vector `p`, by Theorem 1.6. -/
theorem audit_example_dim (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (pressureRatio exampleMaps t) atTop (𝓝 0) ↔
        t = s) ∧
      s < 1 ∧ dimH (attractor exampleMaps) = ENNReal.ofReal s ∧
      ∀ p : Fin 3 → ℝ, IsProbVec p → ∀ μ : Measure ℝ, IsSelfConformal exampleMaps p μ →
        ∀ hχ : lyapunov exampleMaps p μ ≠ 0,
        entropy p < lyapunov exampleMaps p μ ∧
        ∀ᵐ x ∂μ, Tendsto (fun r : Scale => logRatio (μ.real (closedBall x r)) r) scaleZero
          (𝓝 (divide (entropy p) (lyapunov exampleMaps p μ) hχ)) := by
  obtain ⟨s, hs, hs1, hset, hm⟩ :=
    AnalyticESC.example_dim (rapaportMeasure_lib hM) (rapaportSet_lib hS)
  refine ⟨s, fun t => (pressureRatio_tendsto_iff exampleMaps t).trans (hs t), hs1, hset, ?_⟩
  intro p hp μ hμ hχ
  obtain ⟨hent, hlocal⟩ := hm p hp μ hμ
  refine ⟨hent, ?_⟩
  filter_upwards [hlocal] with x hx
  exact (logRatio_tendsto_iff _ _).mpr hx

/-- The natural measure of the polynomial example in Section 1.2.2, from Bowen's theorem:
the pressure has a unique zero `s = s(Φ)`, the potential `s log|f'_{ω₀}(π(σω))|` has a Gibbs measure,
and for every such Gibbs measure `ν` the natural measure `μ = ν ∘ π⁻¹` has local dimension `s(Φ) - 1/3 < s(Φ)`
at `0`. -/
theorem audit_example_localDim (hB : BowenGibbsStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (pressureRatio exampleMaps t) atTop (𝓝 0) ↔
        t = s) ∧
      (∃ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν ∧
        IsGibbsMeasure (potential exampleMaps s) ν) ∧
      ∀ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν →
        IsGibbsMeasure (potential exampleMaps s) ν →
        Tendsto (fun r : Scale => logRatio ((ν.map (natProj exampleMaps)).real (closedBall 0 r)) r)
          scaleZero (𝓝 (s - 1 / 3)) := by
  obtain ⟨s, hs, hG, hm⟩ := AnalyticESC.example_localDim_of_bowen (bowenGibbs_lib hB)
  refine ⟨s, fun t => (pressureRatio_tendsto_iff exampleMaps t).trans (hs t), hG, ?_⟩
  intro ν hν hGν
  exact (logRatio_tendsto_iff _ _).mpr (hm ν hν hGν)

/-- `L^q` dimensions of the polynomial example in Section 1.2.2, from Bowen's theorem:
for every Gibbs measure `ν` of the potential `s(Φ) log|f'_{ω₀}(π(σω))|` and every `q > 1`,
the natural measure `μ = ν ∘ π⁻¹` has `D_μ(q) ≤ q (s(Φ) - 1/3) / (q - 1)`, which is smaller than `s(Φ)` for `q > 3 s(Φ)`. -/
theorem audit_example_lq (hB : BowenGibbsStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (pressureRatio exampleMaps t) atTop (𝓝 0) ↔
        t = s) ∧
      ∀ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν →
        IsGibbsMeasure (potential exampleMaps s) ν → ∀ q > 1, ∀ hq : q - 1 ≠ 0,
        lqDim (ν.map (natProj exampleMaps)) q hq ≤ divide q (q - 1) hq * (s - 1 / 3) ∧
        (3 * s < q → lqDim (ν.map (natProj exampleMaps)) q hq < s) := by
  obtain ⟨s, hs, hq⟩ := AnalyticESC.example_lq_of_bowen (bowenGibbs_lib hB)
  refine ⟨s, fun t => (pressureRatio_tendsto_iff exampleMaps t).trans (hs t), ?_⟩
  intro ν hν hG q hq1 hq0
  simp only [lqDim_eq_lib, divide]
  exact (hq ν hν hG q hq1).2.2.2

end DimensionProofs

end Challenge
