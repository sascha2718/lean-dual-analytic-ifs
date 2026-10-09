module

public import Mathlib

@[expose] public section

/-!
# Exponential separation of analytic self-conformal sets on the real line

Headline statements from B. Bárány, I. Kolossváry and S. Troscheit, *On exponential separation
of analytic self-conformal sets on the real line*, arXiv:2509.07888v2 (26 March 2026). Theorem,
section and equation numbers refer to this version; differences from the printed statements are
noted in the docstrings and in `README.md`.

A map of the IFS is given by its holomorphic extension `f : ℂ → ℂ`; on `[0,1]` it is real, and its
complex derivatives at real points are the derivatives of its real restriction. Finite words are
lists, read from the left: `f_{i₁ ⋯ iₙ} = f_{i₁} ∘ ⋯ ∘ f_{iₙ}`.

Three results that the paper cites are stated as in their sources and are explicit hypotheses
of the theorems that use them: `BowenGibbsStatement` (Bowen's theorem on Gibbs measures),
`RapaportMeasureStatement` (Rapaport's Theorem 1.2, with the exact dimensionality of Feng and Hu)
and `RapaportSetStatement` (Rapaport's Corollary 1.3). Rapaport's results are stated for real
analytic maps of `[0,1]`, as in his paper.
-/

namespace Challenge

open Set Metric

/-- The unit interval `I = [0,1]`. -/
abbrev I : Set ℝ := Icc 0 1

/-- The open `δ`-neighbourhood `B_δ = {z ∈ ℂ : ∃ x ∈ I, |z - x| < δ}` of `I` in `ℂ`. -/
def nbhd (δ : ℝ) : Set ℂ := thickening δ (((↑) : ℝ → ℂ) '' I)

/-- The class `S^ω_ε(I)` of Section 1.1, for a map given by its holomorphic extension:
(A) `f` is complex analytic on `B_{2ε}` and real at the real points of `B_{2ε}`;
(B) `f(I) ⊆ I` and `f(cl B_ε) ⊆ B_ε`; (C) `0 < |f'(z)| < 1` for `z ∈ cl B_ε`. -/
structure InClass (ε : ℝ) (f : ℂ → ℂ) : Prop where
  differentiableOn : DifferentiableOn ℂ f (nbhd (2 * ε))
  im_eq_zero : ∀ x : ℝ, (x : ℂ) ∈ nbhd (2 * ε) → (f x).im = 0
  re_mem_I : ∀ x ∈ I, (f x).re ∈ I
  mapsTo : MapsTo f (closure (nbhd ε)) (nbhd ε)
  deriv_ne_zero : ∀ z ∈ closure (nbhd ε), deriv f z ≠ 0
  norm_deriv_lt_one : ∀ z ∈ closure (nbhd ε), ‖deriv f z‖ < 1

variable {N : ℕ}

/-- `f_w = f_{w₁} ∘ ⋯ ∘ f_{w_k}` for a finite word `w`, with `f_∅ = id`. -/
def comp (f : Fin N → ℂ → ℂ) (w : List (Fin N)) : ℂ → ℂ := w.foldr (fun i g => f i ∘ g) id

/-- `sup_{x ∈ [0,1]} |f_i(x) - f_j(x)|` for finite words `i` and `j`. -/
noncomputable def supDist (f : Fin N → ℂ → ℂ) (i j : List (Fin N)) : ℝ :=
  ⨆ x : I, ‖comp f i ((x : ℝ) : ℂ) - comp f j ((x : ℝ) : ℂ)‖

/-- The strong exponential separation condition (Definition 1.2): there is `c > 0` with
`sup_{x ∈ [0,1]} |f_i(x) - f_j(x)| ≥ c^n` for all distinct `i, j ∈ Σ_n` and all `n`. -/
def SESC (f : Fin N → ℂ → ℂ) : Prop :=
  ∃ c > 0, ∀ n, ∀ i j : Fin n → Fin N, i ≠ j → c ^ n ≤ supDist f (List.ofFn i) (List.ofFn j)

/-- The distortion `f''/f'`. -/
noncomputable def nonlin (g : ℂ → ℂ) (z : ℂ) : ℂ := deriv (deriv g) z / deriv g z

/-- The dual natural projection `H_w` of (1.4) for a finite word `w`. The term with index `n`
(from `0`) is `(f_i''/f_i')(f_{v^←}(z)) · f_{v^←}'(z)`, where `v` is the prefix of the first `n`
letters, `i` the next letter and `f_{v^←} = f_{v_n} ∘ ⋯ ∘ f_{v_1}`. -/
noncomputable def dualProjFin (f : Fin N → ℂ → ℂ) (w : List (Fin N)) (z : ℂ) : ℂ :=
  ∑' n, match w[n]? with
    | none => 0
    | some i => nonlin (f i) (comp f (w.take n).reverse z) * deriv (comp f (w.take n).reverse) z

/-- The dual natural projection `H_w` of (1.4) for an infinite word `w`. -/
noncomputable def dualProjInf (f : Fin N → ℂ → ℂ) (w : ℕ → Fin N) (z : ℂ) : ℂ :=
  ∑' n, nonlin (f (w n)) (comp f (List.ofFn fun k : Fin n => w k).reverse z) *
    deriv (comp f (List.ofFn fun k : Fin n => w k).reverse) z

/-- The constant `c_max` of (1.7): the supremum of `|f_i'|` over `cl B_ε` and `i`. -/
noncomputable def cmax (ε : ℝ) (f : Fin N → ℂ → ℂ) : ℝ :=
  ⨆ (i : Fin N) (z : closure (nbhd ε)), ‖deriv (f i) z‖

/-- `β = sup_{x ∈ [0,1], i} |f_i''/f_i'(x)|` (Proposition 1.8). -/
noncomputable def beta (f : Fin N → ℂ → ℂ) : ℝ := ⨆ (x : I) (i : Fin N), ‖nonlin (f i) ((x : ℝ) : ℂ)‖

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

/-- The `𝒞²` distance `d₂(f, g)` on `[0,1]` of Section 1.1, with derivatives at real points. -/
noncomputable def d2Map (f g : ℂ → ℂ) : ℝ :=
  (⨆ x : I, ‖f ((x : ℝ) : ℂ) - g ((x : ℝ) : ℂ)‖) +
    (⨆ x : I, ‖deriv f ((x : ℝ) : ℂ) - deriv g ((x : ℝ) : ℂ)‖) +
    (⨆ x : I, ‖deriv (deriv f) ((x : ℝ) : ℂ) - deriv (deriv g) ((x : ℝ) : ℂ)‖)

/-- The `𝒞²` distance `d₂(Φ, Ψ) = max_i d₂(f_i, g_i)` between two IFSs (Section 1.1). -/
noncomputable def d2 (f g : Fin N → ℂ → ℂ) : ℝ := ⨆ i, d2Map (f i) (g i)

/-- The space `𝔖_N` of Section 1.1: IFSs whose maps lie in `S^ω_ε(I)` for some `ε > 0`, which may
depend on the system. Section 1.1 of arXiv v2 fixes `ε` throughout. -/
def InUnionClass (f : Fin N → ℂ → ℂ) : Prop := ∃ ε > 0, ∀ i, InClass ε (f i)

section Dimension

open MeasureTheory Filter Topology

/-! ### Dimension theory (Sections 1.2.1 and 1.2.2) -/

/-- The exponential separation condition (ESC): there is `c > 0` with
`sup_{x ∈ [0,1]} |f_i(x) - f_j(x)| ≥ c^n` for all distinct `i, j ∈ Σ_n`, for infinitely many
`n`. -/
def ESC (f : Fin N → ℂ → ℂ) : Prop :=
  ∃ c > 0, ∃ᶠ n in atTop, ∀ i j : Fin n → Fin N, i ≠ j →
    c ^ n ≤ supDist f (List.ofFn i) (List.ofFn j)

/-- `‖f_w'‖ = sup_{x ∈ [0,1]} |f_w'(x)|`. -/
noncomputable def supDeriv (f : Fin N → ℂ → ℂ) (w : List (Fin N)) : ℝ :=
  ⨆ x : I, ‖deriv (comp f w) ((x : ℝ) : ℂ)‖

/-- The sum `∑_{w ∈ Σ_n} ‖f_w'‖^t`. The pressure of Section 1.2.1 is
`P(t) = lim_n (1/n) log ∑_{w ∈ Σ_n} ‖f_w'‖^t`, and the conformality dimension `s(Φ)` is its zero. -/
noncomputable def pressureSum (f : Fin N → ℂ → ℂ) (t : ℝ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → Fin N, supDeriv f (List.ofFn w) ^ t

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
  (∃ s : ℝ, (∀ t, Tendsto (fun n : ℕ => Real.log (pressureSum f t n) / n) atTop (𝓝 0) ↔ t = s) ∧
      dimH (attractor f) = ENNReal.ofReal (min 1 s)) ∧
    ∀ p : Fin N → ℝ, IsProbVec p → ∀ μ : Measure ℝ, IsSelfConformal f p μ →
      ∀ᵐ x ∂μ, Tendsto (fun δ => Real.log (μ.real (closedBall x δ)) / Real.log δ) (𝓝[>] 0)
        (𝓝 (min 1 (entropy p / lyapunov f p μ)))

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

/-- The `L^q` sum `∑_{k ∈ ℤ} μ([kr, (k+1)r))^q` of `μ` at scale `r`. -/
noncomputable def lqSum (μ : Measure ℝ) (q r : ℝ) : ℝ :=
  ∑' k : ℤ, μ.real (Ico (k * r) ((k + 1) * r)) ^ q

/-- The quotient `log(∑_{k ∈ ℤ} μ([kr, (k+1)r))^q) / log r`, whose limit inferior as `r → 0` is the
`L^q` spectrum. -/
noncomputable def lqRatio (μ : Measure ℝ) (q r : ℝ) : ℝ := Real.log (lqSum μ q r) / Real.log r

/-- The `L^q` dimension `D_μ(q) = τ_μ(q)/(q - 1)` of Section 1.2.2, where
`τ_μ(q) = liminf_{r → 0} log(∑_{k ∈ ℤ} μ([kr, (k+1)r))^q) / log r` is the `L^q` spectrum. -/
noncomputable def lqDim (μ : Measure ℝ) (q : ℝ) : ℝ := liminf (lqRatio μ q) (𝓝[>] 0) / (q - 1)

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
      ∀ᵐ x ∂μ, Tendsto (fun δ => Real.log (μ.real (closedBall x δ)) / Real.log δ) (𝓝[>] 0)
        (𝓝 (min 1 ((-∑ i, p i * Real.log (p i)) /
          (-∑ i, p i * ∫ y, Real.log |deriv (φ i) y| ∂μ))))

/-- **Cited result.** A. Rapaport, *Dimension of self-conformal measures associated to an
exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2, Corollary 1.3: under `RapaportHyp`,
the attractor `K`, the nonempty compact set `K ⊆ I` with `K = ⋃_i φ_i(K)`, has Hausdorff dimension
`min{1, s(Φ)}`, where `s(Φ)` is the zero of the pressure
`P(t) = lim_n (1/n) log ∑_{u ∈ Σ_n} (sup_{x ∈ I} |φ_u'(x)|)^t`. -/
def RapaportSetStatement : Prop :=
  ∀ {N : ℕ} (φ : Fin N → ℝ → ℝ), RapaportHyp φ →
    ∀ K : Set ℝ, K.Nonempty → IsCompact K → K ⊆ I → K = ⋃ i, φ i '' K →
    ∀ s : ℝ, Tendsto (fun n : ℕ => Real.log (∑ u : Fin n → Fin N,
        (⨆ x : I, |deriv (realComp φ (List.ofFn u)) x|) ^ s) / n) atTop (𝓝 0) →
      dimH K = ENNReal.ofReal (min 1 s)

end Dimension

/-- Theorem 1.4. The IFSs in `𝔖_N` that satisfy the strong exponential separation condition
contain a subset `U` of `𝔖_N` that is open and dense in `𝔖_N` for the `𝒞²` metric `d₂`. -/
theorem audit_sesc_open_dense (N : ℕ) :
    ∃ U : Set (Fin N → ℂ → ℂ), (∀ f ∈ U, InUnionClass f ∧ SESC f) ∧
      (∀ f ∈ U, ∃ r > 0, ∀ g, InUnionClass g → d2 f g < r → g ∈ U) ∧
      (∀ f, InUnionClass f → ∀ r > 0, ∃ g ∈ U, d2 f g < r) := by
  sorry

/-- Theorem 1.5. Let `Φ = (f_i)_{i ∈ Fin N}` be an analytic IFS in `𝔖_N`. If
`sup_{x ∈ [0,1]} |H_i(x) - H_j(x)| > 0` for all distinct `i, j ∈ Σ ∪ Σ_*` with `|i| = |j|`, then `Φ`
satisfies the strong exponential separation condition. Words of equal length are either both
finite of the same length or both infinite. -/
theorem audit_sesc_of_dualProj {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ)
    (hf : ∀ i, InClass ε (f i))
    (hfin : ∀ n, ∀ i j : Fin n → Fin N, i ≠ j →
      0 < ⨆ x : I, ‖dualProjFin f (List.ofFn i) ((x : ℝ) : ℂ) -
        dualProjFin f (List.ofFn j) ((x : ℝ) : ℂ)‖)
    (hinf : ∀ i j : ℕ → Fin N, i ≠ j →
      0 < ⨆ x : I, ‖dualProjInf f i ((x : ℝ) : ℂ) - dualProjInf f j ((x : ℝ) : ℂ)‖) :
    SESC f := by
  sorry

/-- Proposition 1.8. Let `Φ = (f_i)_{i ∈ Fin N}` be an analytic IFS in `𝔖_N` with `N ≥ 2` maps.
Suppose that there is `α > 0` such that for all `i ≠ j` there is `x ∈ [0,1]` with
`|f_i''/f_i'(x) - f_j''/f_j'(x)| ≥ α`. Then `β > 0`, and if `α > 2β c_max/(1 - c_max)`, then
`sup_{x ∈ [0,1]} |H_i(x) - H_j(x)| > 0` for all distinct `i, j ∈ Σ ∪ Σ_*` with `|i| = |j|`, and `Φ`
satisfies the strong exponential separation condition. The hypothesis `N ≥ 2` is not in the
printed statement, whose conclusion `β > 0` can fail for `N = 1`. -/
theorem audit_example_criterion {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ)
    (hf : ∀ i, InClass ε (f i)) (hN : 2 ≤ N) {α : ℝ} (hα : 0 < α)
    (hsep : ∀ i j : Fin N, i ≠ j → ∃ x ∈ I, α ≤ ‖nonlin (f i) x - nonlin (f j) x‖) :
    0 < beta f ∧ (2 * beta f * cmax ε f / (1 - cmax ε f) < α →
      (∀ n, ∀ i j : Fin n → Fin N, i ≠ j →
        0 < ⨆ x : I, ‖dualProjFin f (List.ofFn i) ((x : ℝ) : ℂ) -
          dualProjFin f (List.ofFn j) ((x : ℝ) : ℂ)‖) ∧
      (∀ i j : ℕ → Fin N, i ≠ j →
        0 < ⨆ x : I, ‖dualProjInf f i ((x : ℝ) : ℂ) - dualProjInf f j ((x : ℝ) : ℂ)‖) ∧
      SESC f) := by
  sorry

/-- The example of Section 1.2.2: the system `x/8`, `x/8 + x²/32`, `x/16 + x²/32 + 29/32` lies in
`𝔖_3` for some `ε > 0` and satisfies the strong exponential separation condition. -/
theorem audit_example_sesc : ∃ ε > 0, (∀ i, InClass ε (exampleMaps i)) ∧ SESC exampleMaps := by
  sorry

/-- Individual-map linearisation for Theorem 1.12: an analytic coordinate with nonvanishing
derivative conjugates the chosen map `f_i` to a contracting similarity. This is narrower than
the first claim in arXiv v2: contraction of the other conjugated maps is not asserted. -/
theorem audit_conj_similarity {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ)
    (hf : ∀ i, InClass ε (f i)) (i : Fin N) :
    ∃ g, IsAnalyticCoord g ∧ (∀ x ∈ I, deriv g x ≠ 0) ∧
      ∃ lam t : ℝ, lam ≠ 0 ∧ |lam| < 1 ∧ ∀ x ∈ I, g (f i x).re = lam * g x + t := by
  sorry

/-- Theorem 1.12 (a). If the attractor of `Φ` is not a singleton, then `Φ` is conjugated to a
self-similar IFS if and only if `H_i ≡ H_j` on `[0,1]` for all `i, j ∈ Σ`. -/
theorem audit_conj_iff {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i))
    (hnd : ¬ ∃ x, attractor f = {x}) :
    ConjSelfSimilar (fun i (x : ℝ) => (f i x).re) ↔
      ∀ i j : ℕ → Fin N, ∀ x ∈ I, dualProjInf f i x = dualProjInf f j x := by
  sorry

/-- Theorem 1.12 (b). If the attractor of `Φ` is not a singleton, then `Φ` is sub-conjugated to a
self-similar IFS, that is, `(f_i, f_j)` is conjugated to a self-similar IFS for some distinct
`i, j ∈ Σ_*` of the same length, if and only if `H_{(i)^∞} ≡ H_{(j)^∞}` on `[0,1]` for some distinct
`i, j ∈ Σ_*` of the same length. -/
theorem audit_subconj_iff {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i))
    (hnd : ¬ ∃ x, attractor f = {x}) :
    (∃ (m : ℕ) (i j : Fin m → Fin N), i ≠ j ∧
      ConjSelfSimilar ![fun x : ℝ => (comp f (List.ofFn i) x).re,
        fun x : ℝ => (comp f (List.ofFn j) x).re]) ↔
      ∃ (m : ℕ) (hm : 0 < m) (i j : Fin m → Fin N), i ≠ j ∧
        ∀ x ∈ I, dualProjInf f (periodic hm i) x = dualProjInf f (periodic hm j) x := by
  sorry

section DimensionEndpoints

open MeasureTheory Filter Topology

/-- Theorem 1.6 (Rapaport), from Rapaport's Theorem 1.2 and Corollary 1.3. Let
`Φ = (f_i)_{i ∈ Fin N}`, `N ≥ 1`, be an analytic IFS in `𝔖_N` whose attractor is not a singleton.
If `Φ` satisfies the ESC, then there is equality in (1.6). -/
theorem audit_dim_of_esc (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) {ε : ℝ}
    (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i)) (hN : 0 < N) (hnd : ¬ ∃ x, attractor f = {x}) (hesc : ESC f) : DimEquality f := by
  sorry

/-- Corollary 1.7, from Rapaport's Theorem 1.2 and Corollary 1.3. For `N ≥ 2`, the IFSs in `𝔖_N`
with equality in (1.6) contain a subset `U` of `𝔖_N` that is open and dense in `𝔖_N` for the `𝒞²`
metric `d₂`. The printed corollary is for every `N`; its `N = 1` case is omitted. -/
theorem audit_dim_open_dense (hM : RapaportMeasureStatement) (hS : RapaportSetStatement)
    (hN : 2 ≤ N) :
    ∃ U : Set (Fin N → ℂ → ℂ), (∀ f ∈ U, InUnionClass f ∧ DimEquality f) ∧
      (∀ f ∈ U, ∃ r > 0, ∀ g, InUnionClass g → d2 f g < r → g ∈ U) ∧
      (∀ f, InUnionClass f → ∀ r > 0, ∃ g ∈ U, d2 f g < r) := by
  sorry

/-- The example of Section 1.2.2, from Rapaport's Theorem 1.2 and Corollary 1.3:
`dim_H Λ = s(Φ) < 1`, where `s(Φ)` is the unique zero of the pressure, and `dim μ_p = H(p)/χ < 1` at
`μ_p`-almost every point, for every positive probability vector `p`, by Theorem 1.6; the printed
text cites Corollary 1.7. -/
theorem audit_example_dim (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (fun n : ℕ => Real.log (pressureSum exampleMaps t n) / n) atTop (𝓝 0) ↔
        t = s) ∧
      s < 1 ∧ dimH (attractor exampleMaps) = ENNReal.ofReal s ∧
      ∀ p : Fin 3 → ℝ, IsProbVec p → ∀ μ : Measure ℝ, IsSelfConformal exampleMaps p μ →
        entropy p < lyapunov exampleMaps p μ ∧
        ∀ᵐ x ∂μ, Tendsto (fun δ => Real.log (μ.real (closedBall x δ)) / Real.log δ) (𝓝[>] 0)
          (𝓝 (entropy p / lyapunov exampleMaps p μ)) := by
  sorry

/-- The remark at the end of Section 1.2.2, from Bowen's theorem: the pressure of the example has a
unique zero `s = s(Φ)`, the potential `s log|f'_{ω₀}(π(σω))|` has a Gibbs measure, and for every
such Gibbs measure `ν` the natural measure `μ = ν ∘ π⁻¹` has local dimension `s(Φ) - 1/3 < s(Φ)`
at `0`. -/
theorem audit_example_localDim (hB : BowenGibbsStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (fun n : ℕ => Real.log (pressureSum exampleMaps t n) / n) atTop (𝓝 0) ↔
        t = s) ∧
      (∃ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν ∧
        IsGibbsMeasure (potential exampleMaps s) ν) ∧
      ∀ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν →
        IsGibbsMeasure (potential exampleMaps s) ν →
        Tendsto (fun r => Real.log ((ν.map (natProj exampleMaps)).real (closedBall 0 r)) /
          Real.log r) (𝓝[>] 0) (𝓝 (s - 1 / 3)) := by
  sorry

/-- The end of Section 1.2.2, from Bowen's theorem: for every Gibbs measure `ν` of the potential
`s(Φ) log|f'_{ω₀}(π(σω))|` and every `q > 1`, the natural measure `μ = ν ∘ π⁻¹` has
`D_μ(q) ≤ q (s(Φ) - 1/3) / (q - 1)`, which is smaller than `s(Φ)` for `q > 3 s(Φ)`. -/
theorem audit_example_lq (hB : BowenGibbsStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (fun n : ℕ => Real.log (pressureSum exampleMaps t n) / n) atTop (𝓝 0) ↔
        t = s) ∧
      ∀ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν →
        IsGibbsMeasure (potential exampleMaps s) ν → ∀ q > 1,
        lqDim (ν.map (natProj exampleMaps)) q ≤ q / (q - 1) * (s - 1 / 3) ∧
        (3 * s < q → lqDim (ν.map (natProj exampleMaps)) q < s) := by
  sorry

end DimensionEndpoints

end Challenge
