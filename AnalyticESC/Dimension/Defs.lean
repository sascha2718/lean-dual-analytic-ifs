module

public import AnalyticESC.Main.LocalDimension

@[expose] public section

/-!
# Dimension theory: vocabulary and cited results

The vocabulary of Section 1.2.1 and of the natural measure of the polynomial example
in Section 1.2.2: entropy, Lyapunov exponent, self-conformal measures, the equality in (1.6),
the potential `s log|f'_{ω₀}(π(σω))|` and its Gibbs measures.

The three results cited from the literature are recorded as propositions, which the theorems of
the library take as hypotheses. `Challenge.lean` states them identically, as hypotheses of the
audited theorems that use them.

* `BowenGibbsStatement`: R. Bowen, *Equilibrium states and the ergodic theory of Anosov
  diffeomorphisms*, Lecture Notes in Mathematics 470, Springer, 1975, Theorem 1.4, for the
  one-sided full shift.
* `RapaportMeasureStatement`: A. Rapaport, *Dimension of self-conformal measures associated to an
  exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2, Theorem 1.2, with the exact
  dimensionality of self-conformal measures of D.-J. Feng and H. Hu, *Dimension theory of iterated
  function systems*, Comm. Pure Appl. Math. 62 (2009).
* `RapaportSetStatement`: the same paper of Rapaport, Corollary 1.3.

Rapaport's statements are for real maps of `I = [0,1]`; `realComp` is the composition of real
maps and `RapaportHyp` collects his hypotheses.
-/

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory

/-! ### Rapaport's setting: real analytic IFSs on `I` -/

/-- `φ_u = φ_{u₁} ∘ ⋯ ∘ φ_{uₙ}` for real maps and a finite word `u`, with `φ_∅ = id`. -/
def realComp {N : ℕ} (φ : Fin N → ℝ → ℝ) (u : List (Fin N)) : ℝ → ℝ :=
  u.foldr (fun i g => φ i ∘ g) id

/-- The hypotheses of Rapaport's Theorem 1.2 and Corollary 1.3: `φ_i(I) ⊆ I`, each `φ_i` is real
analytic on a neighbourhood of each point of `I`, `0 < |φ_i'(x)| < 1` for `x ∈ I`, the maps have no
common fixed point in `I`, and the system is exponentially separated: there is `c > 0` such that
for infinitely many `n`, `sup_{x ∈ I} |φ_u(x) - φ_v(x)| ≥ c^n` for all distinct `u, v` of length
`n`. -/
structure RapaportHyp {N : ℕ} (φ : Fin N → ℝ → ℝ) : Prop where
  mapsTo : ∀ i, MapsTo (φ i) I I
  analytic : ∀ i, AnalyticOnNhd ℝ (φ i) I
  deriv_pos : ∀ i, ∀ x ∈ I, 0 < |deriv (φ i) x|
  deriv_lt_one : ∀ i, ∀ x ∈ I, |deriv (φ i) x| < 1
  no_common_fixed_point : ¬ ∃ x ∈ I, ∀ i, φ i x = x
  exp_separated : ∃ c > 0, ∃ᶠ n in atTop, ∀ u v : Fin n → Fin N, u ≠ v →
    c ^ n ≤ ⨆ x : I, |realComp φ (List.ofFn u) x - realComp φ (List.ofFn v) x|

/-- Rapaport's Theorem 1.2, with the exact dimensionality of Feng and Hu: for a positive
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

/-- Rapaport's Corollary 1.3: the attractor `K`, the nonempty compact set `K ⊆ I` with
`K = ⋃_i φ_i(K)`, has Hausdorff dimension `min{1, s(Φ)}`, where `s(Φ)` is the zero of the pressure
`P(t) = lim_n (1/n) log ∑_{u ∈ Σ_n} (sup_{x ∈ I} |φ_u'(x)|)^t`. -/
def RapaportSetStatement : Prop :=
  ∀ {N : ℕ} (φ : Fin N → ℝ → ℝ), RapaportHyp φ →
    ∀ K : Set ℝ, K.Nonempty → IsCompact K → K ⊆ I → K = ⋃ i, φ i '' K →
    ∀ s : ℝ, Tendsto (fun n : ℕ => Real.log (∑ u : Fin n → Fin N,
        (⨆ x : I, |deriv (realComp φ (List.ofFn u)) x|) ^ s) / n) atTop (𝓝 0) →
      dimH K = ENNReal.ofReal (min 1 s)

/-! ### Gibbs measures -/

/-- `ν` is a Gibbs measure for the potential `φ` on `Σ = (Fin N)^ℕ` in Bowen's sense: there are
`c₁, c₂ > 0` and `P` with `c₁ ≤ ν[x₀ ⋯ x_{m-1}] / exp(-P m + ∑_{k<m} φ(σ^k x)) ≤ c₂` for every
`x ∈ Σ` and `m ≥ 0`, where `σ` is the left shift. -/
def IsGibbsMeasure {N : ℕ} (φ : (ℕ → Fin N) → ℝ) (ν : Measure (ℕ → Fin N)) : Prop :=
  ∃ c₁ > 0, ∃ c₂ > 0, ∃ P : ℝ, ∀ (x : ℕ → Fin N) (m : ℕ),
    c₁ * Real.exp (-P * m + ∑ k ∈ Finset.range m, φ (fun i => x (i + k))) ≤
        ν.real {y | ∀ i < m, y i = x i} ∧
      ν.real {y | ∀ i < m, y i = x i} ≤
        c₂ * Real.exp (-P * m + ∑ k ∈ Finset.range m, φ (fun i => x (i + k)))

/-- Bowen's Theorem 1.4 for the one-sided full shift on `N ≥ 1` symbols: a potential `φ` with
`sup{|φ(x) - φ(y)| : x_i = y_i for i < k} ≤ b α^k` for all `k`, where `b > 0` and `0 < α < 1`, has a
Gibbs measure. Bowen states the theorem for two-sided mixing subshifts of finite type; a potential
of the coordinates `i ≥ 0` has the same variations, and the image of the two-sided Gibbs measure
under `x ↦ (x_i)_{i ≥ 0}` has the same cylinder measures. -/
def BowenGibbsStatement : Prop :=
  ∀ {N : ℕ}, 0 < N → ∀ (φ : (ℕ → Fin N) → ℝ) {b α : ℝ}, 0 < b → 0 < α → α < 1 →
    (∀ (k : ℕ) (x y : ℕ → Fin N), (∀ i < k, x i = y i) → |φ x - φ y| ≤ b * α ^ k) →
    ∃ ν : Measure (ℕ → Fin N), IsProbabilityMeasure ν ∧ IsGibbsMeasure φ ν

/-! ### Entropy, Lyapunov exponent and self-conformal measures -/

/-- The entropy `H(p) = -∑_i p_i log p_i` of a probability vector. -/
noncomputable def entropy {N : ℕ} (p : Fin N → ℝ) : ℝ := -∑ i, p i * Real.log (p i)

/-- `p` is a positive probability vector. -/
def IsProbVec {N : ℕ} (p : Fin N → ℝ) : Prop := (∀ i, 0 < p i) ∧ ∑ i, p i = 1

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- The real map `x ↦ f_i(x)` of the system. -/
def realMap (i : Fin N) (x : ℝ) : ℝ := (Φ.f i x).re

/-- The Lyapunov exponent `χ(Φ, p) = -∑_i p_i ∫ log|f_i'| dμ` of Section 1.2.1, for the measure
`μ`. -/
noncomputable def lyapunov (p : Fin N → ℝ) (μ : Measure ℝ) : ℝ :=
  -∑ i, p i * ∫ x, Real.log |deriv (Φ.realMap i) x| ∂μ

/-- `μ` is the self-conformal measure of `Φ` and `p`, (1.2): a Borel probability measure on `I`
with `μ = ∑_i p_i μ ∘ f_i⁻¹`. -/
def IsSelfConformal (p : Fin N → ℝ) (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ Iᶜ = 0 ∧ μ = ∑ i, ENNReal.ofReal (p i) • μ.map (Φ.realMap i)

/-- Equality in (1.6): the pressure `P(t) = lim_n (1/n) log ∑_{w ∈ Σ_n} ‖f_w'‖^t` has a unique zero
`s(Φ)`, the attractor has Hausdorff dimension `min{1, s(Φ)}`, and for every positive probability
vector `p` the self-conformal measure `μ_p` has local dimension `min{1, H(p)/χ}` at `μ_p`-almost
every point. -/
def DimEquality : Prop :=
  (∃ s : ℝ, (∀ t, Tendsto (fun n : ℕ => Real.log (Φ.pressureSum t n) / n) atTop (𝓝 0) ↔ t = s) ∧
      dimH Φ.attractor = ENNReal.ofReal (min 1 s)) ∧
    ∀ p : Fin N → ℝ, IsProbVec p → ∀ μ : Measure ℝ, Φ.IsSelfConformal p μ →
      ∀ᵐ x ∂μ, Tendsto (fun δ => Real.log (μ.real (closedBall x δ)) / Real.log δ) (𝓝[>] 0)
        (𝓝 (min 1 (entropy p / Φ.lyapunov p μ)))

/-- The potential `φ_s(ω) = s log|f'_{ω₀}(π(σω))|` on `Σ`, where `σ` is the left shift. -/
noncomputable def potential (s : ℝ) (ω : ℕ → Fin N) : ℝ :=
  s * Real.log ‖deriv (Φ.f (ω 0)) (Φ.natProj fun i => ω (i + 1))‖

end IFS

end AnalyticESC
