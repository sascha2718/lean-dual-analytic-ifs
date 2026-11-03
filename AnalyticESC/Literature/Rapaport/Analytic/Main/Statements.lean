module

public import AnalyticESC.Literature.Rapaport.Analytic.Statements
public import AnalyticESC.Literature.SelfConformal.Toolkit

@[expose] public section

/-!
# Inputs and intermediate statements for Section 4 of Rapaport

Statements used by the formalisation of Section 4 of A. Rapaport, *Dimension of self-conformal
measures associated to an exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2: the
proof of Theorem 1.2 from the entropy increase theorem (Theorem 3.1) and the results of Feng and
Hu.

## Main declarations

* `wordMap φ u`: the composition `φ_u = φ_{u_0} ∘ ⋯ ∘ φ_{u_{n-1}}` for a word `u : Fin n → Fin N`.
* `FibreEntropyVanishes φ p hp`: the conclusion of the argument of Section 4. If `μ` is exact
  dimensional with dimension `d < 1`, the fibre measures `β_x` have cylinder entropy rate `0`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Rapaport.Analytic.Main.Statements`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Rapaport.Analytic

open MeasureTheory Set Filter Topology FractalGeometry.SelfConformal

variable {N : ℕ}

/-- The composition `φ_u = φ_{u_0} ∘ ⋯ ∘ φ_{u_{n-1}}` along a word `u` of length `n`, outermost
letter first. -/
noncomputable def wordMap (φ : Fin N → ℝ → ℝ) {n : ℕ} (u : Fin n → Fin N) : ℝ → ℝ :=
  AnalyticESC.realComp φ (List.ofFn u)

/-- The conclusion of the argument of Section 4 of Rapaport (arXiv:2412.16753v2): if the
self-conformal measure `μ` is exact dimensional with dimension `d < 1` and the fibre measures
`β_x` have cylinder entropy rate `Δ'` for `μ`-a.e. `x`, then `Δ' ≤ 0`. Rapaport derives a
contradiction from `Δ' > 0`. -/
def FibreEntropyVanishes [NeZero N] (φ : Fin N → ℝ → ℝ) (p : Fin N → ℝ)
    (hp : AnalyticESC.IsProbVec p) : Prop :=
  ∀ d Δ' : ℝ, FractalGeometry.IsExactDim (selfConformal φ p hp) d → d < 1 →
    (∀ᵐ x ∂(selfConformal φ p hp),
      Tendsto (fun l : ℕ => cylEntropy (fibre φ p hp x) l / l) atTop (𝓝 Δ')) →
    Δ' ≤ 0

end FractalGeometry.Rapaport.Analytic
