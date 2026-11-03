module

public import AnalyticESC.Literature.SelfConformal.FengHu.ExactDim

@[expose] public section

/-!
# Entropy of the fibre measures

D.-J. Feng and H. Hu, *Dimension theory of iterated function systems*, Comm. Pure Appl. Math. 62
(2009), Proposition 4.10, for a conformal system on the line: for `μ`-a.e. `x`, the fibre measure
`β_x` (the disintegration of the Bernoulli measure `β` over the coding map `Π`) has cylinder
entropy rate `Δ = ∫ -log β_{Π ω}[ω_0] dβ(ω)`, the conditional information of the first letter
given the coding (`condInfo`, equal to `-log β_{Π ω}[ω_0]` almost surely).

The cocycle identity `β_{Π ω}[ω|_{l+1}] = β_{Π ω}[ω_0] β_{Π σ ω}[(σ ω)|_l]` (`ae_fibre_cocycle`)
makes the fibre information `-log β_{Π ω}[ω|_l]` a Birkhoff sum of `condInfo`, so Birkhoff's
theorem gives the pointwise rate `Δ`; disintegrating, the rate holds `β_x`-a.e. for `μ`-a.e. `x`,
and `tendsto_cylEntropy_div_of_ae` turns it into the entropy rate.

## Main declarations

* `ae_condInfo_eq`: `condInfo ω = -log β_{Π ω}[ω_0]` for `β`-a.e. `ω`.
* `ConformalIFS.ae_cylInfo_eq_birkhoffSum`: `-log β_{Π ω}[ω|_l]` is the Birkhoff sum of
  `condInfo`.
* `ConformalIFS.ae_tendsto_cylEntropy_fibre`: for `μ`-a.e. `x`,
  `H(β_x, 𝒞_l) / l → ∫ condInfo dβ`.

Copied from the library `FractalGeometry` (module `FractalGeometry.SelfConformal.FengHu.FibreEntropy`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.SelfConformal.FengHu

open MeasureTheory Set Filter Topology Metric
open AnalyticESC (I realComp IsProbVec)
open FractalGeometry.SelfSimilar.FengHu (densityInfo)

variable {N : ℕ} [NeZero N] {φ : Fin N → ℝ → ℝ} {c L : ℝ} {p : Fin N → ℝ}

/-- `condInfo ω = -log β_{Π ω}[ω_0]` for `β`-a.e. `ω`. -/
theorem ae_condInfo_eq (φ : Fin N → ℝ → ℝ) (hp : IsProbVec p) :
    ∀ᵐ ω ∂bernoulli p hp, condInfo φ p hp ω = cylInfo (fibre φ p hp (coding φ ω)) 1 ω := by
  have h : ∀ᵐ x ∂selfConformal φ p hp, ∀ a : Fin N,
      (kQ φ p hp a).rnDeriv (selfConformal φ p hp) x = fibre φ p hp x {η | η 0 = a} :=
    ae_all_iff.2 fun a => by
      rw [kQ_eq]
      exact rnDeriv_map_restrict φ hp (measurableSet_head a)
  filter_upwards [ae_of_ae_map (measurable_coding φ).aemeasurable h] with ω hω
  rw [condInfo, densityInfo, hω (ω 0), cylInfo, cylinder_pre_one, measureReal_def]

omit [NeZero N] in
/-- The cylinder of the empty word is everything. -/
theorem cylinder_pre_zero (ω : ℕ → Fin N) : cylinder (pre 0 ω) = univ :=
  eq_univ_of_forall fun _ k => k.elim0

namespace ConformalIFS

variable (hφ : ConformalIFS φ c L)
include hφ

/-- The information cocycle `I_{l+1}(ω) = I_1(ω) + I_l(σ ω)` along the fibres. -/
theorem ae_cylInfo_succ (hp : IsProbVec p) :
    ∀ᵐ ω ∂bernoulli p hp, ∀ l,
      cylInfo (fibre φ p hp (coding φ ω)) (l + 1) ω =
        cylInfo (fibre φ p hp (coding φ ω)) 1 ω +
          cylInfo (fibre φ p hp (coding φ (shift ω))) l (shift ω) := by
  have hpos := ae_fibre_cylinder_pos φ hp
  have hpos' := (measurePreserving_shift hp).quasiMeasurePreserving.ae hpos
  filter_upwards [ae_fibre_cocycle hφ hp, hpos, hpos'] with ω hω h1 h2 l
  have hA := h1 1
  have hB := h2 l
  rw [cylInfo, cylInfo, cylInfo, measureReal_def, measureReal_def, measureReal_def, hω l,
    ENNReal.toReal_mul, Real.log_mul (ENNReal.toReal_pos hA.ne' (measure_ne_top _ _)).ne'
      (ENNReal.toReal_pos hB.ne' (measure_ne_top _ _)).ne']
  ring

/-- The fibre information `-log β_{Π ω}[ω|_l]` is the Birkhoff sum of the first-letter
information `-log β_{Π ω}[ω_0]`. -/
theorem ae_cylInfo_eq_birkhoffSum (hp : IsProbVec p) :
    ∀ᵐ ω ∂bernoulli p hp, ∀ l, cylInfo (fibre φ p hp (coding φ ω)) l ω =
      birkhoffSum shift (fun η => cylInfo (fibre φ p hp (coding φ η)) 1 η) l ω := by
  have h := ae_all_iff.2 fun j =>
    ((measurePreserving_shift hp).iterate j).quasiMeasurePreserving.ae (hφ.ae_cylInfo_succ hp)
  filter_upwards [h] with ω hω
  intro l
  induction l generalizing ω with
  | zero =>
    simp [cylInfo, cylinder_pre_zero]
  | succ l ih =>
    rw [birkhoffSum_succ_apply', ← ih (shift ω) fun j => by
      simpa [Function.iterate_succ_apply] using hω (j + 1)]
    simpa using hω 0 l

/-- The pointwise conditional Shannon–McMillan–Breiman theorem along the fibres:
`-log β_{Π ω}[ω|_l] / l → ∫ condInfo dβ` for `β`-a.e. `ω`. -/
theorem ae_tendsto_cylInfo_fibre (hp : IsProbVec p) :
    ∀ᵐ ω ∂bernoulli p hp, Tendsto (fun l : ℕ => cylInfo (fibre φ p hp (coding φ ω)) l ω / l)
      atTop (𝓝 (∫ ω, condInfo φ p hp ω ∂bernoulli p hp)) := by
  set F : (ℕ → Fin N) → ℝ := fun η => cylInfo (fibre φ p hp (coding φ η)) 1 η
  have hF : F =ᵐ[bernoulli p hp] condInfo φ p hp :=
    (ae_condInfo_eq φ hp).mono fun ω h => h.symm
  have hFi : Integrable F (bernoulli p hp) := (hφ.integrable_condInfo hp).congr hF.symm
  have hB := FractalGeometry.Ergodic.birkhoff_ergodic (ergodic_shift hp) hFi
  rw [integral_congr_ae hF] at hB
  filter_upwards [hB, hφ.ae_cylInfo_eq_birkhoffSum hp] with ω hω hsum
  refine hω.congr fun l => ?_
  rw [birkhoffAverage, smul_eq_mul, hsum l]
  ring

/-- **Feng–Hu, Proposition 4.10, on the line**: for `μ`-a.e. `x`, the fibre measure `β_x` has
cylinder entropy rate `∫ condInfo dβ`. -/
theorem ae_tendsto_cylEntropy_fibre (hp : IsProbVec p) :
    ∀ᵐ x ∂selfConformal φ p hp, Tendsto (fun l : ℕ => cylEntropy (fibre φ p hp x) l / l) atTop
      (𝓝 (∫ ω, condInfo φ p hp ω ∂bernoulli p hp)) := by
  filter_upwards [ae_ae_fibre_of_ae φ hp (P := fun x ω => Tendsto
    (fun l : ℕ => cylInfo (fibre φ p hp x) l ω / l) atTop
      (𝓝 (∫ ω, condInfo φ p hp ω ∂bernoulli p hp))) (hφ.ae_tendsto_cylInfo_fibre hp)] with x hx
  exact tendsto_cylEntropy_div_of_ae (fibre φ p hp x) hx

end ConformalIFS

end FractalGeometry.SelfConformal.FengHu
