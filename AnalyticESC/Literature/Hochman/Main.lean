module

public import AnalyticESC.Literature.Hochman.Statement
public import AnalyticESC.Literature.Hochman.Rescaling

@[expose] public section

/-!
# Hochman's entropy growth theorem on the line

The proof of `FractalGeometry.Hochman.HochmanEntropyGrowth`, Rapaport's Theorem 3.2
(arXiv:2412.16753v2, Section 3.1): Hochman's entropy growth under convolution (Hochman, *On
self-similar sets with overlaps and inverse theorems for entropy*, Ann. of Math. 180 (2014),
Theorem 2.8, a consequence of his inverse theorem, Theorem 2.7) in the scale-shifted form of
Bárány–Hochman–Rapaport (Invent. Math. 216 (2019), Theorem 4.1).

## Strategy

The core input is the sufficient inverse theorem of the vendored Kittle–Kogler library,
`ExactOverlaps.Entropy.exists_sufficient_inverse_entropy`: for measures `μ, ν` on `[0, 1]`, if all
but a mass `e/32` of the components of `μ` (over the levels `0 ≤ q < n`) have entropy at most
`1 - a` at a scale `M ≥ M₀(a, e)`, and if `H_n(ν) > e`, then `H_n(μ ∗ ν) ≥ H_n(μ) + γ`. Its proof
is Hochman's: positive entropy gives many levels with components of large variance, the
quantitative central limit theorem makes the components of `ν^{∗k}` almost uniform at those
levels, the multiscale formula turns this into entropy growth of `μ ∗ ν^{∗k}`, and the
Kaimanovich–Vershik inequality brings the growth back to `μ ∗ ν`. We add:

1. the scale transfer (`FractalGeometry/Hochman/ScaleTransfer.lean`): the hypothesis at the given
   scale `m` gives the hypothesis at a large scale `M ≥ max(M₀, 4m/ε)`, with the exceptional mass
   multiplied by `2` up to boundary terms (Hochman's Lemmas 3.4 and 3.7);
2. the rescaling (`FractalGeometry/Hochman/Rescaling.lean`) `x ↦ (2^i x - K)/2^c`, which maps the
   intervals of length `ε⁻¹ 2^{-i}` into `[0, 1]` and the levels `i + p` to the levels `c + p`;
3. the bridges between the shared vocabulary and the Kittle–Kogler library
   (`FractalGeometry/Hochman/Bridge.lean`, `FractalGeometry/Hochman/Entropy.lean`).

The parameters: `e = ε/2`, `a = ε/4`, `η₀ = ε/512`, `2^c ≥ 1 + ε⁻¹`, `M = max(M₀, ⌈4m/ε⌉)`, and
`δ = γ(a, e, M)` from the Kittle–Kogler theorem.

## Main declarations

* `FractalGeometry.Hochman.entropyGrowth_of_offset`: the statement for every offset `i ≥ 0`.
* `FractalGeometry.Hochman.hochmanEntropyGrowth : HochmanEntropyGrowth`.
* `FractalGeometry.Hochman.hochman_theorem_2_8`: Hochman's Theorem 2.8 on `[0, 1]`, with the
  exceptional mass `η < η₀(ε)`.

Copied from the library `FractalGeometry` (module `FractalGeometry.Hochman.Main`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.Hochman

open MeasureTheory Set FractalGeometry.SelfConformal
open scoped MeasureTheory

/-- Hochman's entropy growth theorem in the form of Rapaport's Theorem 3.2, for every scale offset
`i ≥ 0` (the statement `HochmanEntropyGrowth` asks for `i ≥ 1`). -/
theorem entropyGrowth_of_offset : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η₀ : ℝ, 0 < η₀ ∧
    ∀ m : ℕ, 1 ≤ m → ∀ η : ℝ, 0 < η → η < η₀ →
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ i : ℕ,
    ∀ ξ θ : Measure ℝ, IsProbabilityMeasure ξ → IsProbabilityMeasure θ →
      (∃ a : ℝ, ξ (Set.Icc a (a + ε⁻¹ / 2 ^ i))ᶜ = 0) →
      (∃ b : ℝ, θ (Set.Icc b (b + ε⁻¹ / 2 ^ i))ᶜ = 0) →
      ε < dyadicEntropy ξ (i + n) / n →
      1 - η < levelProb θ i n (fun j x => dyadicEntropy (component θ j x) (j + m) / m < 1 - ε) →
      dyadicEntropy θ (i + n) / n + δ ≤ dyadicEntropy (ξ ∗ θ) (i + n) / n := by
  intro ε hε hε1
  have he : (0 : ℝ) < ε / 2 := by positivity
  have ha : (0 : ℝ) < ε / 4 := by positivity
  obtain ⟨M₀, -, hKK⟩ := ExactOverlaps.Entropy.exists_sufficient_inverse_entropy ha he
  obtain ⟨c, hc⟩ : ∃ c : ℕ, 1 + ε⁻¹ ≤ 2 ^ c := by
    obtain ⟨c, hc⟩ := pow_unbounded_of_one_lt (1 + ε⁻¹) (one_lt_two : (1 : ℝ) < 2)
    exact ⟨c, hc.le⟩
  refine ⟨ε / 512, by positivity, fun m hm η hη hηlt => ?_⟩
  set M : ℕ := max M₀ ⌈4 * (m : ℝ) / ε⌉₊
  have hmM : 4 * (m : ℝ) ≤ ε * M := by
    have h1 : 4 * (m : ℝ) / ε ≤ M :=
      (Nat.le_ceil _).trans (Nat.cast_le.2 (le_max_right M₀ ⌈4 * (m : ℝ) / ε⌉₊))
    rw [div_le_iff₀ hε] at h1
    linarith
  have hm0 : 0 < m := hm
  obtain ⟨γ, hγ, N, -, hgain⟩ := hKK M (le_max_left _ _)
  set T : ℕ := ⌈64 * ((c : ℝ) + 2 * M) / (ε / 2)⌉₊
  refine ⟨γ, hγ, N + c + T + 1, ?_⟩
  intro n hn i ξ θ hξ hθ ⟨a₁, ha₁⟩ ⟨b₁, hb₁⟩ hent hlev
  -- elementary bounds on `n`
  have hnN : N ≤ c + n := by omega
  have hcn : c ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
  have hTn : 64 * ((c : ℝ) + 2 * M) / (ε / 2) ≤ n :=
    (Nat.le_ceil _).trans (Nat.cast_le.2 (show T ≤ n by omega))
  have hcM : (c : ℝ) + 2 * M ≤ ε / 128 * n := by
    rw [div_le_iff₀ he] at hTn
    linarith
  -- the rescaled measures on `[0, 1]`
  set K₁ : ℤ := ⌊2 ^ i * a₁⌋
  set K₂ : ℤ := ⌊2 ^ i * b₁⌋
  set ξ₂ := ξ.map (resc i c K₁)
  set θ₂ := θ.map (resc i c K₂)
  have : IsProbabilityMeasure ξ₂ := inferInstance
  have : IsProbabilityMeasure θ₂ := inferInstance
  have hξ₂ : ξ₂ (Icc 0 1)ᶜ = 0 := map_resc_compl_Icc ξ ha₁ hc
  have hθ₂ : θ₂ (Icc 0 1)ᶜ = 0 := map_resc_compl_Icc θ hb₁ hc
  have hμ := hasBoundedSupport_toPM θ₂ hθ₂
  have hν := hasBoundedSupport_toPM ξ₂ hξ₂
  -- the entropy hypothesis for `ξ₂`
  have hentK : ε / 2 < ExactOverlaps.Entropy.normalizedDyadicEntropy (toPM ξ₂) hν (c + n) := by
    rw [normalizedDyadicEntropy_eq, toPM_coe, dyadicEntropy_map_resc]
    have h1 : ε * n < dyadicEntropy ξ (i + n) := by
      rw [lt_div_iff₀ hn'] at hent
      exact hent
    have hcn' : (c : ℝ) ≤ n := by exact_mod_cast hcn
    rw [lt_div_iff₀ (by positivity)]
    push_cast
    nlinarith
  -- the deficiency hypothesis for `θ₂` at scale `M`
  set P : ℕ → ℝ → Prop := fun j x => dyadicEntropy (component θ j x) (j + m) / m < 1 - ε
  have hPmeas : ∀ j, MeasurableSet {x | P j x} := fun j =>
    measurableSet_setOf_component θ j fun ρ => dyadicEntropy ρ (j + m) / m < 1 - ε
  have huniform : ∑ j ∈ Finset.Icc i (i + n), θ.real (uniformSet θ ε m j) <
      η * (n + 1) := by
    have hcompl : ∀ j, θ.real (uniformSet θ ε m j) = 1 - θ.real {x | P j x} := by
      intro j
      rw [← probReal_compl_eq_one_sub (hPmeas j)]
      congr 1
      ext x
      simp only [mem_compl_iff, Set.mem_ofPred_eq, not_lt, uniformSet, P]
    simp_rw [hcompl]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    have hlev' := hlev
    rw [levelProb, lt_div_iff₀ (by positivity)] at hlev'
    have : ((i + n + 1 - i : ℕ) : ℝ) = n + 1 := by
      rw [show i + n + 1 - i = n + 1 by omega]
      push_cast
      ring
    rw [this]
    linarith
  have hbad := sum_measureReal_uniform_le θ hε le_rfl (by linarith) hm0 hmM i n
  have htail : 1 - ε / 2 / 32 ≤
      ExactOverlaps.Entropy.levelEntropyLowerTailMass (toPM θ₂) hμ (c + n) M (ε / 4) := by
    unfold ExactOverlaps.Entropy.levelEntropyLowerTailMass
    simp_rw [componentEntropyLowerTailMass_eq θ₂ hθ₂ hμ]
    rw [Finset.sum_range_add]
    have hlow : 0 ≤ ∑ q ∈ Finset.range c,
        θ₂.real {x | dyadicEntropy (component θ₂ q x) (q + M) / M ≤ 1 - ε / 4} :=
      Finset.sum_nonneg fun q _ => measureReal_nonneg
    have hhigh : ∀ p ∈ Finset.range n,
        θ₂.real {x | dyadicEntropy (component θ₂ (c + p) x) (c + p + M) / M ≤ 1 - ε / 4} =
          1 - θ.real {x | 1 - ε / 4 < dyadicEntropy (component θ (i + p) x) (i + p + M) / M} := by
      intro p _
      rw [measureReal_map_resc_setOf_component θ i c p M K₂ (fun h => h / M ≤ 1 - ε / 4),
        ← probReal_compl_eq_one_sub (measurableSet_setOf_component θ (i + p)
          fun ρ => 1 - ε / 4 < dyadicEntropy ρ (i + p + M) / M)]
      congr 1
      ext x
      simp only [mem_compl_iff, Set.mem_ofPred_eq, not_lt]
    rw [Finset.sum_congr rfl hhigh, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, le_div_iff₀ (by positivity)]
    push_cast
    have hηn : 2 * (η * (n + 1)) ≤ ε / 128 * n := by
      have h1 : η * (n + 1) ≤ ε / 512 * (n + 1) := by nlinarith
      have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have h2 : ε * 1 ≤ ε * n := mul_le_mul_of_nonneg_left hn1' hε.le
      linarith
    nlinarith
  -- the Kittle–Kogler theorem and the conclusion
  have hK := hgain (c + n) hnN (toPM θ₂) (toPM ξ₂) hμ hν (ae_iff.2 hθ₂) (ae_iff.2 hξ₂) htail hentK
  rw [normalizedDyadicEntropy_eq, normalizedDyadicEntropy_eq,
    ExactOverlaps.Entropy.realConvolution_toMeasure, toPM_coe, toPM_coe, map_resc_conv,
    dyadicEntropy_map_resc, dyadicEntropy_map_resc, Measure.conv_comm θ ξ] at hK
  have hD : (0 : ℝ) < ((c + n : ℕ) : ℝ) := by positivity
  rw [div_add' _ _ _ hD.ne', div_le_div_iff_of_pos_right hD] at hK
  have hcn' : (n : ℝ) ≤ ((c + n : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ c + n)
  rw [div_add' _ _ _ hn'.ne', div_le_div_iff_of_pos_right hn']
  nlinarith

/-- Hochman's entropy growth theorem in the form of Rapaport's Theorem 3.2 (arXiv:2412.16753v2),
from Hochman (Ann. of Math. 180 (2014), Theorem 2.8) and Bárány–Hochman–Rapaport
(Invent. Math. 216 (2019), Theorem 4.1). -/
theorem hochmanEntropyGrowth : HochmanEntropyGrowth := by
  intro ε hε hε1
  obtain ⟨η₀, hη₀, h⟩ := entropyGrowth_of_offset ε hε hε1
  refine ⟨η₀, hη₀, fun m hm η hη hηlt => ?_⟩
  obtain ⟨δ, hδ, N₀, hN⟩ := h m hm η hη hηlt
  exact ⟨δ, hδ, N₀, fun n hn i _ => hN n hn i⟩

/-- Hochman's Theorem 2.8 (Ann. of Math. 180 (2014)) for probability measures on `[0, 1]`, with
the non-uniformity of the components of `μ` required outside a mass `η < η₀(ε)`: if
`ℙ_{0 ≤ j ≤ n}(H(μ_{x,j}, 𝒟_{j+m}) / m < 1 - ε) > 1 - η` and `H(ν, 𝒟_n) / n > ε`, then
`H(μ ∗ ν, 𝒟_n) / n ≥ H(μ, 𝒟_n) / n + δ`. -/
theorem hochman_theorem_2_8 : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η₀ : ℝ, 0 < η₀ ∧
    ∀ m : ℕ, 1 ≤ m → ∀ η : ℝ, 0 < η → η < η₀ →
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∀ μ ν : Measure ℝ, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      μ (Icc 0 1)ᶜ = 0 → ν (Icc 0 1)ᶜ = 0 →
      1 - η < levelProb μ 0 n (fun j x => dyadicEntropy (component μ j x) (j + m) / m < 1 - ε) →
      ε < dyadicEntropy ν n / n →
      dyadicEntropy μ n / n + δ ≤ dyadicEntropy (μ ∗ ν) n / n := by
  intro ε hε hε1
  obtain ⟨η₀, hη₀, h⟩ := entropyGrowth_of_offset ε hε hε1
  refine ⟨η₀, hη₀, fun m hm η hη hηlt => ?_⟩
  obtain ⟨δ, hδ, N₀, hN⟩ := h m hm η hη hηlt
  refine ⟨δ, hδ, N₀, fun n hn μ ν hμ hν hμ01 hν01 hlev hent => ?_⟩
  have hsub : (Icc (0 : ℝ) (0 + ε⁻¹ / 2 ^ 0))ᶜ ⊆ (Icc 0 1)ᶜ := by
    refine compl_subset_compl.2 (Icc_subset_Icc le_rfl ?_)
    rw [pow_zero, div_one, zero_add]
    exact (one_le_inv₀ hε).2 hε1.le
  have h := hN n hn 0 ν μ hν hμ ⟨0, measure_mono_null hsub hν01⟩
    ⟨0, measure_mono_null hsub hμ01⟩ (by rwa [zero_add]) hlev
  rwa [zero_add, Measure.conv_comm ν μ] at h

end FractalGeometry.Hochman
