module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.GaussianComponentMass
public import AnalyticESC.Literature.ExactOverlaps.Entropy.CentralCellApproximation
public import AnalyticESC.Literature.ExactOverlaps.Entropy.ComponentAtomBounds
public import AnalyticESC.Literature.ExactOverlaps.Entropy.FiniteComponentCertificate

set_option maxSynthPendingDepth 3

/-!
# Local uniformity transferred from a Gaussian law

The hypotheses are errors in actual half-open interval probabilities.
The approximating law may have atoms. The positive lower mass of the
reference central cells controls conditional probabilities, and the entire
central block loses just one interval error.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.NearGaussian`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace ExactOverlaps.Entropy

theorem component_lowerTail_le_of_gaussian_interval_error
    (μ : ProbabilityMeasure ℝ) (hμ : HasBoundedSupport μ) (b : ℝ) (v : ℝ≥0)
    {σ V R δ ε : ℝ} (hσ : 0 < σ) (hvσ : σ ≤ (v : ℝ)) (hvV : (v : ℝ) ≤ V)
    (hR : 0 < R) (hδ : 0 < δ) (i : ℕ) {m : ℕ} (hm : 0 < m)
    (hscale : 2 * (R + 1) * (2 : ℝ) ^ (-(i : ℤ)) / σ ≤
      δ * ((m : ℝ) * Real.log 2) / 2)
    (herror : (Real.exp (δ * ((m : ℝ) * Real.log 2) / 2) / (2 : ℝ) ^ m + 1) * ε ≤
      (Real.exp (δ * ((m : ℝ) * Real.log 2) / 2) / (2 : ℝ) ^ m -
        Real.exp (2 * (R + 1) * (2 : ℝ) ^ (-(i : ℤ)) / σ) / (2 : ℝ) ^ m) *
        (gaussianDensityFloor σ V (R + 1) * (2 : ℝ) ^ (-(i : ℤ))))
    (hclose : ∀ a c : ℝ, |((μ : Measure ℝ) (Ico a c)).toReal -
      (gaussianReal b v (Ico a c)).toReal| ≤ ε) :
    componentEntropyLowerTailMass μ hμ i m δ ≤ (v : ℝ) / R ^ 2 + ε := by
  let J := Finset.Icc (dyadicQuantize i (b - R)) (dyadicQuantize i (b + R))
  have hJ : ∀ k : (dyadicLaw μ i).support, k.val ∈ J →
      1 - δ < normalizedDyadicEntropy (rescaledComponent μ i k)
        (rescaledComponent_hasBoundedSupport μ i k) m := by
    intro k hk
    have hk' : k.val ∈ Icc (dyadicQuantize i (b - R)) (dyadicQuantize i (b + R)) := by
      simpa only [J, Finset.mem_Icc, Set.mem_Icc] using hk
    have hA : 0 ≤ Real.exp (2 * (R + 1) * (2 : ℝ) ^ (-(i : ℤ)) / σ) /
        (2 : ℝ) ^ m := by positivity
    have hAB := div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hscale)
      (le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) m))
    have hc := gaussian_central_cell_mass_ge b v hσ hvσ hvV hR.le i k hk'
    rw [dyadicLaw_apply] at hc
    have ha (j : ℤ) := rawComponent_atom_le_of_interval_error μ (gaussianProbability b v)
      hclose i k m hA hAB hc
      (fun j ↦ gaussian_central_inter_mass_le b v hσ hvσ i k m j hk') herror j
    have he := normalizedEntropy_component_ge_of_raw_atom_bound μ i k hm
      (Real.exp_pos (δ * ((m : ℝ) * Real.log 2) / 2)) ha
    have hd : 0 < (m : ℝ) * Real.log 2 :=
      mul_pos (Nat.cast_pos.mpr hm) (Real.log_pos (by norm_num))
    rw [Real.log_exp] at he
    have hcancel : (δ * ((m : ℝ) * Real.log 2) / 2) /
        ((m : ℝ) * Real.log 2) = δ / 2 := by field_simp
    rw [hcancel] at he
    linarith
  have htail := componentEntropyLowerTailMass_le_compl_finset μ hμ i m δ J hJ
  have hmass := central_labels_mass_ge_of_gaussian_interval_error μ b v hclose i hR
  dsimp only [J] at htail
  linarith

end ExactOverlaps.Entropy
