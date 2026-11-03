module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.TupleConvolution
public import Mathlib.Probability.Independence.CharacteristicFunction

set_option maxSynthPendingDepth 3

/-!
# Continuous product realization of tuple convolutions

The product is the genuine finite product measure of the selected real
laws. Its coordinates have the stated marginals and are independent.
Characteristic-function uniqueness identifies the sum pushforward with the
recursive real convolution, including the empty family.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.ContinuousProductLaw`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ExactOverlaps.Entropy

noncomputable def continuousProductLaw {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) : ProbabilityMeasure (ι → ℝ) :=
  ⟨Measure.pi (fun i ↦ (ν i : Measure ℝ)), inferInstance⟩

noncomputable def continuousSumLaw {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  (continuousProductLaw ν).map (fun w ↦ ∑ i, w i)

lemma continuousProductLaw_map_coordinate {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) (i : ι) :
    (continuousProductLaw ν).map (fun w ↦ w i) = ν i := by
  apply ProbabilityMeasure.toMeasure_injective
  exact (measurePreserving_eval (fun j ↦ (ν j : Measure ℝ)) i).map_eq

lemma continuousProductLaw_independent {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) :
    iIndepFun (fun i (w : ι → ℝ) ↦ w i) (continuousProductLaw ν : Measure (ι → ℝ)) :=
  iIndepFun_pi (X := fun _ ↦ (id : ℝ → ℝ)) (fun _ ↦ aemeasurable_id)

lemma charFun_continuousSumLaw {ι : Type*} [Fintype ι]
    (ν : ι → ProbabilityMeasure ℝ) (t : ℝ) :
    charFun (continuousSumLaw ν : Measure ℝ) t = ∏ i, charFun (ν i : Measure ℝ) t := by
  have h := congrArg (fun f : ℝ → ℂ ↦ f t)
    (charFun_map_sum_pi_eq_prod (fun i ↦ (ν i : Measure ℝ)))
  rw [continuousSumLaw, ProbabilityMeasure.toMeasure_map]
  change charFun ((Measure.pi (fun i ↦ (ν i : Measure ℝ))).map
    (fun w : ι → ℝ ↦ ∑ i, w i)) t = _
  simpa only [Finset.prod_apply] using h

lemma charFun_tupleConvolution {α : Type*} (ν : α → ProbabilityMeasure ℝ)
    (n : ℕ) (w : FiniteTuple α n) (t : ℝ) :
    charFun (tupleConvolution ν n w : Measure ℝ) t =
      ∏ i : Fin n, charFun (ν (tupleCoordinate n w i) : Measure ℝ) t := by
  induction n with
  | zero =>
    change charFun (Measure.dirac (0 : ℝ)) t = ∏ i : Fin 0, _
    simp [charFun_dirac]
  | succ n ih =>
    rw [tupleConvolution, realConvolution_toMeasure, charFun_conv, Fin.prod_univ_succ]
    simp only [tupleCoordinate, Fin.cases_zero, Fin.cases_succ]
    rw [ih w.2]

theorem tupleConvolution_eq_continuousSumLaw {α : Type*} (ν : α → ProbabilityMeasure ℝ)
    (n : ℕ) (w : FiniteTuple α n) :
    tupleConvolution ν n w = continuousSumLaw (fun i ↦ ν (tupleCoordinate n w i)) := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_tupleConvolution, charFun_continuousSumLaw]

end ExactOverlaps.Entropy
