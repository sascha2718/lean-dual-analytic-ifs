module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Convolution
public import Mathlib.MeasureTheory.Group.Convolution

set_option maxSynthPendingDepth 3

/-!
# Agreement of discrete and measure convolution

On countable measurable spaces, the independent PMF pair represents the
product probability measure. The sum law therefore represents convolution
of measures, allowing discrete entropy results to be used for quantized laws.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.DiscreteMeasureConvolution`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set

namespace ExactOverlaps.Entropy

lemma independentPair_toMeasure {α β : Type*} [Countable α] [Countable β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (p : PMF α) (q : PMF β) :
    (independentPair p q).toMeasure = p.toMeasure.prod q.toMeasure := by
  have he : (p.toMeasure.prod q.toMeasure).toPMF = independentPair p q := by
    ext z
    rcases z with ⟨a, b⟩
    rw [Measure.toPMF_apply, ← singleton_prod_singleton, Measure.prod_prod,
      PMF.toMeasure_apply_singleton p a (measurableSet_singleton a),
      PMF.toMeasure_apply_singleton q b (measurableSet_singleton b), independentPair_apply]
  rw [← he, Measure.toPMF_toMeasure]

lemma discreteConvolution_toMeasure {G : Type*} [AddMonoid G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableAdd₂ G] (p q : PMF G) :
    (discreteConvolution p q).toMeasure = p.toMeasure ∗ q.toMeasure := by
  rw [discreteConvolution, ← PMF.toMeasure_map _ _ measurable_add, independentPair_toMeasure]
  rfl

end ExactOverlaps.Entropy
