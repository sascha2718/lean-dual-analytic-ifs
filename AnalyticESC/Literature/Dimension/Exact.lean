module

public import Mathlib
public import AnalyticESC.Literature.Ergodic.Birkhoff

@[expose] public section

/-!
Copied from the library `FractalGeometry` (module `FractalGeometry.Dimension.Exact`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Metric

open scoped ENNReal

section Definitions

def HasLocalDim {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (x : X) (d : ℝ) : Prop :=
  Tendsto (fun r : ℝ => Real.log (μ.real (closedBall x r)) / Real.log r) (𝓝[>] 0) (𝓝 d)

def IsExactDim {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (d : ℝ) : Prop := ∀ᵐ x ∂μ, HasLocalDim μ x d

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  {μ ν' ν : Measure X} {x : X} {d d' d₁ d₂ : ℝ}

end Definitions

end FractalGeometry
