module

public import AnalyticESC.Dimension.Defs
public import AnalyticESC.Literature.Bowen.Main
public import AnalyticESC.Literature.Hochman.Main
public import AnalyticESC.Literature.SelfConformal.FengHu.Main
public import AnalyticESC.Literature.Rapaport.Analytic.EntropyIncrease
public import AnalyticESC.Literature.Rapaport.Analytic.Main.RapaportMeasure
public import AnalyticESC.Literature.Rapaport.Attractor.Corollary

@[expose] public section

/-!
# The cited results of Bowen and Rapaport

The dimension results of the paper use three cited theorems, stated in `Dimension/Defs.lean` as
`BowenGibbsStatement`, `RapaportMeasureStatement` and `RapaportSetStatement`. This module proves
them from Mathlib.

* `bowenGibbsStatement`: R. Bowen, *Equilibrium states and the ergodic theory of Anosov
  diffeomorphisms*, LNM 470 (1975), Theorem 1.4, for the one-sided full shift (`Literature/Bowen`).
* `rapaportMeasureStatement`: A. Rapaport, *Dimension of self-conformal measures associated to an
  exponentially separated analytic IFS on ℝ*, arXiv:2412.16753, Theorem 1.2
  (`Literature/Rapaport/Analytic`), with the exact dimensionality of D.-J. Feng and H. Hu,
  *Dimension theory of iterated function systems*, CPAM 62 (2009), Theorem 2.8
  (`Literature/SelfConformal/FengHu`), and the entropy growth theorem of M. Hochman, *On
  self-similar sets with overlaps and inverse theorems for entropy*, Ann. of Math. 180 (2014),
  Theorem 2.8, in the form of Bárány, Hochman and Rapaport (`Literature/Hochman`), which uses the
  inverse theorem for entropy of S. Kittle and C. Kogler, *The exact overlaps conjecture for
  self-similar measures on the real line*, arXiv:2610.10511 (`Literature/ExactOverlaps`).
* `rapaportSetStatement`: Rapaport, Corollary 1.3 (`Literature/Rapaport/Attractor`).

The modules of `Literature/` are copied from the library `FractalGeometry` of the third author and
from the Kittle–Kogler library `ExactOverlaps` (BSD Zero Clause License,
`Literature/ExactOverlaps/LICENSE`). Each records its source in its docstring and keeps the
namespace of its origin.
-/

namespace AnalyticESC.Literature

/-- Bowen's theorem on the one-sided full shift, in the form `BowenGibbsStatement`. -/
theorem bowenGibbsStatement : AnalyticESC.BowenGibbsStatement :=
  FractalGeometry.Bowen.bowenGibbsStatement_holds

/-- Rapaport's Theorem 1.2 with the exact dimensionality of Feng and Hu, in the form
`RapaportMeasureStatement`. -/
theorem rapaportMeasureStatement : AnalyticESC.RapaportMeasureStatement :=
  FractalGeometry.Rapaport.Analytic.rapaportMeasure
    (fun _ hφ _ hp => FractalGeometry.Rapaport.Analytic.entropyIncreasePoly
      FractalGeometry.Hochman.hochmanEntropyGrowth hφ hp)
    (fun _ hφ _ hp => FractalGeometry.SelfConformal.FengHu.fengHuInterface_holds hφ hp)

/-- Rapaport's Corollary 1.3, in the form `RapaportSetStatement`. -/
theorem rapaportSetStatement : AnalyticESC.RapaportSetStatement :=
  FractalGeometry.Rapaport.Attractor.rapaportSet_of_measure rapaportMeasureStatement
    bowenGibbsStatement

end AnalyticESC.Literature
