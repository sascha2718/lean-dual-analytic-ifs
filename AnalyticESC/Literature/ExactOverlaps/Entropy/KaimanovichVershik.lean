module

/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Convolution
public import AnalyticESC.Literature.ExactOverlaps.Entropy.Submodularity

set_option maxSynthPendingDepth 3

/-!
# The finite Kaimanovich–Vershik entropy inequality

Strong subadditivity is applied to the total sum, the first summand, and
the first partial sum of three independent finite laws. Injective recodings
identify the joint entropies. This proves that adding independent noise
decreases a convolution entropy increment.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.Entropy.KaimanovichVershik`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

namespace ExactOverlaps.Entropy

lemma sum_fst_injective {G : Type*} [AddLeftCancelSemigroup G] :
    Function.Injective (fun x : G × G ↦ (x.1 + x.2, x.1)) := by
  intro a b h
  have hx : a.1 = b.1 := congrArg Prod.snd h
  have hs : a.1 + a.2 = b.1 + b.2 := congrArg Prod.fst h
  exact Prod.ext hx (add_left_cancel (by simpa only [hx] using hs))

lemma total_first_partial_injective {G : Type*} [AddLeftCancelSemigroup G] :
    Function.Injective (fun x : G × (G × G) ↦
      (x.1 + x.2.1 + x.2.2, (x.1, x.1 + x.2.1))) := by
  intro a b h
  have hx : a.1 = b.1 := congrArg (fun x : G × (G × G) ↦ x.2.1) h
  have hv : a.1 + a.2.1 = b.1 + b.2.1 :=
    congrArg (fun x : G × (G × G) ↦ x.2.2) h
  have hs : a.1 + a.2.1 + a.2.2 = b.1 + b.2.1 + b.2.2 := congrArg Prod.fst h
  have hy : a.2.1 = b.2.1 := add_left_cancel (by simpa only [hx] using hv)
  have hz : a.2.2 = b.2.2 := add_left_cancel (by simpa only [hv] using hs)
  exact Prod.ext hx (Prod.ext hy hz)

/-- The entropy increment from adding `r` decreases after adding an independent `p`. -/
theorem finiteEntropy_convolution_increment_le {G : Type*} [AddLeftCancelSemigroup G]
    (p q r : PMF G)
    (hp : p.support.Finite) (hq : q.support.Finite) (hr : r.support.Finite) :
    finiteEntropy (discreteConvolution (discreteConvolution p q) r)
        (discreteConvolution_support_finite _ _ (discreteConvolution_support_finite p q hp hq) hr) +
      finiteEntropy q hq ≤
    finiteEntropy (discreteConvolution p q) (discreteConvolution_support_finite p q hp hq) +
      finiteEntropy (discreteConvolution q r) (discreteConvolution_support_finite q r hq hr) := by
  let w := independentPair p (independentPair q r)
  let hw : w.support.Finite :=
    independentPair_support_finite p _ hp (independentPair_support_finite q r hq hr)
  let s : G × (G × G) → G := fun x ↦ x.1 + x.2.1 + x.2.2
  let x : G × (G × G) → G := fun a ↦ a.1
  let v : G × (G × G) → G := fun a ↦ a.1 + a.2.1
  have hX : w.map (fun a ↦ (a.1, a.2.1 + a.2.2)) =
      independentPair p (discreteConvolution q r) :=
    independentPair_map_right p (independentPair q r) (fun a ↦ a.1 + a.2)
  have hV : w.map (fun a ↦ (a.1 + a.2.1, a.2.2)) =
      independentPair (discreteConvolution p q) r := by
    calc
      _ = (w.map (fun a ↦ ((a.1, a.2.1), a.2.2))).map
          (fun a ↦ (a.1.1 + a.1.2, a.2)) := by rw [PMF.map_comp]; rfl
      _ = _ := by
        rw [independentPair_assoc]
        exact independentPair_map_left (independentPair p q) r (fun a ↦ a.1 + a.2)
  have hS : w.map s = discreteConvolution (discreteConvolution p q) r := by
    rw [discreteConvolution, ← hV, PMF.map_comp]
    rfl
  have hSX : w.map (fun a ↦ (s a, x a)) =
      (independentPair p (discreteConvolution q r)).map (fun a ↦ (a.1 + a.2, a.1)) := by
    rw [← hX, PMF.map_comp]
    congr 1
    funext a
    simp only [s, x, Function.comp_def, add_assoc]
  have hSV : w.map (fun a ↦ (s a, v a)) =
      (independentPair (discreteConvolution p q) r).map (fun a ↦ (a.1 + a.2, a.1)) := by
    rw [← hV, PMF.map_comp]
    rfl
  have htriple := finiteEntropy_map_of_injective w hw
    (total_first_partial_injective (G := G))
  change finiteEntropy (w.map (fun a ↦ (s a, (x a, v a)))) _ = _ at htriple
  rw [finiteEntropy_independentPair p _ hp (independentPair_support_finite q r hq hr),
    finiteEntropy_independentPair q r hq hr] at htriple
  have hentSX : finiteEntropy (w.map (fun a ↦ (s a, x a)))
      (by simpa using hw.image (fun a ↦ (s a, x a))) =
      finiteEntropy p hp + finiteEntropy (discreteConvolution q r)
        (discreteConvolution_support_finite q r hq hr) := by
    apply (finiteEntropy_congr hSX _ _).trans
    apply (finiteEntropy_map_of_injective _ _ (sum_fst_injective (G := G))).trans
    exact finiteEntropy_independentPair _ _ _ _
  have hentSV : finiteEntropy (w.map (fun a ↦ (s a, v a)))
      (by simpa using hw.image (fun a ↦ (s a, v a))) =
      finiteEntropy (discreteConvolution p q) (discreteConvolution_support_finite p q hp hq) +
        finiteEntropy r hr := by
    apply (finiteEntropy_congr hSV _ _).trans
    apply (finiteEntropy_map_of_injective _ _ (sum_fst_injective (G := G))).trans
    exact finiteEntropy_independentPair _ _ _ _
  have h := finiteEntropy_submodular w hw s x v
  rw [htriple, hentSX, hentSV] at h
  have hentS := finiteEntropy_congr hS
    (show (w.map s).support.Finite from by simpa using hw.image s)
    (discreteConvolution_support_finite _ _ (discreteConvolution_support_finite p q hp hq) hr)
  rw [hentS] at h
  linarith

end ExactOverlaps.Entropy
