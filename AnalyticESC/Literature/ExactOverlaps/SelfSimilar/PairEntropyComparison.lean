module

public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.EntropyComparison
public import Mathlib.Data.Int.Interval

set_option maxSynthPendingDepth 3

/-!
Comparing integer-valued marginals of a finite coupling. A bounded interval
of possible label differences gives a quantitative entropy comparison. This
is the finite probabilistic core of dyadic grid translation and displacement
estimates, and does not presume regularity or separation of the underlying law.

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.PairEntropyComparison`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open scoped Classical

namespace ExactOverlaps.Entropy

theorem fst_fiber_card_le_of_sub_mem_Icc (p : PMF (ℤ × ℤ))
    (hp : p.support.Finite) {l u : ℤ}
    (hband : ∀ z ∈ p.support, z.2 - z.1 ∈ Set.Icc l u) (b : ℤ) :
    (hp.toFinset.filter (fun z ↦ z.1 = b)).card ≤ (u - l + 1).toNat := by
  have hsub : hp.toFinset.filter (fun z ↦ z.1 = b) ⊆
      (Finset.Icc (b + l) (b + u)).image (fun j ↦ (b, j)) := by
    intro z hz
    obtain ⟨hz, hzb⟩ := Finset.mem_filter.mp hz
    obtain ⟨hl, hu⟩ := hband z (by simpa using hz)
    refine Finset.mem_image.mpr ⟨z.2, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      constructor <;> omega
    · exact Prod.ext hzb.symm rfl
  calc
    (hp.toFinset.filter (fun z ↦ z.1 = b)).card ≤
        ((Finset.Icc (b + l) (b + u)).image (fun j ↦ (b, j))).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.Icc (b + l) (b + u)).card := Finset.card_image_le
    _ = (u - l + 1).toNat := by rw [Int.card_Icc]; congr 1; omega

/-- An integer interval containing every label difference bounds the entropy difference. -/
theorem snd_entropy_sub_fst_le_of_sub_mem_Icc (p : PMF (ℤ × ℤ))
    (hp : p.support.Finite) {l u : ℤ}
    (hband : ∀ z ∈ p.support, z.2 - z.1 ∈ Set.Icc l u) :
    finiteEntropy (p.map Prod.snd) (by simpa using hp.image Prod.snd) -
      finiteEntropy (p.map Prod.fst) (by simpa using hp.image Prod.fst) ≤
      Real.log (u - l + 1).toNat := by
  apply entropy_map_sub_le_log_of_fiber_card_le p hp Prod.fst Prod.snd
  intro b
  convert fst_fiber_card_le_of_sub_mem_Icc p hp hband b using 1
  congr 1
  ext z
  simp only [Finset.mem_filter]

/-- The same bound is symmetric in the two marginals of the coupling. -/
theorem abs_snd_entropy_sub_fst_le_of_sub_mem_Icc (p : PMF (ℤ × ℤ))
    (hp : p.support.Finite) {l u : ℤ}
    (hband : ∀ z ∈ p.support, z.2 - z.1 ∈ Set.Icc l u) :
    |finiteEntropy (p.map Prod.snd) (by simpa using hp.image Prod.snd) -
      finiteEntropy (p.map Prod.fst) (by simpa using hp.image Prod.fst)| ≤
      Real.log (u - l + 1).toNat := by
  let q := p.map Prod.swap
  have hq : q.support.Finite := by simpa [q] using hp.image Prod.swap
  have hrev : ∀ z ∈ q.support, z.2 - z.1 ∈ Set.Icc (-u) (-l) := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    obtain ⟨hl, hu⟩ := hband w hw
    subst z
    constructor <;> dsimp only [Prod.swap] <;> omega
  have hfwd := snd_entropy_sub_fst_le_of_sub_mem_Icc p hp hband
  have hback := snd_entropy_sub_fst_le_of_sub_mem_Icc q hq hrev
  have heq : -l - -u + 1 = u - l + 1 := by omega
  simp only [heq, q, PMF.map_comp, Function.comp_def, Prod.snd_swap, Prod.fst_swap] at hback
  exact abs_le.mpr ⟨by linarith, hfwd⟩

end ExactOverlaps.Entropy
