module

public import AnalyticESC.Literature.ExactOverlaps.Entropy.Dyadic

set_option maxSynthPendingDepth 3

/-! A bounded dyadic law has at most C times 2^n labels at level n. 

Copied unchanged, apart from this paragraph, the module names of the imports, the position
of `module` and the file-level option `maxSynthPendingDepth`, from the library `ExactOverlaps`
of S. Kittle and C. Kogler, module `ExactOverlaps.SelfSimilar.DyadicSupportGrowth`, revision `99c43adec5c5`
(<https://github.com/ckkogler/exact-overlaps-one-dim-lean>), BSD Zero Clause License; see
`AnalyticESC/Literature/ExactOverlaps/LICENSE`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Classical

namespace ExactOverlaps.Entropy

theorem dyadicLaw_card_le_base_mul_pow (μ : ProbabilityMeasure ℝ)
    (hμ : HasBoundedSupport μ) (n : ℕ) :
    (dyadicLaw_support_finite μ hμ n).toFinset.card ≤
      (dyadicLaw_support_finite μ hμ 0).toFinset.card * 2 ^ n := by
  let A := (dyadicLaw_support_finite μ hμ 0).toFinset
  let B := (dyadicLaw_support_finite μ hμ n).toFinset
  let encode : ℤ × ℕ → ℤ := fun z ↦ z.1 * (2 ^ n : ℕ) + z.2
  have hmap : (dyadicLaw μ n).map (fun k : ℤ ↦ k / (2 ^ n : ℕ)) = dyadicLaw μ 0 := by
    simpa only [zero_add] using dyadicLaw_map_div μ 0 n
  have hsub : B ⊆ (A ×ˢ Finset.range (2 ^ n)).image encode := by
    intro k hk
    have hk' : k ∈ (dyadicLaw μ n).support := by simpa [B] using hk
    have hq : k / (2 ^ n : ℕ) ∈ A := by
      change k / (2 ^ n : ℕ) ∈ (dyadicLaw_support_finite μ hμ 0).toFinset
      simp only [Set.Finite.mem_toFinset]
      rw [← hmap]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨k, hk', rfl⟩
    have hd : (0 : ℤ) < (2 ^ n : ℕ) := by positivity
    let r : ℕ := (k % (2 ^ n : ℕ)).toNat
    have hr : (r : ℤ) = k % (2 ^ n : ℕ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ hd.ne')
    have hrlt : r < 2 ^ n := by
      have hh : (r : ℤ) < (2 ^ n : ℕ) := by
        rw [hr]
        exact Int.emod_lt_of_pos _ hd
      exact_mod_cast hh
    apply Finset.mem_image.mpr
    refine ⟨(k / (2 ^ n : ℕ), r), Finset.mem_product.mpr ⟨hq, Finset.mem_range.mpr hrlt⟩, ?_⟩
    dsimp [encode]
    rw [hr]
    convert Int.emod_add_ediv_mul k (2 ^ n : ℕ) using 1
    push_cast
    ring
  calc
    B.card ≤ ((A ×ˢ Finset.range (2 ^ n)).image encode).card := Finset.card_le_card hsub
    _ ≤ (A ×ˢ Finset.range (2 ^ n)).card := Finset.card_image_le
    _ = A.card * 2 ^ n := by rw [Finset.card_product, Finset.card_range]

end ExactOverlaps.Entropy
