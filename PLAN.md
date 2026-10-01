# Formalisation plan

Plan for the Lean formalisation of B. Bárány, I. Kolossváry and S. Troscheit, *On exponential
separation of analytic self-conformal sets on the real line* (`../analytic.tex`). Statement
numbers refer to the current compiled version: Definition 1.2 (`def:SESC`), Theorem 1.4
(`thm:ESCOpenDense`), Theorem 1.5 (`thm:main`), Proposition 1.8 (`prop:example`), Theorem 1.12
(`thm:SubConjugation`), Section 2 (dual IFS), Section 3 (proof of 1.5), Section 4 (proof of 1.4),
Section 5 (conjugation).

Status: every statement of the paper without an open issue (Section 3) is formalised, with no
`sorry` and only the axioms `propext`, `Classical.choice` and `Quot.sound`:

| Paper | Lean |
|---|---|
| ESC, Definition 1.2 (SESC and weak super-exponential condensation), exact overlaps | `IFS.ESC`, `IFS.SESC`, `IFS.not_sesc_iff`, `IFS.HasExactOverlaps` |
| Theorem 1.5 | `Challenge.audit_sesc_of_dualProj` (audited), `IFS.theorem_1_5` |
| Proposition 1.8 and the example of Section 1.2.2 | `Challenge.audit_example_criterion`, `Challenge.audit_example_sesc` (audited), `IFS.proposition_1_8`, `example_sesc` |
| Lemma 2.1 | `IFS.existsUnique_isDualAttractor` |
| Theorem 2.2 | `IFS.theorem_2_2` |
| Lemma 2.4 | `IFS.dualProj_mem_analyticSpace`, `IFS.exists_dualProj_holder`, `IFS.isDualAttractor_range` |
| Lemma 2.6 and (2.6) | `IFS.lemma_2_6`, `IFS.exists_dualProj_sub_le_d2` |
| Lemma 2.8, Corollary 2.9, Lemma 2.10 | `IFS.lemma_2_8`, `IFS.corollary_2_9`, `IFS.lemma_2_10` |
| Lemma 3.1 | `lemma_3_1` |
| Lemma 4.1 and (4.3) | `IFS.lemma_4_1`, `gaussian_bound` |
| Lemma 5.1, (5.1), (5.2) | `lemma_5_1`, `existsUnique_fixedPoint`, `hatH`, `koenigs` |

The manuscript now corrects the statements of Proposition 1.8, Theorem 2.3 and Lemma 5.1 and the
proofs affected by issues I6 and I8 to I14. Theorems 1.12 and 2.3 wait for decision D3, Theorem 1.4
and Proposition 4.2 for decision D1 and the fixes for issues I1 to I3, and Lemma 2.5 for issue I4.
Lemma 5.1 is proved through the linearising map (5.2), constructed as a uniform limit on `B_ε`, so
no primitive of `Ĥ_f` is needed. Lemma 2.7 is not needed
by the Lean route. The proof of Theorem 1.5 uses the condensation dichotomy
`IFS.condensation_dichotomy`, with a single case split on whether the prefix lengths `|a_k|` stay
bounded.

## 1. Proposed headline endpoints

Seven audited theorems, stated in `Challenge.lean` over Mathlib alone.

| Endpoint | Paper | Content |
|---|---|---|
| `audit_sesc_of_dualProj` | Thm 1.5 | Distinct dual projections of equal length imply SESC |
| `audit_example_criterion` | Prop 1.8 | The explicit criterion `α > 2βc/(1-c)` implies the hypothesis of 1.5 and SESC |
| `audit_example_sesc` | Prop 1.8, example | The system `x/8`, `x/8 + x²/32`, `x/16 + x²/32 + 29/32` lies in the class for some `ε > 0` and satisfies SESC |
| `audit_sesc_open_dense` | Thm 1.4 | SESC systems contain a `d₂`-open, `d₂`-dense subset (ambient class: decision D1) |
| `audit_conj_similarity` | Thm 1.12, first claim | Every system is conjugated to one with a similarity map |
| `audit_conj_iff` | Thm 1.12(a) | Conjugacy to a self-similar system iff all `H_i` agree on `[0,1]` |
| `audit_subconj_iff` | Thm 1.12(b) | Sub-conjugacy iff `H_{i^∞} ≡ H_{j^∞}` for distinct `i, j` of equal length |

The dual-IFS reformulations (Theorems 2.2, 2.3 and Lemma 2.1) are proved in the library and
recorded in the correspondence manifest, but are not audited endpoints: stating them in the
challenge would add the dual attractor to the challenge vocabulary without adding content.

### Challenge vocabulary (sketch, not compiled)

Maps are given by their holomorphic extension `F : ℂ → ℂ`; the real map is `x ↦ (F x).re`
(decision D2). Suprema over `[0,1]` are written as existentials over `x ∈ [0,1]` (decision D6).

```lean
abbrev I : Set ℝ := Set.Icc 0 1

/-- The open `δ`-neighbourhood `B_δ` of `I` in `ℂ`. -/
def nbhd (δ : ℝ) : Set ℂ := Metric.thickening δ ((↑) '' I)

/-- The class `S^ω_ε(I)`: conditions (A)–(C) for the holomorphic extension `F`. -/
structure InClass (ε : ℝ) (F : ℂ → ℂ) : Prop where
  holo : DifferentiableOn ℂ F (nbhd (2 * ε))
  real : ∀ x : ℝ, (x : ℂ) ∈ nbhd (2 * ε) → (F x).im = 0
  mapsTo_I : ∀ x ∈ I, (F x).re ∈ I
  mapsTo_nbhd : Set.MapsTo F (closure (nbhd ε)) (nbhd ε)
  deriv_ne_zero : ∀ z ∈ closure (nbhd ε), deriv F z ≠ 0
  deriv_lt_one : ∀ z ∈ closure (nbhd ε), ‖deriv F z‖ < 1

def realMap (F : ℂ → ℂ) (x : ℝ) : ℝ := (F x).re

/-- `f_w = f_{w₁} ∘ ⋯ ∘ f_{w_k}`. -/
def comp (Φ : Fin N → ℂ → ℂ) (w : List (Fin N)) : ℝ → ℝ :=
  w.foldr (fun i g => realMap (Φ i) ∘ g) id

def SESC (Φ : Fin N → ℂ → ℂ) : Prop :=
  ∃ c > 0, ∀ n (i j : Fin n → Fin N), i ≠ j →
    ∃ x ∈ I, c ^ n ≤ |comp Φ (List.ofFn i) x - comp Φ (List.ofFn j) x|

/-- `f''/f'` on the real line. -/
def nonlin (F : ℂ → ℂ) (x : ℝ) : ℝ := deriv (deriv (realMap F)) x / deriv (realMap F) x

/-- `H_w` for a finite word, (1.4): the `n`-th term evaluates `f_{w_{n+1}}''/f_{w_{n+1}}'` along
`f_{w_n} ∘ ⋯ ∘ f_{w_1}`, the composition of the first `n` letters in reverse order. -/
def dualProj (Φ : Fin N → ℂ → ℂ) (w : List (Fin N)) (x : ℝ) : ℝ :=
  ∑ n : Fin w.length, nonlin (Φ (w.get n)) (comp Φ (w.take n).reverse x) *
    deriv (comp Φ (w.take n).reverse) x

/-- `H_w` for an infinite word, (1.4). The series converges absolutely on `I`. -/
def dualProjInf (Φ : Fin N → ℂ → ℂ) (w : ℕ → Fin N) (x : ℝ) : ℝ :=
  ∑' n, nonlin (Φ (w n)) (comp Φ (List.ofFn fun k : Fin n => w k).reverse x) *
    deriv (comp Φ (List.ofFn fun k : Fin n => w k).reverse) x

/-- The `C²` distance `d₂` on `I`, maximised over the maps. -/
def d2 (Φ Ψ : Fin N → ℂ → ℂ) : ℝ :=
  ⨆ i, (⨆ x : I, |realMap (Φ i) x - realMap (Ψ i) x|)
    + (⨆ x : I, |deriv (realMap (Φ i)) x - deriv (realMap (Ψ i)) x|)
    + (⨆ x : I, |deriv (deriv (realMap (Φ i))) x - deriv (deriv (realMap (Ψ i))) x|)
```

### Endpoint statements (sketch)

```lean
theorem audit_sesc_of_dualProj (hε : 0 < ε) (Φ : Fin N → ℂ → ℂ) (hΦ : ∀ i, InClass ε (Φ i))
    (hfin : ∀ n (i j : Fin n → Fin N), i ≠ j →
      ∃ x ∈ I, dualProj Φ (List.ofFn i) x ≠ dualProj Φ (List.ofFn j) x)
    (hinf : ∀ i j : ℕ → Fin N, i ≠ j → ∃ x ∈ I, dualProjInf Φ i x ≠ dualProjInf Φ j x) :
    SESC Φ := sorry

-- β and c are any upper bounds for sup |f_i''/f_i'| and sup |f_i'| on I. This implies the paper's
-- version with the suprema, and needs only real bounds.
theorem audit_example_criterion (hε : 0 < ε) (Φ : Fin N → ℂ → ℂ) (hΦ : ∀ i, InClass ε (Φ i))
    {α β c : ℝ} (hα : 0 < α) (hsep : ∀ i j, i ≠ j → ∃ x ∈ I, α ≤ |nonlin (Φ i) x - nonlin (Φ j) x|)
    (hβ : ∀ i, ∀ x ∈ I, |nonlin (Φ i) x| ≤ β) (hc : ∀ i, ∀ x ∈ I, |deriv (realMap (Φ i)) x| ≤ c)
    (hc1 : c < 1) (hαβc : 2 * β * c / (1 - c) < α) :
    (∀ n (i j : Fin n → Fin N), i ≠ j →
      ∃ x ∈ I, dualProj Φ (List.ofFn i) x ≠ dualProj Φ (List.ofFn j) x) ∧
    (∀ i j : ℕ → Fin N, i ≠ j → ∃ x ∈ I, dualProjInf Φ i x ≠ dualProjInf Φ j x) ∧
    SESC Φ := sorry

def exampleIFS : Fin 3 → ℂ → ℂ :=
  ![fun z => z / 8, fun z => z / 8 + z ^ 2 / 32, fun z => z / 16 + z ^ 2 / 32 + 29 / 32]

theorem audit_example_sesc : ∃ ε > 0, (∀ i, InClass ε (exampleIFS i)) ∧ SESC exampleIFS := sorry

-- Ambient class `C` per decision D1: `InClass ε` for the fixed `ε`, or `∃ ε > 0, InClass ε`.
theorem audit_sesc_open_dense (N : ℕ) :
    ∃ U : Set (Fin N → ℂ → ℂ), (∀ Φ ∈ U, (∀ i, C (Φ i)) ∧ SESC Φ) ∧
      (∀ Φ ∈ U, ∃ r > 0, ∀ Ψ, (∀ i, C (Ψ i)) → d2 Φ Ψ < r → Ψ ∈ U) ∧
      (∀ Φ, (∀ i, C (Φ i)) → ∀ r > 0, ∃ Ψ ∈ U, d2 Φ Ψ < r) := sorry

/-- `g` is an analytic change of coordinates on `I` (decision D3). -/
def IsAnalyticCoord (g : ℝ → ℝ) : Prop := AnalyticOnNhd ℝ g I ∧ Set.InjOn g I

def ConjSelfSimilar (f : Fin M → ℝ → ℝ) : Prop :=
  ∃ g, IsAnalyticCoord g ∧ ∃ lam t : Fin M → ℝ, ∀ j,
    lam j ≠ 0 ∧ |lam j| < 1 ∧ ∀ x ∈ I, g (f j x) = lam j * g x + t j

/-- The attractor is not a singleton: two maps have distinct fixed points (remark after Thm 1.6). -/
def NonDegenerate (Φ : Fin N → ℂ → ℂ) : Prop :=
  ∃ i j, ∃ x ∈ I, ∃ y ∈ I, realMap (Φ i) x = x ∧ realMap (Φ j) y = y ∧ x ≠ y

theorem audit_conj_similarity (hε : 0 < ε) (Φ : Fin N → ℂ → ℂ) (hΦ : ∀ i, InClass ε (Φ i))
    (i : Fin N) : ∃ g, IsAnalyticCoord g ∧ ∃ lam t : ℝ, ∀ x ∈ I,
      g (realMap (Φ i) x) = lam * g x + t := sorry

theorem audit_conj_iff (hε : 0 < ε) (Φ : Fin N → ℂ → ℂ) (hΦ : ∀ i, InClass ε (Φ i))
    (hnd : NonDegenerate Φ) :
    ConjSelfSimilar (fun i => realMap (Φ i)) ↔
      ∀ i j : ℕ → Fin N, ∀ x ∈ I, dualProjInf Φ i x = dualProjInf Φ j x := sorry

theorem audit_subconj_iff (hε : 0 < ε) (Φ : Fin N → ℂ → ℂ) (hΦ : ∀ i, InClass ε (Φ i))
    (hnd : NonDegenerate Φ) :
    (∃ i j : List (Fin N), i ≠ j ∧ i.length = j.length ∧ ConjSelfSimilar ![comp Φ i, comp Φ j]) ↔
      ∃ i j : List (Fin N), i ≠ j ∧ i.length = j.length ∧ ∀ x ∈ I,
        dualProjInf Φ (fun n => i.get ⟨n % i.length, _⟩) x =
          dualProjInf Φ (fun n => j.get ⟨n % j.length, _⟩) x := sorry
```

## 2. Decisions for the authors

**D1. Ambient class of Theorem 1.4 (blocking for Phase 5).** As written, the density step does
not stay in `𝔖_N` for the fixed `ε` (issue I1). Options:
(a) state 1.4 for the class `⋃_{ε>0} 𝔖_N(ε)`, that is analytic systems with no fixed complex
neighbourhood; the paper's argument proves this after the fixes for I2 and I3;
(b) keep the fixed `ε` and find a new density argument;
(c) audit only the openness half for fixed `ε` until (b) is settled.
Recommendation: (a), and correct the paper accordingly. Theorems 1.5 and 1.12 do not depend on
`ε`, since their hypotheses and conclusions only involve `[0,1]`.

**D2. Encoding of maps.** Recommendation: the holomorphic extension `F : ℂ → ℂ` with
`DifferentiableOn ℂ F (B_{2ε})` and realness on the real segment, with real derivatives taken of
`x ↦ (F x).re`. The library bridges real and complex derivatives with
`HasDerivAt.real_of_complex`. The alternative, a real map with an existential holomorphic
extension, makes every statement carry the extension.

**D3. Conjugacy.** Definition 1.9 asks for an analytic, invertible `g`. If invertibility only
means injectivity, `g'` may vanish and the step `|g'(p_i)| > 0` in the proof of 1.12(a) needs an
argument (issue I5). Recommendation: keep the paper's notion (analytic and injective on `I`) in
the challenge and prove in the library that `g' ≠ 0` on `I` when the attractor is not a
singleton. Fallback: require `g' ≠ 0` (analytic diffeomorphism), which removes that lemma.

**D4. Headline scope.** The seven endpoints of Section 1. Adding Theorems 2.2 and 2.3 as
endpoints is possible but brings the dual attractor into the challenge.

**D5. Corollary 1.7 and Rapaport's theorem.** Recommendation: out of scope. A conditional
version with Theorem 1.6 as a named, cited literature axiom would need Hausdorff dimension of
measures, self-conformal measures, pressure and Lyapunov exponents in the challenge vocabulary.

**D6. Suprema.** Recommendation: write `sup_{x∈[0,1]} |u(x)| > 0` as `∃ x ∈ I, u x ≠ 0`, and
`sup ≥ c^n` as `∃ x ∈ I, c^n ≤ |u x|`. These are equivalent for continuous `u` (for SESC up to
the choice of `c`), and avoid junk values of `⨆` on unbounded families. `d₂` keeps `⨆`, which is
bounded on the class.

**D7. Packaging.** Library name `AnalyticESC`, licence Apache-2.0 and a public GitHub repository
for the `lean/` directory, as for JA-ST. All three need the co-authors' agreement.

## 3. Issues found in the paper while planning

Ordered by severity. Each affects either a statement or the route of the Lean proof.

**I1. Proposition 4.2: the perturbation leaves the class.** The proposition asserts that, after
shrinking the `η_i`, `g = f·exp(φψA)` satisfies (B) and (C) on `cl B_ε`. Off the real axis,
`|exp(-(z-y_i)²/η_i)| = exp(((Im z)² - (Re z - y_i)²)/η_i)`, which near `z = y_i + iε` grows like
`exp(ε²/η_i)`; shrinking `η_i` makes `g` larger on `cl B_ε`. A numerical check with
`f(z) = z/2 + 1/4`, `Y = {1/2}`, `δ = 0.01`, `ε = 0.1` gives `max Re(φψA)` on `Im z = ε` of about
`0.9` at `η = 10⁻³` and about `10³⁹` at `η = 10⁻⁴`, so `|g|` is astronomically large and
`g(cl B_ε) ⊄ B_ε`. The real-line estimates are unaffected. Consequence: the density half of
Theorem 1.4 is not established for fixed `ε`. It does hold for the union class (D1(a)), where
only conditions on `[0,1]` and analyticity on some neighbourhood are required.

**I2. Proposition 4.2 assumes `f([0,1]) ⊂ (0,1)`.** The proof divides by `f(y_i)` and states the
constant `C` depends only on `f`; the class only gives `f(I) ⊆ I`, and the paper's own example has
`f_1(0) = 0` and `f_3(1) = 1`. Then `a_i` is undefined at zeros of `f`, `C` is not uniform as
points approach a zero, and `g(I) ⊆ I` can fail (for `f(1) = 1`, `g(1) > 1`). Fix: first
replace `f_i` by `(1-t)f_i + t/2`, which stays in `𝔖_N(ε)` for fixed `ε` (as `B_ε` is convex),
is `d₂`-close, and maps `I` into `(0,1)`.

**I3. "We may assume that Φ has no exact overlaps."** No argument is given for removing exact
overlaps by a small perturbation. Lemma 4.1 only needs `f_u ≢ f_v` on `[0,1]` for the finitely
many distinct compositions of length at most `n`, so a lemma removing finitely many coincidences
suffices. It still needs a written proof (for example, generic parameters in the family
`(1-t)f_i + t c_i`).

**I4. Lemma 2.5(d) and the proof of Theorem 2.2.** For a finite word, `H_i = F_i(0)` and `0` is
not in `Λ*` in general, so (a) ⇒ (d) is not a consequence of the strong separation of `Λ*` for
short words; the proof is left to the reader. Theorem 2.2 is deduced from 2.5 and 1.5, which
needs `H_a ≢ H_b` for distinct finite words of equal length. The Lean route avoids (d): the
condensation dichotomy of Section 5 yields either infinite words with equal `H` or an exact
coincidence `f_a ≡ f_b`, and both contradict the separation of the dual.

**I5. Theorem 1.12(a), forward direction.** The proof uses `|g'(p_i)| > 0`. For a merely
injective analytic `g` this can fail: `g(x) = x³` conjugates `x/2` to `y/8` on `[0,1]`, with
`f'(p) = 1/2 ≠ 1/8 = λ`. The identity `f'_i(p_i) = λ_i` then fails. With a non-singleton attractor
one can show `g' ≠ 0`: the zero set of `g'` in `I` is finite and invariant under every `f_i`,
hence contains the attractor. See also D3.

**I6. Lemma 5.1 needs `b ≠ 0`.** *Resolved in the manuscript.* For `b = 0` the solution of `g'' = Ĥ_f g'` with `g'(p) = 0` is
constant, so not invertible.

**I7. Theorem 1.12(b) via (a).** Part (a) is applied to the sub-system `(f_i, f_j)`, whose
attractor can be a singleton (in the example, `(f_1, f_2)` has the common fixed point `0`), while
the proof of (a) uses a non-singleton attractor. The Lean route for (a) does not need it: if
`g ∘ f_i = λ_i g + t_i` with `g' ≠ 0`, then `G = g''/g'` satisfies `G = f_i'·G∘f_i + f_i''/f_i'`,
so `G` is the common fixed point of the dual operators on bounded functions on `[0,1]`, hence
`H_w = G` for every infinite word `w`.

**I8. Proposition 1.8: `β > 0` needs `N ≥ 2`.** *Resolved in the manuscript.* For `N = 1` the hypothesis is vacuous and
`f(x) = x/2` gives `β = 0`. The conclusion about `H` does not use `β > 0`.

**I9. Theorem 2.3, second part.** *Resolved in the manuscript.* The words `i, j` must be distinct.

**I10. "SSC ⇒ SESC ⇒ ESC ⇒ no exact overlaps."** *Resolved in the manuscript.* The last implication needs a non-singleton
attractor. The sub-system `(x/8, x/8 + x²/32)` satisfies SESC by Proposition 1.8, while
`f_1 = f_2` on its attractor `{0}`.

**I11. Proof of Theorem 1.5: bounded subsequence.** *Resolved in the manuscript.* If `sup|f_i - f_j| = 0` at a fixed level,
the subsequence `n_ℓ` is bounded. This case gives `f_i ≡ f_j`, hence `H` coincides for the reversed
words, and is handled separately.

**I12. Lemma 2.10's hypothesis** *Resolved in the manuscript.* `|i ∧ j| < min{|i|,|j|}` excludes the prefix case used in the proof
of Theorem 1.5 (`i^{(n_ℓ)}` a prefix of `i*`). The bound holds in that case as well; the Lean
lemma covers both.

**I13. Proof of Lemma 2.6: constants of the perturbed system.** *Resolved in the manuscript.* For `Ψ` close to `Φ`, the proof
asserts `c_min ≤ |g_i'| ≤ c_max` on `[0,1]`. A small perturbation can push `|g_i'|` beyond these
bounds. The argument goes through with `c_min/2 ≤ |g_i'| ≤ c_max + δ₀ < 1`, which is what the Lean
proof uses.

**I14. Lemma 2.7 uses `g_0`.** *Resolved in the manuscript.* Blocks of size one give the factor `g_{|B|-1} = g_0`, which is not
defined (the recursion starts at `g_1`); the intended value is `g_0 = 1`. In (2.11), `E_k` should be
the supremum of `|g_k|`.

**Minor.** *Resolved in the manuscript.* In the proof of Theorem 1.4 the last bullet should place non-base orbit points in
`Z_ℓ` for every map `ℓ`. Lemma 2.4 states the bound with `K` and proves it with `2K`.
`𝔖_N` is not complete for `d₂` (for instance `(1-1/n)x + 1/(2n)` has no limit in the class),
so "Polish, i.e. complete" needs rewording; the claim is not used.

## 4. Proof routes in Lean that differ from the paper

1. **Derivative bounds by Cauchy estimates.** `H_w` is holomorphic on `B_ε` with a uniform bound
   `M` over all words, and `|H_w - H_v| ≤ 2M c_max^{|w∧v|}` on `B_ε`. Discs of radius `ε` about
   points of `I` lie in `B_ε`, so `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`
   gives Lemmas 2.8 and 2.10 directly, and Corollary 2.9 by the mean value theorem. The
   Faà di Bruno formula (Lemma 2.7) is not needed.
2. **Condensation dichotomy.** One lemma: if SESC fails, then either there are infinite words
   `i* ≠ j*` with different first letters and `H_{i*} ≡ H_{j*}` on `I`, or there are finite words
   `a ≠ b` of equal length with different last letters and `f_a ≡ f_b` on `I`. Theorem 1.5,
   Proposition 1.8 and Theorem 2.2 all follow from it (see I4, I11).
3. **Dual attractor through the coding map.** `Λ* = {H_w : w ∈ Σ}` is shown to be the unique
   nonempty compact invariant set directly, without Hutchinson's theorem on compact sets.
4. **Conjugation through a common fixed point.** For (a) ⇐, take `g = ∫ exp ∫ H` with `g' ≠ 0`;
   `G = g''/g' = H` is fixed by every dual operator, so `(log|g' ∘ f_i| + log|f_i'| - log|g'|)' = 0`
   and `g ∘ f_i = λ_i g + t_i`. For (a) ⇒, see I7. The limit formula (5.2) is not needed.
5. **Finite and infinite words together.** Internally, a word in `Σ ∪ Σ_*` is a sequence in
   `Option (Fin N)` that stays `none` once it is `none`. This is a closed subset of a compact
   space, so limits of words of equal length have equal length, as used in Section 3.

## 5. Library architecture

Namespace `AnalyticESC`. Paper labels in brackets.

| Phase | Module | Content |
|---|---|---|
| 1 | `Words` | Finite and infinite words, prefixes, `∧`, reversal, `i^∞`, compactness of `Σ ∪ Σ_*`, subsequences |
| 1 | `Neighbourhood` | `B_δ`, convexity, closure, discs in `B_ε`, `F(I) ⊆ I` and `‖F'‖ < 1` give `F(cl B_ε) ⊆ B_ε` |
| 1 | `Class` | The class `S^ω_ε` [§1.1], real restriction, real versus complex derivatives, constants `c_min`, `c_max`, monotonicity in `ε` |
| 1 | `Composition` | `f_w` for complex and real maps, chain rule, `c_min^n ≤ |f_w'| ≤ c_max^n`, natural projection, attractor, fixed points of `f_w`, singleton criterion |
| 1 | `Separation` | ESC, SESC [def:SESC], exact overlaps, the implications of §1.1 |
| 2 | `Dual.Operator` | Dual operators [(2.1)], contraction, composition reverses the word |
| 2 | `Dual.Projection` | `H_w` [(1.4)], recursion, cocycle, `H_{rev w} = f_w''/f_w'` [(2.7)], periodic words |
| 2 | `Dual.Holomorphic` | Holomorphy, uniform bounds, Hölder dependence on `w` [thm:H_iAnalytic] |
| 2 | `Dual.Derivatives` | [thm:kbound], [thm:difcor], [thm:difbound] by Cauchy estimates |
| 2 | `Analysis.Interpolation` | [thm:analyticity] and its iterate with exponent `2^{-k}` |
| 2 | `Analysis.Identity` | Identity theorem on `I`: equality on a subinterval, or of all derivatives at a point |
| 3 | `Main.Dichotomy` | The condensation dichotomy |
| 3 | `Main.Sufficient` | [thm:main] |
| 3 | `Main.Example` | [prop:example] and the three-map example |
| 4 | `Dual.Attractor` | `Λ*` [lem:ExistanceAttractor], dual SSC, [lem:SSCEequiv] (a)–(c), [thm:DualSSC] |
| 5 | `Generic.Metric` | `d₂`, [(2.3)–(2.6)], [lem:cont] |
| 5 | `Generic.Points` | [lem:Pointsx_ij] with the coincidence-removal lemma (I3) |
| 5 | `Generic.Bump` | [(4.3)], [prop:AnalyticBumpFunc] on the real line |
| 5 | `Generic.Perturbation` | Interior perturbation (I2), coincidence removal (I3) |
| 5 | `Generic.OpenDense` | [thm:ESCOpenDense] in the class fixed by D1 |
| 6 | `Conjugation.Linearisation` | `Ĥ_f`, the coordinate `g` [lem:conj0], `g ∘ f = λ g + t` |
| 6 | `Conjugation.Characterisation` | [thm:SubConjugation], [thm:DualConj], the remark on single letters |

Dependencies: Phase 1 → Phase 2 → Phase 3 → Phases 4 and 5; Phase 6 needs only Phases 1 and 2
and can run in parallel with Phases 3 to 5. The two `Analysis` modules are independent of
everything else.

### Mathlib entry points (checked in the shared Mathlib at `v4.35.0-rc2`)

- Cauchy estimates: `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`,
  `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`.
- Holomorphic limits: `TendstoLocallyUniformlyOn.differentiableOn`.
- Analyticity: `DifferentiableOn.analyticOnNhd`, `AnalyticOnNhd.restrictScalars`,
  `AnalyticOnNhd.deriv`, `Complex.taylorSeries_eq_on_ball'`.
- Identity theorem: `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`,
  `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.
- Real and complex derivatives: `HasDerivAt.real_of_complex`, `ContDiffAt.real_of_complex`.
- Primitives: `DifferentiableOn.isExactOn_ball`, `intervalIntegral.integral_hasDerivAt_right`.
- Neighbourhoods: `Convex.thickening`, `closure_thickening`.
- Taylor: `taylor_mean_remainder_lagrange`. Fixed points: `ContractingWith.fixedPoint_unique`.
- Compactness: `IsCompact.tendsto_subseq`.

### Reuse from other projects

All of the following are on the same toolchain (`v4.35.0-rc2`) but use plain `import`; copied
code gets a `module` header and `public import`, with the source recorded in the module
docstring. Copying is preferred to a lake `require`, which would tie CI and Palomar to
unpublished sibling repositories.

- `SoleAuthor/AnalyticIFS/lean` (closest match; real-analytic maps only):
  `PeriodicDual.lean` (`dualSeries_fixedPoint`, `dual_fixedPoint_unique`, `dualSeries_tail_bound`,
  `periodicDual_*`) for `H_{i^∞}` and the dual fixed points; `AffineDual.lean` (`dualAffine`,
  `dualAffine_composition`, `second_deriv_composition`) for `Dual.Operator`; `Cylinders.lean`
  (`listMap`, `cylinder_uniform_derivative_bounds`) and `ExactOverlaps.lean`
  (`deriv_eqOn_interval`, `periodicDual_eqOn_of_wordMap_eqOn`) for `Composition`.
- `LeanLibraries/GeometricMeasureTheory`: `wordComp` and `wordComp_append`
  (`QuasiSelfSimilar/Basic.lean`), the chain rule along words in `CookieCutter/Basic.lean`.
- `LeanLibraries/FractalGeometry`: the coding map and attractor API (`code`, `code_cons`,
  `continuous_code`, `attractorSet`, `eq_attractorSet`) as a template for `Composition`.
- `ML-ST/lean`: `exists_first_diff`, `prefixWord`; `SoleAuthor/BrownianImages/lean`:
  prefix and incomparability lemmas in `Schief.lean`.
- `DA-AK-ST/lean`: `ProjExpSeparation` in `BoxLike/Separation.lean` as a template for ESC.
- TauCeti offers little here (no IFS or attractor material; Mathlib already has `k`-th Cauchy
  estimates) and is on toolchain `v4.34.0-rc2`, so it is not a dependency.
- Tooling worth adopting later: the `collectAxioms` loop of `SoleAuthor/AffineBoxDimension`
  (`ProofAudit.lean`) and the byte-identical vocabulary check `check_identical.py` of
  `IK-ST/AffineAssouadDim`.

## 6. Order of work

| Phase | Goal | Size | Gate |
|---|---|---|---|
| 0 | Decide D1–D7, write `Challenge.lean` and its copy in `Solution`, list endpoints in `comparator.json` | S | Author approval of the statements |
| 1 | Foundations | M | |
| 2 | Dual projection, regularity, analysis lemmas | L | |
| 3 | Theorem 1.5, Proposition 1.8, example | L | Phases 1–2 |
| 4 | Dual attractor and Theorem 2.2 | M | Phase 3 |
| 5 | Theorem 1.4 | XL | D1, written fixes for I1–I3 |
| 6 | Theorem 1.12, Theorem 2.3 | M | Phases 1–2, D3 |

Sizes: S below 300 lines, M up to 1000, L up to 3000, XL beyond. Phase 5 is the largest and
riskiest; the real-line estimates of Proposition 4.2 alone are long. Within a phase, modules can
be assigned to separate agents once their interfaces (definitions and statements) are fixed.

The first milestone is Phases 0 to 3 with three audited endpoints (`audit_sesc_of_dualProj`,
`audit_example_criterion`, `audit_example_sesc`). The second adds Phase 6 (three more). The
third is Theorem 1.4.

## 7. Workflow

- Challenge and solution follow `AGENTS.md`: minimal Mathlib-only vocabulary in the challenge,
  the same definitions repeated in `Solution`, a `Solution` bridge from the library to that
  vocabulary, endpoints listed individually in `comparator.json`, and only `propext`,
  `Classical.choice` and `Quot.sound` permitted.
- When an endpoint is proved, add its name to `comparator.json`, an alignment entry to
  `formalization.yaml`, and set the manifest entry to `formalized` with the declaration names.
- Run `python3 scripts/check_module_headers.py` and `python3 scripts/check_paper_correspondence.py`
  before committing. CI builds the library and runs the comparator once endpoints exist.
- If the paper gains a Lean appendix, set `appendix_file` in `paper-correspondence.yaml` to have
  the checker verify it.
- Deviations from the paper's statements and proofs go into the manifest notes and
  `fidelity.divergences`, never silently into the statements.
