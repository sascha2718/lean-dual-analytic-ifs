module

public import AnalyticESC.Literature.SelfConformal.FengHu.Branch
public import AnalyticESC.Literature.ExactOverlaps.SelfSimilar.BallLocalDimension

@[expose] public section

/-!
# Radii along the coding and the one-step information inequalities

For the proof of exact dimensionality in D.-J. Feng and H. Hu, *Dimension theory of iterated
function systems*, Comm. Pure Appl. Math. 62 (2009), Theorem 2.8, for a conformal system on the
line, the information `-log μ(B(Π ω, r))` is compared along three sequences of radii:

* `radD n ω = |φ_{ω|_n}'(Π σ^n ω)| = ∏_{j<n} |φ_{ω_j}'(Π σ^{j+1} ω)|`;
* `radLo`, `radHi`: perturbations of `radD` by the distortion factors `e^{∓L ρ}`, chosen so that
  `φ_{ω_0}` maps the ball `B(Π σ ω, radLo n (σ ω)) ∩ I` onto a set containing
  `B(Π ω, radLo (n+1) ω) ∩ φ_{ω_0}(I)`, and maps `B(Π σ ω, radHi n (σ ω)) ∩ I` into
  `B(Π ω, radHi (n+1) ω)`.

The distortion factors multiply to at most `e^{L/(1-c)}`, so all three radii are comparable.
The one-step inequalities `info_step_ge`, `info_step_le` turn the ball inclusions into
inequalities between ball informations, with the branch ratio `μ_{ω_0}(B)/μ(B)` as increment.

## Main declarations

* `dfac`, `radD`, `radLo`, `radHi` and their bounds `radLo_le_radD`, `radD_le_radHi`,
  `exp_mul_radD_le_radLo`, `radHi_le_exp_mul_radD`, `radD_add_le`.
* `kQ_closedBall_radLo_le`, `le_kQ_closedBall_radHi`: the one-step ball inclusions.
* `info_step_ge`, `info_step_le`: the one-step information inequalities.

Copied from the library `FractalGeometry` (module `FractalGeometry.SelfConformal.FengHu.Radii`) and adapted to the module
system: `public import`, `@[expose] public section` and the module names of the imports.
-/

namespace FractalGeometry.SelfConformal.FengHu

open MeasureTheory Set Filter Topology Metric
open AnalyticESC (I realComp IsProbVec)
open FractalGeometry.SelfSimilar.FengHu (ratioInfo densityInfo)

variable {N : ℕ} {φ : Fin N → ℝ → ℝ} {c L : ℝ} {p : Fin N → ℝ}

/-- The one-step derivative factor `|φ_{ω_0}'(Π σ ω)|`. -/
noncomputable def dfac (φ : Fin N → ℝ → ℝ) (ω : ℕ → Fin N) : ℝ :=
  |deriv (φ (ω 0)) (coding φ (shift ω))|

/-- `radD n ω = ∏_{j<n} |φ_{ω_j}'(Π σ^{j+1} ω)|`. -/
noncomputable def radD (φ : Fin N → ℝ → ℝ) : ℕ → (ℕ → Fin N) → ℝ
  | 0, _ => 1
  | n + 1, ω => dfac φ ω * radD φ n (shift ω)

/-- The lower radii `radLo (n+1) ω = |φ_{ω_0}'(Π σ ω)| e^{-L ρ} ρ` with `ρ = radLo n (σ ω)`. -/
noncomputable def radLo (φ : Fin N → ℝ → ℝ) (L : ℝ) : ℕ → (ℕ → Fin N) → ℝ
  | 0, _ => 1
  | n + 1, ω => dfac φ ω * Real.exp (-(L * radLo φ L n (shift ω))) * radLo φ L n (shift ω)

/-- The upper radii `radHi (n+1) ω = min(c, |φ_{ω_0}'(Π σ ω)| e^{L ρ}) ρ` with
`ρ = radHi n (σ ω)`. -/
noncomputable def radHi (φ : Fin N → ℝ → ℝ) (c L : ℝ) : ℕ → (ℕ → Fin N) → ℝ
  | 0, _ => 1
  | n + 1, ω =>
      min c (dfac φ ω * Real.exp (L * radHi φ c L n (shift ω))) * radHi φ c L n (shift ω)

/-- The derivative factor is measurable. -/
theorem measurable_dfac (φ : Fin N → ℝ → ℝ) : Measurable (dfac φ) :=
  FractalGeometry.SelfSimilar.FengHu.measurable_of_index (measurable_pi_apply 0)
    ((measurable_coding φ).comp measurable_shift)
    (G := fun a y => |deriv (φ a) y|) fun a => (measurable_deriv (φ a)).abs

/-- `radD n` is measurable. -/
theorem measurable_radD (φ : Fin N → ℝ → ℝ) : ∀ n, Measurable (radD φ n)
  | 0 => measurable_const
  | n + 1 => (measurable_dfac φ).mul ((measurable_radD φ n).comp measurable_shift)

/-- `radLo n` is measurable. -/
theorem measurable_radLo (φ : Fin N → ℝ → ℝ) (L : ℝ) : ∀ n, Measurable (radLo φ L n)
  | 0 => measurable_const
  | n + 1 => by
    have h := (measurable_radLo φ L n).comp measurable_shift
    exact ((measurable_dfac φ).mul (measurable_const.mul h).neg.exp).mul h

/-- `radHi n` is measurable. -/
theorem measurable_radHi (φ : Fin N → ℝ → ℝ) (c L : ℝ) : ∀ n, Measurable (radHi φ c L n)
  | 0 => measurable_const
  | n + 1 => by
    have h := (measurable_radHi φ c L n).comp measurable_shift
    exact (measurable_const.min ((measurable_dfac φ).mul (measurable_const.mul h).exp)).mul h

/-- The geometric sums `S n = ∑_{k<n} c^k`. -/
noncomputable def geomS (c : ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, c ^ k

namespace ConformalIFS

variable (hφ : ConformalIFS φ c L)
include hφ

/-- The derivative factor is positive. -/
theorem dfac_pos (ω : ℕ → Fin N) : 0 < dfac φ ω :=
  hφ.abs_deriv_pos _ (hφ.coding_mem _)

/-- The derivative factor is at most `c`. -/
theorem dfac_le (ω : ℕ → Fin N) : dfac φ ω ≤ c :=
  hφ.abs_deriv_le _ _ (hφ.coding_mem _)

/-- The contraction bound is positive for a nonempty alphabet. -/
theorem c_pos [NeZero N] : 0 < c :=
  (hφ.abs_deriv_pos 0 zero_mem_I).trans_le (hφ.abs_deriv_le 0 0 zero_mem_I)

/-- `∑_{k<n} c^k ≤ 1 / (1 - c)`. -/
theorem geomS_le (n : ℕ) : geomS c n ≤ 1 / (1 - c) := by
  have h1 : 0 < 1 - c := by linarith [hφ.c_lt_one]
  rw [le_div_iff₀ h1, mul_comm, geomS, mul_neg_geom_sum]
  linarith [pow_nonneg hφ.c_nonneg n]

omit hφ in
/-- `S_{n+1} = c^n + S_n`. -/
theorem geomS_succ (n : ℕ) : geomS c (n + 1) = c ^ n + geomS c n := by
  rw [geomS, Finset.sum_range_succ, geomS, add_comm]

/-- `radD n ω > 0`. -/
theorem radD_pos : ∀ n ω, 0 < radD φ n ω
  | 0, _ => one_pos
  | n + 1, ω => mul_pos (hφ.dfac_pos ω) (radD_pos n _)

/-- `radD n ω ≤ c^n`. -/
theorem radD_le_pow : ∀ n ω, radD φ n ω ≤ c ^ n
  | 0, _ => le_rfl
  | n + 1, ω => by
    rw [radD, pow_succ, mul_comm (c ^ n)]
    exact mul_le_mul (hφ.dfac_le ω) (radD_le_pow n _) (hφ.radD_pos n _).le hφ.c_nonneg

/-- `radD (n+1) ω ≤ radD n ω`. -/
theorem radD_succ_le : ∀ n ω, radD φ (n + 1) ω ≤ radD φ n ω
  | 0, ω => by
    show dfac φ ω * 1 ≤ 1
    rw [mul_one]
    exact (hφ.dfac_le ω).trans hφ.c_lt_one.le
  | n + 1, ω => by
    show dfac φ ω * radD φ (n + 1) (shift ω) ≤ dfac φ ω * radD φ n (shift ω)
    exact mul_le_mul_of_nonneg_left (radD_succ_le n _) (hφ.dfac_pos ω).le

/-- `n ↦ radD n ω` is antitone. -/
theorem radD_antitone (ω : ℕ → Fin N) : Antitone fun n => radD φ n ω :=
  antitone_nat_of_succ_le fun n => hφ.radD_succ_le n ω

/-- `radD (n + k) ω ≤ c^k radD n ω`. -/
theorem radD_add_le (k : ℕ) : ∀ n ω, radD φ (n + k) ω ≤ c ^ k * radD φ n ω
  | 0, ω => by simpa [radD] using hφ.radD_le_pow k ω
  | n + 1, ω => by
    rw [show n + 1 + k = (n + k) + 1 by omega, radD, radD]
    calc dfac φ ω * radD φ (n + k) (shift ω) ≤ dfac φ ω * (c ^ k * radD φ n (shift ω)) :=
          mul_le_mul_of_nonneg_left (radD_add_le k n _) (hφ.dfac_pos ω).le
      _ = c ^ k * (dfac φ ω * radD φ n (shift ω)) := by ring

/-- `radLo n ω > 0`. -/
theorem radLo_pos : ∀ n ω, 0 < radLo φ L n ω
  | 0, _ => one_pos
  | n + 1, ω => mul_pos (mul_pos (hφ.dfac_pos ω) (Real.exp_pos _)) (radLo_pos n _)

/-- `radLo n ω ≤ radD n ω`. -/
theorem radLo_le_radD : ∀ n ω, radLo φ L n ω ≤ radD φ n ω
  | 0, _ => le_rfl
  | n + 1, ω => by
    rw [radLo, radD]
    have h1 : Real.exp (-(L * radLo φ L n (shift ω))) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hφ.L_nonneg (hφ.radLo_pos n _).le))
    calc dfac φ ω * Real.exp (-(L * radLo φ L n (shift ω))) * radLo φ L n (shift ω)
        ≤ dfac φ ω * 1 * radD φ n (shift ω) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (hφ.dfac_pos ω).le) (radLo_le_radD n _)
            (hφ.radLo_pos n _).le (by linarith [hφ.dfac_pos ω])
      _ = dfac φ ω * radD φ n (shift ω) := by ring

/-- `radLo n ω ≤ c^n`. -/
theorem radLo_le_pow (n : ℕ) (ω : ℕ → Fin N) : radLo φ L n ω ≤ c ^ n :=
  (hφ.radLo_le_radD n ω).trans (hφ.radD_le_pow n ω)

/-- `e^{-L S_n} radD n ω ≤ radLo n ω`. -/
theorem exp_mul_radD_le_radLo : ∀ n ω,
    Real.exp (-(L * geomS c n)) * radD φ n ω ≤ radLo φ L n ω
  | 0, _ => by simp [radD, radLo, geomS]
  | n + 1, ω => by
    rw [radLo, radD, geomS_succ]
    have h1 : Real.exp (-(L * c ^ n)) ≤ Real.exp (-(L * radLo φ L n (shift ω))) :=
      Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left (hφ.radLo_le_pow n _)
        hφ.L_nonneg))
    have h2 := exp_mul_radD_le_radLo n (shift ω)
    have hd := (hφ.dfac_pos ω).le
    calc Real.exp (-(L * (c ^ n + geomS c n))) * (dfac φ ω * radD φ n (shift ω))
        = dfac φ ω * Real.exp (-(L * c ^ n)) *
            (Real.exp (-(L * geomS c n)) * radD φ n (shift ω)) := by
          rw [mul_add, neg_add, Real.exp_add]
          ring
      _ ≤ dfac φ ω * Real.exp (-(L * radLo φ L n (shift ω))) * radLo φ L n (shift ω) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hd) h2
            (mul_pos (Real.exp_pos _) (hφ.radD_pos n _)).le (by positivity)

/-- `radD n ω ≤ radHi n ω`. -/
theorem radD_le_radHi : ∀ n ω, radD φ n ω ≤ radHi φ c L n ω
  | 0, _ => le_rfl
  | n + 1, ω => by
    rw [radHi, radD]
    have hD := radD_le_radHi n (shift ω)
    have h1 : dfac φ ω ≤ min c (dfac φ ω * Real.exp (L * radHi φ c L n (shift ω))) := by
      refine le_min (hφ.dfac_le ω) ?_
      have : 1 ≤ Real.exp (L * radHi φ c L n (shift ω)) :=
        Real.one_le_exp (mul_nonneg hφ.L_nonneg ((hφ.radD_pos n _).le.trans hD))
      nlinarith [hφ.dfac_pos ω]
    exact mul_le_mul h1 hD (hφ.radD_pos n _).le ((hφ.dfac_pos ω).le.trans h1)

/-- `radHi n ω > 0`. -/
theorem radHi_pos (n : ℕ) (ω : ℕ → Fin N) : 0 < radHi φ c L n ω :=
  (hφ.radD_pos n ω).trans_le (hφ.radD_le_radHi n ω)

/-- `radHi n ω ≤ c^n`. -/
theorem radHi_le_pow : ∀ n ω, radHi φ c L n ω ≤ c ^ n
  | 0, _ => le_rfl
  | n + 1, ω => by
    rw [radHi, pow_succ, mul_comm (c ^ n)]
    exact mul_le_mul (min_le_left _ _) (radHi_le_pow n _) (hφ.radHi_pos n _).le hφ.c_nonneg

/-- `radHi n ω ≤ e^{L S_n} radD n ω`. -/
theorem radHi_le_exp_mul_radD : ∀ n ω,
    radHi φ c L n ω ≤ Real.exp (L * geomS c n) * radD φ n ω
  | 0, _ => by simp [radD, radHi, geomS]
  | n + 1, ω => by
    rw [radHi, radD, geomS_succ]
    have h1 : Real.exp (L * radHi φ c L n (shift ω)) ≤ Real.exp (L * c ^ n) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hφ.radHi_le_pow n _) hφ.L_nonneg)
    have h2 := radHi_le_exp_mul_radD n (shift ω)
    have hd := (hφ.dfac_pos ω).le
    calc min c (dfac φ ω * Real.exp (L * radHi φ c L n (shift ω))) * radHi φ c L n (shift ω)
        ≤ (dfac φ ω * Real.exp (L * c ^ n)) *
            (Real.exp (L * geomS c n) * radD φ n (shift ω)) := by
          apply mul_le_mul ((min_le_right _ _).trans (by gcongr)) h2 (hφ.radHi_pos n _).le
          positivity
      _ = Real.exp (L * (c ^ n + geomS c n)) * (dfac φ ω * radD φ n (shift ω)) := by
          rw [mul_add, Real.exp_add]
          ring

end ConformalIFS

/-! ### One-step ball inclusions -/

namespace ConformalIFS

variable (hφ : ConformalIFS φ c L)
include hφ

/-- The lower one-step inclusion:
`μ_{ω_0}(B(Π ω, radLo (n+1) ω)) ≤ p_{ω_0} μ(B(Π σ ω, radLo n (σ ω)))`. -/
theorem kQ_closedBall_radLo_le (hp : IsProbVec p) (n : ℕ) (ω : ℕ → Fin N) :
    kQ φ p hp (ω 0) (closedBall (coding φ ω) (radLo φ L (n + 1) ω)) ≤
      ENNReal.ofReal (p (ω 0)) *
        selfConformal φ p hp (closedBall (coding φ (shift ω)) (radLo φ L n (shift ω))) := by
  set a := ω 0
  set y := coding φ (shift ω)
  set ρ' := radLo φ L n (shift ω)
  have hy : y ∈ I := hφ.coding_mem _
  have hρ' : 0 < ρ' := hφ.radLo_pos n _
  rw [kQ_apply hφ hp a measurableSet_closedBall,
    selfConformal_apply φ hp measurableSet_closedBall]
  gcongr
  intro η hη
  simp only [mem_ofPred_eq, mem_closedBall, Real.dist_eq] at hη
  simp only [mem_preimage, mem_closedBall, Real.dist_eq]
  have hx : coding φ ω = φ a y := hφ.coding_eq ω
  rw [hx] at hη
  refine hφ.abs_sub_le_of_abs_map_sub_le a hy (hφ.coding_mem η) hρ'
    (t := radLo φ L (n + 1) ω) (fun w hw hwy => ?_) ?_
  · have h1 := hφ.mul_exp_le_abs_deriv a hw hy
    have h2 : Real.exp (-(L * ρ')) ≤ Real.exp (-(L * |w - y|)) :=
      Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hwy hφ.L_nonneg))
    have h3 : |deriv (φ a) y| * Real.exp (-(L * ρ')) ≤ |deriv (φ a) w| :=
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)).trans h1
    calc radLo φ L (n + 1) ω = |deriv (φ a) y| * Real.exp (-(L * ρ')) * ρ' := rfl
      _ ≤ |deriv (φ a) w| * ρ' := by gcongr
  · exact hη

/-- The upper one-step inclusion:
`p_{ω_0} μ(B(Π σ ω, radHi n (σ ω))) ≤ μ_{ω_0}(B(Π ω, radHi (n+1) ω))`. -/
theorem le_kQ_closedBall_radHi (hp : IsProbVec p) (n : ℕ) (ω : ℕ → Fin N) :
    ENNReal.ofReal (p (ω 0)) *
        selfConformal φ p hp (closedBall (coding φ (shift ω)) (radHi φ c L n (shift ω))) ≤
      kQ φ p hp (ω 0) (closedBall (coding φ ω) (radHi φ c L (n + 1) ω)) := by
  set a := ω 0
  set y := coding φ (shift ω)
  set ρ' := radHi φ c L n (shift ω)
  have hy : y ∈ I := hφ.coding_mem _
  rw [kQ_apply hφ hp a measurableSet_closedBall,
    selfConformal_apply φ hp measurableSet_closedBall]
  gcongr
  intro η hη
  simp only [mem_preimage, mem_closedBall, Real.dist_eq] at hη
  simp only [mem_ofPred_eq, mem_closedBall, Real.dist_eq]
  have hx : coding φ ω = φ a y := hφ.coding_eq ω
  rw [hx]
  refine hφ.abs_map_sub_le_of a hy (hφ.coding_mem η) hη fun w hw hwy => ?_
  refine le_min (hφ.abs_deriv_le a w hw) ?_
  calc |deriv (φ a) w| ≤ |deriv (φ a) y| * Real.exp (L * |w - y|) :=
        hφ.abs_deriv_le_mul_exp a hw hy
    _ ≤ |deriv (φ a) y| * Real.exp (L * ρ') := by
        gcongr
        exact hφ.L_nonneg

end ConformalIFS

/-! ### One-step information inequalities -/

/-- If `κ(B(x, ρ)) ≤ q μ(B(y, ρ'))`, then
`-log q - log(κ/μ)(B(x, ρ))^{-1} + I_μ(y, ρ') ≤ I_μ(x, ρ)`, where `I_μ(z, r) = -log μ(B(z, r))`.
-/
theorem info_step_ge {κ μ : Measure ℝ} [IsFiniteMeasure κ] [IsFiniteMeasure μ] (hκμ : κ ≤ μ)
    {x y ρ ρ' q : ℝ} (hq : 0 < q) (hκ : 0 < κ (closedBall x ρ))
    (hμy : 0 < μ (closedBall y ρ'))
    (h : κ (closedBall x ρ) ≤ ENNReal.ofReal q * μ (closedBall y ρ')) :
    -Real.log q - ratioInfo κ μ x ρ + ExactOverlaps.ballInformation μ y ρ' ≤
      ExactOverlaps.ballInformation μ x ρ := by
  set A := (κ (closedBall x ρ)).toReal
  set Bx := (μ (closedBall x ρ)).toReal
  set By := (μ (closedBall y ρ')).toReal
  have hA : 0 < A := ENNReal.toReal_pos hκ.ne' (measure_ne_top _ _)
  have hBx : 0 < Bx := hA.trans_le (ENNReal.toReal_mono (measure_ne_top _ _) (hκμ _))
  have hBy : 0 < By := ENNReal.toReal_pos hμy.ne' (measure_ne_top _ _)
  have hle : A ≤ q * By := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq.le] at this
  unfold ratioInfo ExactOverlaps.ballInformation
  rw [ENNReal.toReal_div]
  change -Real.log q - -Real.log (A / Bx) + -Real.log By ≤ -Real.log Bx
  rw [Real.log_div hA.ne' hBx.ne']
  have := Real.log_le_log hA hle
  rw [Real.log_mul hq.ne' hBy.ne'] at this
  linarith

/-- If `q μ(B(y, ρ')) ≤ κ(B(x, ρ))`, then
`I_μ(x, ρ) ≤ -log q - log(κ/μ)(B(x, ρ))^{-1} + I_μ(y, ρ')`. -/
theorem info_step_le {κ μ : Measure ℝ} [IsFiniteMeasure κ] [IsFiniteMeasure μ] (hκμ : κ ≤ μ)
    {x y ρ ρ' q : ℝ} (hq : 0 < q) (hμy : 0 < μ (closedBall y ρ'))
    (h : ENNReal.ofReal q * μ (closedBall y ρ') ≤ κ (closedBall x ρ)) :
    ExactOverlaps.ballInformation μ x ρ ≤
      -Real.log q - ratioInfo κ μ x ρ + ExactOverlaps.ballInformation μ y ρ' := by
  set A := (κ (closedBall x ρ)).toReal
  set Bx := (μ (closedBall x ρ)).toReal
  set By := (μ (closedBall y ρ')).toReal
  have hBy : 0 < By := ENNReal.toReal_pos hμy.ne' (measure_ne_top _ _)
  have hle : q * By ≤ A := by
    have := ENNReal.toReal_mono (measure_ne_top _ _) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq.le] at this
  have hA : 0 < A := (mul_pos hq hBy).trans_le hle
  have hBx : 0 < Bx := hA.trans_le (ENNReal.toReal_mono (measure_ne_top _ _) (hκμ _))
  unfold ratioInfo ExactOverlaps.ballInformation
  rw [ENNReal.toReal_div]
  change -Real.log Bx ≤ -Real.log q - -Real.log (A / Bx) + -Real.log By
  rw [Real.log_div hA.ne' hBx.ne']
  have := Real.log_le_log (mul_pos hq hBy) hle
  rw [Real.log_mul hq.ne' hBy.ne'] at this
  linarith

end FractalGeometry.SelfConformal.FengHu
