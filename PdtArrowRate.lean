/-
# The arrow's rate is forced by the inflation factor

The off-Perron modes of the Padovan substitution have modulus `rho^(-1/2)` and
decay at `(1/2) ln rho = 0.1406` per step.

This file shows that rate is **not an independent input**. It is forced by
UNIMODULARITY of the substitution matrix, in one line:

    |det M| = 1   =>   rho * |sigma|^2 = 1   =>   log |sigma| = -(1/2) log rho

so the decay rate `-log |sigma|` equals half the log of the inflation factor.
Scale and rate come from the SAME matrix — its dominant and sub-dominant
eigenvalues — tied together by the determinant.

For the Padovan matrix M = [[0,0,1],[1,0,1],[0,1,0]] (from s: a->b, b->c, c->ab)
the numbers are: det M = 1, char poly x^3 - x - 1, Perron root
rho = 1.32471795724475, |sigma| = 0.868836961832709 = rho^(-1/2), and
(1/2) ln rho = 0.140599787161481 (computed numerically; not part of the kernel
check).

WHAT IS PROVED HERE: the implication, for any positive real `rho` and any complex
`sigma` satisfying the unimodularity relation. WHAT IS NOT: that the physical
arrow IS this decay — that is an identification, not a theorem, and it is
never asserted in the kernel.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Norm

@[expose] public section

namespace PDT.ArrowRate

open Real Complex

/-- **Unimodularity forces the rate.** If the product of the Perron eigenvalue with
the squared modulus of the sub-dominant pair is 1 — which is what `|det| = 1` says
for a cubic with one real and one conjugate-pair eigenvalue — then the sub-dominant
log-modulus is exactly minus half the log of the Perron value. -/
theorem log_norm_eq_neg_half_log (ρ : ℝ) (hρ : 0 < ρ) (σ : ℂ) (hσ : σ ≠ 0)
    (h : ρ * Complex.normSq σ = 1) :
    Real.log ‖σ‖ = -(1 / 2) * Real.log ρ := by
  have hpos : (0:ℝ) < ‖σ‖ := norm_pos_iff.mpr hσ
  have key : ρ * ‖σ‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h
  have hlog := congrArg Real.log key
  rw [Real.log_mul (ne_of_gt hρ) (by positivity), Real.log_pow, Real.log_one] at hlog
  push_cast at hlog
  linarith

/-- **The decay rate is half the log of the inflation factor.** -/
theorem rate_eq_half_log (ρ : ℝ) (hρ : 0 < ρ) (σ : ℂ) (hσ : σ ≠ 0)
    (h : ρ * Complex.normSq σ = 1) :
    -Real.log ‖σ‖ = (1 / 2) * Real.log ρ := by
  rw [log_norm_eq_neg_half_log ρ hρ σ hσ h]; ring

/-- The same statement in modulus form: the sub-dominant modulus is
`rho^(-1/2)`. -/
theorem norm_eq_rpow_neg_half (ρ : ℝ) (hρ : 0 < ρ) (σ : ℂ) (hσ : σ ≠ 0)
    (h : ρ * Complex.normSq σ = 1) :
    ‖σ‖ = ρ ^ (-(1:ℝ) / 2) := by
  have hpos : (0:ℝ) < ‖σ‖ := norm_pos_iff.mpr hσ
  have hlog := log_norm_eq_neg_half_log ρ hρ σ hσ h
  have heq : Real.log ‖σ‖ = Real.log (ρ ^ (-(1:ℝ) / 2)) := by
    rw [Real.log_rpow hρ, hlog]; ring
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr hpos) (Set.mem_Ioi.mpr (by positivity)) heq

end PDT.ArrowRate
