import Mathlib

/-!
# ConstantChain — the coupling chain κ < r_in < χ < A* and the fixed-arm tick

House style: everything is proved over HYPOTHETICAL roots — any `r : ℝ` with
`r³ = r + 1` and `0 < r` (the unique real root of `x³ − x − 1`, ρ ≈ 1.3247)
and any `q : ℝ` with `q⁴ = q + 1` and `0 < q` (the positive real root of
`x⁴ − x − 1`, Q ≈ 1.2207). Derived quantities:

* `χ := q/r` (the two-clock ratio, ≈ 0.92151);
* `κ := χ²` (the portal coefficient, ≈ 0.84919);
* `r_in := √3/2` (the Voronoi in-radius of the unit 1 in the canonical
  `Tr(x·x̄)` gauge, ≈ 0.86603);
* `A* := √(2r) − √(3/4 − r⁻²)` (the ambiguity threshold, ≈ 1.20326).

## Theorems

* **T-BOUNDS** (`root_cubic_bounds`, `root_quartic_bounds`): rational
  bracketing `1.32 < r < 1.33` and `1.22 < q < 1.23`, by sign evaluation of
  the strictly monotone (for x > 0) defining polynomials at rational points —
  each bound is a product factorization `(x − c)·(positive) = f(c)-defect`
  closed by `linear_combination` + `nlinarith`.
* **T-CHAIN** (`kappa_lt_rin`, `rin_lt_chi`, `chi_lt_Astar`, `chain_strict`):
  the strict chain **κ < r_in < χ < A\***. Square-root comparisons are
  restated as polynomial inequalities in `r, q` (using positivity of both
  sides) and closed with `nlinarith` over the brackets + defining equations:
  `κ < r_in ⟺ 4(q+1) < 3r⁴`; `r_in < χ ⟺ 3r² < 4q²`; `χ < A*` via the
  rational cut `χ < 0.94 < 1.18 ≤ √(2r) − √(3/4 − r⁻²)`. Well-definedness of
  `A*` (`radicand_pos`: `3/4 − r⁻² > 0`, from `3r² > 4`) is proved so the
  inner square root is of a genuinely positive quantity.
* **T-FIXED** (`cleanWindow_tick_eq_one`, `cleanWindow_tick_sInf`,
  `chi_mem_cleanWindow`, `chi_tick_eq_one`): the log-free clean-window
  characterization. `certSteps r A = {n | A·((√r)⁻¹)ⁿ ≤ r_in}` is the set of
  step counts after which the injected amplitude `A`, contracted by
  `ρ^(−1/2)` per tick, sits at-or-inside the certification radius; for
  `r_in < A ≤ r_in·√r` the LEAST element is exactly 1 (`IsLeast`, hence
  `sInf = 1`): one contraction step certifies, zero steps do not. Corollary:
  `χ` satisfies the window hypothesis (`r_in < χ < r_in·√r`, the second via
  `4q² < 3(r+1) = 3r³`), so the χ-sourced first-order tick is clean with
  `n* = 1` — and by T-CHAIN the portal `κ` is instant (`κ < r_in`). The
  optional ceiling form `⌈ln(A/r_in) / (½·ln r)⌉ = 1`
  (`cleanWindow_tick_ceil`) is derived from the log-free inequalities.
* **T-ASTAR-IDENTITY** (`kappa_sq_mul_r_eq`, plus `one_sub_inv_cubic_root`,
  `one_sub_inv_quartic_root`): the exact algebraic identities:
  `κ²·r = (q+1)/(r+1)` (polynomial core `q⁴(r+1) = (q+1)r³`, an unconditional
  consequence of the two defining equations — verified numerically at 50 dps
  first, residual 2.7e−51), `1 − r⁻¹ = r⁻⁵` (namely λ₃ = ρ⁻⁵) and
  `1 − q⁻¹ = 2 − q³` (namely λ₄ = 2 − Q³).

## Faithfulness notes (reformulations, none weakening)

* Every theorem quantifies over ALL `r, q` satisfying the defining equations
  with positivity — stronger than fixing the particular roots (each equation
  has exactly one positive real solution, so the hypotheses pin the objects).
* `r⁻²` in `A*` is written `(r²)⁻¹`; the per-tick contraction factor
  `ρ^(−1/2)` is written `(√r)⁻¹`, proved equal to the `rpow` form
  `r ^ (−(1/2) : ℝ)` in `sqrt_inv_eq_rpow` — the same normalization as
  `Settling.norm_z_eq_rpow`.
* "Certification time exactly 1" is stated log-free as
  `IsLeast (certSteps r A) 1`: membership of 1 (one step certifies) plus
  minimality (zero steps do not) — the defining property of `n* = 1`, with
  the ceiling form derived, not assumed.
* The chain constants are compared through squares against explicit
  positivity of both sides; no square root is ever compared directly.
-/

namespace Time

noncomputable section

/-! ## The objects -/

/-- The Voronoi in-radius of the unit `1` of `ℤ[ρ]` in the canonical
`Tr(x·x̄)` gauge: `r_in = √3/2 ≈ 0.86603`. -/
def rin : ℝ := Real.sqrt 3 / 2

/-- The two-clock ratio `χ = q/r ≈ 0.92151` (`Q/ρ` on the actual roots). -/
def chi (r q : ℝ) : ℝ := q / r

/-- The portal coefficient `κ = χ² ≈ 0.84919`. -/
def kappa (r q : ℝ) : ℝ := chi r q ^ 2

/-- The ambiguity threshold `A* = √(2r) − √(3/4 − r⁻²) ≈ 1.20326`. -/
def Astar (r : ℝ) : ℝ := Real.sqrt (2 * r) - Real.sqrt (3 / 4 - (r ^ 2)⁻¹)

/-- The certification-step set of an injected amplitude `A`: the step counts
`n` after which `A`, contracted by the tick factor `ρ^(−1/2) = (√r)⁻¹` per
step, is at-or-inside the certification radius `r_in`. -/
def certSteps (r A : ℝ) : Set ℕ := {n | A * (Real.sqrt r)⁻¹ ^ n ≤ rin}

/-- The tick contraction factor `(√r)⁻¹` IS `r^(−1/2)` (rpow form), matching
`Settling.norm_z_eq_rpow`. -/
lemma sqrt_inv_eq_rpow {r : ℝ} (hr0 : 0 < r) :
    (Real.sqrt r)⁻¹ = r ^ (-(1 / 2) : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hr0.le]

/-- `r_in > 0`. -/
lemma rin_pos : 0 < rin := by
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [rin]; linarith

/-! ## T-BOUNDS — rational brackets on the roots -/

section Bounds

variable {r q : ℝ}

/-- `1.32 < r`: sign of `x³ − x − 1` at `1.32` is negative
(`f(1.32) = −0.020032`), factored against the quadratic cofactor. -/
theorem root_cubic_gt (hr : r ^ 3 = r + 1) (hr0 : 0 < r) : 1.32 < r := by
  have key : (r - 1.32) * (r ^ 2 + 1.32 * r + 0.7424) = 0.020032 := by
    linear_combination hr
  have hpos : 0 < r ^ 2 + 1.32 * r + 0.7424 := by nlinarith [sq_nonneg r]
  by_contra hle
  rw [not_lt] at hle
  have h2 : (r - 1.32) * (r ^ 2 + 1.32 * r + 0.7424) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
  linarith

/-- `r < 1.33`: sign of `x³ − x − 1` at `1.33` is positive
(`f(1.33) = +0.022637`). -/
theorem root_cubic_lt (hr : r ^ 3 = r + 1) (hr0 : 0 < r) : r < 1.33 := by
  have key : (r - 1.33) * (r ^ 2 + 1.33 * r + 0.7689) = -0.022637 := by
    linear_combination hr
  have hpos : 0 < r ^ 2 + 1.33 * r + 0.7689 := by nlinarith [sq_nonneg r]
  by_contra hle
  rw [not_lt] at hle
  have h2 : 0 ≤ (r - 1.33) * (r ^ 2 + 1.33 * r + 0.7689) :=
    mul_nonneg (by linarith) hpos.le
  linarith

/-- **T-BOUNDS (cubic).** `1.32 < r < 1.33` for the positive root of
`x³ = x + 1`. -/
theorem root_cubic_bounds (hr : r ^ 3 = r + 1) (hr0 : 0 < r) :
    1.32 < r ∧ r < 1.33 :=
  ⟨root_cubic_gt hr hr0, root_cubic_lt hr hr0⟩

/-- `1.22 < q`: sign of `x⁴ − x − 1` at `1.22` is negative
(`f(1.22) = −0.00466544`), factored against the cubic cofactor. -/
theorem root_quartic_gt (hq : q ^ 4 = q + 1) (hq0 : 0 < q) : 1.22 < q := by
  have key : (q - 1.22) * (q ^ 3 + 1.22 * q ^ 2 + 1.4884 * q + 0.815848)
      = 0.00466544 := by linear_combination hq
  have hpos : 0 < q ^ 3 + 1.22 * q ^ 2 + 1.4884 * q + 0.815848 := by
    have h3 : 0 < q ^ 3 := pow_pos hq0 3
    have h2 : 0 < q ^ 2 := pow_pos hq0 2
    nlinarith
  by_contra hle
  rw [not_lt] at hle
  have h2 : (q - 1.22) * (q ^ 3 + 1.22 * q ^ 2 + 1.4884 * q + 0.815848) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
  linarith

/-- `q < 1.23`: sign of `x⁴ − x − 1` at `1.23` is positive
(`f(1.23) = +0.05886641`). -/
theorem root_quartic_lt (hq : q ^ 4 = q + 1) (hq0 : 0 < q) : q < 1.23 := by
  have key : (q - 1.23) * (q ^ 3 + 1.23 * q ^ 2 + 1.5129 * q + 0.860867)
      = -0.05886641 := by linear_combination hq
  have hpos : 0 < q ^ 3 + 1.23 * q ^ 2 + 1.5129 * q + 0.860867 := by
    have h3 : 0 < q ^ 3 := pow_pos hq0 3
    have h2 : 0 < q ^ 2 := pow_pos hq0 2
    nlinarith
  by_contra hle
  rw [not_lt] at hle
  have h2 : 0 ≤ (q - 1.23) * (q ^ 3 + 1.23 * q ^ 2 + 1.5129 * q + 0.860867) :=
    mul_nonneg (by linarith) hpos.le
  linarith

/-- **T-BOUNDS (quartic).** `1.22 < q < 1.23` for the positive root of
`x⁴ = x + 1`. -/
theorem root_quartic_bounds (hq : q ^ 4 = q + 1) (hq0 : 0 < q) :
    1.22 < q ∧ q < 1.23 :=
  ⟨root_quartic_gt hq hq0, root_quartic_lt hq hq0⟩

/-- Derived square bracket: `1.7424 < r² < 1.7689`. -/
lemma sq_cubic_bounds (hr : r ^ 3 = r + 1) (hr0 : 0 < r) :
    1.7424 < r ^ 2 ∧ r ^ 2 < 1.7689 := by
  have h1 := root_cubic_gt hr hr0
  have h2 := root_cubic_lt hr hr0
  constructor
  · nlinarith [sq_nonneg (r - 1.32)]
  · nlinarith [sq_nonneg (1.33 - r)]

/-- Derived fourth-power lower bound: `3.03595776 < r⁴`. -/
lemma pow4_cubic_gt (hr : r ^ 3 = r + 1) (hr0 : 0 < r) :
    3.03595776 < r ^ 4 := by
  have h2 := (sq_cubic_bounds hr hr0).1
  nlinarith [sq_nonneg (r ^ 2 - 1.7424)]

/-- Derived square lower bound: `1.4884 < q²`. -/
lemma sq_quartic_gt (hq : q ^ 4 = q + 1) (hq0 : 0 < q) : 1.4884 < q ^ 2 := by
  have h1 := root_quartic_gt hq hq0
  nlinarith [sq_nonneg (q - 1.22)]

end Bounds

/-! ## T-CHAIN — the strict chain κ < r_in < χ < A* -/

section Chain

variable {r q : ℝ}

/-- **Chain link 1: `κ < r_in`** — the portal coefficient sits strictly below
the certification radius (instant settling). Squared form: `4(q+1) < 3r⁴`. -/
theorem kappa_lt_rin (hr : r ^ 3 = r + 1) (hr0 : 0 < r)
    (hq : q ^ 4 = q + 1) (hq0 : 0 < q) : kappa r q < rin := by
  have hr4 : (0 : ℝ) < r ^ 4 := pow_pos hr0 4
  have hqb := root_quartic_lt hq hq0
  have hkey : 4 * (q + 1) < 3 * r ^ 4 := by
    have := pow4_cubic_gt hr hr0
    linarith
  have hknn : 0 ≤ kappa r q * 2 := by
    have : 0 ≤ kappa r q := by rw [kappa]; positivity
    linarith
  rw [rin, lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  refine (Real.lt_sqrt hknn).mpr ?_
  have hexp : (kappa r q * 2) ^ 2 * r ^ 4 = 4 * (q + 1) := by
    rw [kappa, chi, ← hq]
    field_simp
    ring
  nlinarith [hexp, hkey, hr4]

/-- **Chain link 2: `r_in < χ`** — the two-clock ratio sits strictly above
the certification radius (a living clock, not instant). Squared form:
`3r² < 4q²`. -/
theorem rin_lt_chi (hr : r ^ 3 = r + 1) (hr0 : 0 < r)
    (hq : q ^ 4 = q + 1) (hq0 : 0 < q) : rin < chi r q := by
  have hchi2 : 0 < chi r q * 2 := by
    have : 0 < chi r q := div_pos hq0 hr0
    linarith
  rw [rin, div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
  refine (Real.sqrt_lt' hchi2).mpr ?_
  have hexp : (chi r q * 2) ^ 2 * r ^ 2 = 4 * q ^ 2 := by
    rw [chi]
    field_simp
    ring
  have hr2 : (0 : ℝ) < r ^ 2 := pow_pos hr0 2
  have hkey : 3 * r ^ 2 < 4 * q ^ 2 := by
    have h1 := (sq_cubic_bounds hr hr0).2
    have h2 := sq_quartic_gt hq hq0
    linarith
  nlinarith [hexp, hkey, hr2]

/-- The radicand of `A*` is genuinely positive: `3/4 − r⁻² > 0`
(equivalently `3r² > 4`), so `A*` is the difference of square roots of
positive quantities — well-defined, not a `√(negative) = 0` artifact. -/
theorem radicand_pos (hr : r ^ 3 = r + 1) (hr0 : 0 < r) :
    0 < 3 / 4 - (r ^ 2)⁻¹ := by
  have hr2 : (0 : ℝ) < r ^ 2 := pow_pos hr0 2
  have hid : r ^ 2 * (r ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hr2.ne'
  have hinv : (0 : ℝ) < (r ^ 2)⁻¹ := inv_pos.mpr hr2
  have h1 := (sq_cubic_bounds hr hr0).1
  nlinarith [hid, hinv, h1]

/-- **Chain link 3: `χ < A*`** — the two-clock ratio sits strictly below the
ambiguity threshold (its ticks are never ambiguous). Via the rational cut
`χ < 0.94 < 1.18 ≤ √(2r) − √(3/4 − r⁻²)`. -/
theorem chi_lt_Astar (hr : r ^ 3 = r + 1) (hr0 : 0 < r)
    (hq : q ^ 4 = q + 1) (hq0 : 0 < q) : chi r q < Astar r := by
  have hrb := root_cubic_gt hr hr0
  have hqb := root_quartic_lt hq hq0
  -- χ < 0.94
  have h1 : chi r q < 0.94 := by
    rw [chi, div_lt_iff₀ hr0]
    nlinarith
  -- 1.62 < √(2r)
  have h2 : (1.62 : ℝ) < Real.sqrt (2 * r) := by
    refine (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1.62)).mpr ?_
    nlinarith
  -- √(3/4 − r⁻²) < 0.44
  have h3 : Real.sqrt (3 / 4 - (r ^ 2)⁻¹) < 0.44 := by
    refine (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 0.44)).mpr ?_
    have hr2 : (0 : ℝ) < r ^ 2 := pow_pos hr0 2
    have hid : r ^ 2 * (r ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hr2.ne'
    have hinv : (0 : ℝ) < (r ^ 2)⁻¹ := inv_pos.mpr hr2
    have hup := (sq_cubic_bounds hr hr0).2
    nlinarith [hid, hinv, hup]
  rw [Astar]
  linarith

/-- **T-CHAIN.** The strict coupling chain `κ < r_in < χ < A*`:
`(q/r)² < √3/2 < q/r < √(2r) − √(3/4 − r⁻²)` for the positive roots of
`x³ = x + 1` and `x⁴ = x + 1`. Numerically
`0.84919 < 0.86603 < 0.92151 < 1.20326`; here proved exactly, so the chain
is untunable forever. -/
theorem chain_strict (hr : r ^ 3 = r + 1) (hr0 : 0 < r)
    (hq : q ^ 4 = q + 1) (hq0 : 0 < q) :
    kappa r q < rin ∧ rin < chi r q ∧ chi r q < Astar r :=
  ⟨kappa_lt_rin hr hr0 hq hq0, rin_lt_chi hr hr0 hq hq0,
    chi_lt_Astar hr hr0 hq hq0⟩

end Chain

/-! ## T-FIXED — the clean-window tick theorem (log-free) -/

section Fixed

variable {r q A : ℝ}

/-- **T-FIXED (a), log-free.** For any injection amplitude `A` in the clean
window `r_in < A ≤ r_in·√r`, the certification time is EXACTLY 1: one
contraction step lands at-or-inside the certification radius
(`A·(√r)⁻¹ ≤ r_in`) while zero steps do not (`A > r_in`) — stated as:
`1` is the least element of the certification-step set. -/
theorem cleanWindow_tick_eq_one (hr0 : 0 < r)
    (hA1 : rin < A) (hA2 : A ≤ rin * Real.sqrt r) :
    IsLeast (certSteps r A) 1 := by
  constructor
  · show A * (Real.sqrt r)⁻¹ ^ 1 ≤ rin
    have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
    rw [pow_one, ← div_eq_mul_inv, div_le_iff₀ hs]
    exact hA2
  · intro n hn
    by_contra hlt
    rw [not_le] at hlt
    interval_cases n
    have h0 : A * (Real.sqrt r)⁻¹ ^ 0 ≤ rin := hn
    rw [pow_zero, mul_one] at h0
    linarith

/-- **T-FIXED (a), infimum form.** `sInf {n | A·((√r)⁻¹)ⁿ ≤ r_in} = 1` on the
clean window. -/
theorem cleanWindow_tick_sInf (hr0 : 0 < r)
    (hA1 : rin < A) (hA2 : A ≤ rin * Real.sqrt r) :
    sInf (certSteps r A) = 1 :=
  (cleanWindow_tick_eq_one hr0 hA1 hA2).csInf_eq

/-- `χ < r_in·√r` (strict): squared form `4q² < 3r³ = 3(r+1)`. Together with
`rin_lt_chi` this puts `χ` strictly inside the clean window. -/
theorem chi_lt_rin_mul_sqrt (hr : r ^ 3 = r + 1) (hr0 : 0 < r)
    (hq : q ^ 4 = q + 1) (hq0 : 0 < q) :
    chi r q < rin * Real.sqrt r := by
  have hrin : rin * Real.sqrt r = Real.sqrt (3 * r) / 2 := by
    rw [rin, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), div_mul_eq_mul_div]
  rw [hrin, lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have hchi2 : 0 ≤ chi r q * 2 := by
    have : 0 < chi r q := div_pos hq0 hr0
    linarith
  refine (Real.lt_sqrt hchi2).mpr ?_
  have hexp : (chi r q * 2) ^ 2 * r ^ 2 = 4 * q ^ 2 := by
    rw [chi]
    field_simp
    ring
  have hr2 : (0 : ℝ) < r ^ 2 := pow_pos hr0 2
  have hkey : 4 * q ^ 2 < 3 * r * r ^ 2 := by
    have h1 : 4 * q ^ 2 < 6.0516 := by
      have hqb := root_quartic_lt hq hq0
      nlinarith [sq_nonneg (1.23 - q)]
    have h2 : 3 * r * r ^ 2 = 3 * (r + 1) := by linear_combination 3 * hr
    have hrb := root_cubic_gt hr hr0
    nlinarith
  nlinarith [hexp, hkey, hr2]

/-- **T-FIXED (b), window membership.** `χ` satisfies the clean-window
hypothesis: `r_in < χ ≤ r_in·√r` (numerically `0.8660 < 0.9215 ≤ 0.9968`). -/
theorem chi_mem_cleanWindow (hr : r ^ 3 = r + 1) (hr0 : 0 < r)
    (hq : q ^ 4 = q + 1) (hq0 : 0 < q) :
    rin < chi r q ∧ chi r q ≤ rin * Real.sqrt r :=
  ⟨rin_lt_chi hr hr0 hq hq0, (chi_lt_rin_mul_sqrt hr hr0 hq hq0).le⟩

/-- **T-FIXED (b), corollary.** If the two-clock ratio `χ` is the fixed
injection amplitude, first-order ticks are clean-window with certification
time exactly `n* = 1`. -/
theorem chi_tick_eq_one (hr : r ^ 3 = r + 1) (hr0 : 0 < r)
    (hq : q ^ 4 = q + 1) (hq0 : 0 < q) :
    IsLeast (certSteps r (chi r q)) 1 :=
  cleanWindow_tick_eq_one hr0 (rin_lt_chi hr hr0 hq hq0)
    (chi_lt_rin_mul_sqrt hr hr0 hq hq0).le

/-- **T-FIXED (a), ceiling form (derived).** On the clean window, with
`1 < r`, the formula `n* = ⌈ln(A/r_in) / (½·ln r)⌉` evaluates to `1` —
derived FROM the log-free inequalities, not assumed. -/
theorem cleanWindow_tick_ceil (hr1 : 1 < r)
    (hA1 : rin < A) (hA2 : A ≤ rin * Real.sqrt r) :
    ⌈Real.log (A / rin) / (1 / 2 * Real.log r)⌉ = 1 := by
  have hr0 : (0 : ℝ) < r := lt_trans one_pos hr1
  have hrinpos := rin_pos
  have hApos : 0 < A := lt_trans hrinpos hA1
  have hlogr : 0 < Real.log r := Real.log_pos hr1
  have hden : 0 < 1 / 2 * Real.log r := by linarith
  have hquot : 1 < A / rin := (one_lt_div hrinpos).mpr hA1
  have hlognum : 0 < Real.log (A / rin) := Real.log_pos hquot
  have hupper : Real.log (A / rin) ≤ 1 / 2 * Real.log r := by
    have hsq : Real.log (Real.sqrt r) = Real.log r / 2 := Real.log_sqrt hr0.le
    have hle : A / rin ≤ Real.sqrt r := by
      rw [div_le_iff₀ hrinpos]
      linarith [hA2, mul_comm rin (Real.sqrt r)]
    have hsqrtpos : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
    calc Real.log (A / rin) ≤ Real.log (Real.sqrt r) :=
          (Real.log_le_log_iff (by positivity) hsqrtpos).mpr hle
      _ = 1 / 2 * Real.log r := by rw [hsq]; ring
  have hpos : 0 < Real.log (A / rin) / (1 / 2 * Real.log r) :=
    div_pos hlognum hden
  have hle1 : Real.log (A / rin) / (1 / 2 * Real.log r) ≤ 1 := by
    rw [div_le_one hden]
    exact hupper
  have hc1 : ⌈Real.log (A / rin) / (1 / 2 * Real.log r)⌉ ≤ 1 := by
    apply Int.ceil_le.mpr
    push_cast
    exact hle1
  have hc2 : 0 < ⌈Real.log (A / rin) / (1 / 2 * Real.log r)⌉ :=
    Int.ceil_pos.mpr hpos
  omega

end Fixed

/-! ## T-ASTAR-IDENTITY — the exact algebraic identities -/

section Identities

variable {r q : ℝ}

/-- Polynomial core of the identity `κ²ρ = (Q+1)/(ρ+1)`:
`q⁴(r+1) = (q+1)r³`, an unconditional consequence of the two defining
equations (both sides equal `(q+1)(r+1)`). -/
theorem quartic_cubic_identity (hr : r ^ 3 = r + 1) (hq : q ^ 4 = q + 1) :
    q ^ 4 * (r + 1) = (q + 1) * r ^ 3 := by
  linear_combination (r + 1) * hq - (q + 1) * hr

/-- **The exact identity `κ²·ρ = (Q+1)/(ρ+1)`** (division form):
`((q/r)²)²·r = (q+1)/(r+1)`. Verified numerically at 50 dps first
(residual 2.7e−51), then proved exact here. -/
theorem kappa_sq_mul_r_eq (hr : r ^ 3 = r + 1) (hr0 : 0 < r)
    (hq : q ^ 4 = q + 1) (hq0 : 0 < q) :
    kappa r q ^ 2 * r = (q + 1) / (r + 1) := by
  have hrne : r ≠ 0 := hr0.ne'
  have hr1 : (0 : ℝ) < r + 1 := by linarith
  have h1 : kappa r q ^ 2 * r = q ^ 4 / r ^ 3 := by
    rw [kappa, chi]
    field_simp
  rw [h1, div_eq_div_iff (by positivity) hr1.ne']
  linear_combination quartic_cubic_identity hr hq

/-- **The exact identity `λ₃ = ρ⁻⁵`**:
`1 − r⁻¹ = (r⁵)⁻¹` (polynomial core `r⁴(r−1) = 1`). -/
theorem one_sub_inv_cubic_root (hr : r ^ 3 = r + 1) (hr0 : 0 < r) :
    1 - r⁻¹ = (r ^ 5)⁻¹ := by
  have hrne : r ≠ 0 := hr0.ne'
  have hpoly : r ^ 4 * (r - 1) = 1 := by
    linear_combination (r ^ 2 - r + 1) * hr
  field_simp
  linear_combination hpoly

/-- **The exact identity `λ₄ = 2 − Q³`**:
`1 − q⁻¹ = 2 − q³` (polynomial core `q(2 − q³) = q − 1`). -/
theorem one_sub_inv_quartic_root (hq : q ^ 4 = q + 1) (hq0 : 0 < q) :
    1 - q⁻¹ = 2 - q ^ 3 := by
  have hqne : q ≠ 0 := hq0.ne'
  field_simp
  linear_combination hq

end Identities

end

end Time
