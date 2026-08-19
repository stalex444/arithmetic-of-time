import Mathlib

/-!
# Challenge: the Pisot boundary of `xⁿ = x + 1` and the mechanical tick word

This module is the small, trusted surface to audit. It states two groups of
results, with `sorry` placeholders; the proved versions are in `Solution.lean`.

**Group 1 — the Pisot boundary of the trinomial family.** Every non-real root
of `x³ = x + 1` lies strictly inside the complex unit circle, and every
non-real root of `x⁴ = x + 1` lies strictly outside it. Consequently the real
root of the cubic (the plastic number) is a Pisot number, while the real root
of the quartic is not: between degrees three and four the family's conjugate
dynamics switches from contraction to expansion. The dichotomy is stated for
the two concrete polynomials; no general Pisot theory is claimed.

**Group 2 — the mechanical (Sturmian) tick word.** For a slope `β`, define
`tick β n = ⌊(n+1)β⌋ − ⌊nβ⌋`. For `0 < β < 1` the word is two-valued; its
Cesàro density is exactly `β`; for irrational `β` it has no period; and any
two windows of equal length carry 1-counts differing by at most one (balance).
Irrationality of the slope enters as an explicit hypothesis, never an axiom.
-/

namespace ArithmeticOfTime

/-! ## Group 1 — the Pisot boundary -/

/-- Every non-real root `z` of `x³ = x + 1` has `‖z‖ < 1`: the conjugate mode
of the plastic number contracts, so the cubic's real root is a Pisot number. -/
theorem cubic_conj_norm_lt_one (z : ℂ) (hz : z ^ 3 = z + 1) (him : z.im ≠ 0) :
    ‖z‖ < 1 := by
  sorry

/-- Every non-real root `w` of `x⁴ = x + 1` has `‖w‖ > 1`: the conjugate mode
of the quartic's real root expands, so that root is not a Pisot number. -/
theorem quartic_conj_norm_gt_one (w : ℂ) (hw : w ^ 4 = w + 1) (him : w.im ≠ 0) :
    1 < ‖w‖ := by
  sorry

/-- **The Pisot boundary dichotomy.** The cubic settles and the quartic
spirals: for any non-real roots `z` of `x³ = x + 1` and `w` of `x⁴ = x + 1`,
`‖z‖ < 1 ∧ 1 < ‖w‖`. One flipped inequality, driven purely by the degree. -/
theorem pisot_boundary_dichotomy
    (z : ℂ) (hz : z ^ 3 = z + 1) (hzim : z.im ≠ 0)
    (w : ℂ) (hw : w ^ 4 = w + 1) (hwim : w.im ≠ 0) :
    ‖z‖ < 1 ∧ 1 < ‖w‖ := by
  sorry

/-! ## Group 2 — the mechanical tick word -/

/-- The mechanical (Beatty/Sturmian) word of slope `β`:
`tick β n = ⌊(n+1)·β⌋ − ⌊n·β⌋`, the duration of the `n`-th tick. -/
noncomputable def tick (β : ℝ) (n : ℕ) : ℤ := ⌊((n : ℝ) + 1) * β⌋ - ⌊(n : ℝ) * β⌋

/-- **Two-valued.** For `0 < β < 1`, every letter of the word is `0` or `1`. -/
theorem tick_two_valued (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    tick β n = 0 ∨ tick β n = 1 := by
  sorry

/-- **Density.** The Cesàro mean of the word converges to the slope:
`(∑_{k<N} tick β k) / N → β` as `N → ∞`. -/
theorem tick_density (β : ℝ) :
    Filter.Tendsto (fun N : ℕ => ((∑ k ∈ Finset.range N, tick β k : ℤ) : ℝ) / (N : ℝ))
      Filter.atTop (nhds β) := by
  sorry

/-- **Aperiodic.** For an irrational slope, the word has no period: there is
no `p > 0` with `tick β (n + p) = tick β n` for all `n`. -/
theorem tick_aperiodic (β : ℝ) (hβ : Irrational β) :
    ¬ ∃ p : ℕ, 0 < p ∧ ∀ n : ℕ, tick β (n + p) = tick β n := by
  sorry

/-- **Balanced.** Any two windows of equal length have 1-counts differing by
at most one — the Sturmian balance property: even, never random. -/
theorem tick_balanced (β : ℝ) (L i j : ℕ) :
    |(∑ k ∈ Finset.range L, tick β (i + k)) - (∑ k ∈ Finset.range L, tick β (j + k))| ≤ 1 := by
  sorry

end ArithmeticOfTime
