import Mathlib

/-!
# Challenge: the Pisot boundary of `xⁿ = x + 1` and the mechanical tick word

This module is the small, trusted surface to audit. It states two groups of
results, with `sorry` placeholders; the proved versions are in `Solution.lean`.

**Group 1 — root-modulus dichotomy for the two trinomials.** Every non-real
root of `x³ = x + 1` lies strictly inside the complex unit circle, and every
non-real root of `x⁴ = x + 1` lies strictly outside it. The compared
statements are exactly these inequalities about non-real roots — no real
root, minimal polynomial, or Pisot predicate appears in them. (Classically,
combined with irreducibility and the fact that each polynomial has a real
root exceeding one — for the quartic, the positive one of its two real
roots — the inequalities yield the usual reading: the plastic number is a
Pisot number and the quartic's positive root is not. That consequence is
prose, outside the compared statements.)

**Group 2 — the mechanical (Sturmian) tick word.** For a slope `β`, define
`tick β n = ⌊(n+1)β⌋ − ⌊nβ⌋`. For `0 < β < 1` the word is two-valued; its
Cesàro density is exactly `β` (any real slope); for irrational `β` it has no
period; and — for every real slope — any two equal-length windows have sums
differing by at most one. When `0 < β < 1`, so that the word is `{0,1}`-valued,
that window-sum bound is precisely the Sturmian 1-count balance property.
Irrationality of the slope enters as an explicit hypothesis, never an axiom.
-/

namespace ArithmeticOfTime

/-! ## Group 1 — the Pisot boundary -/

/-- Every non-real root `z` of `x³ = x + 1` has `‖z‖ < 1`. (With
irreducibility and the real root exceeding one — classical facts outside this
statement — this is the Pisot property of the plastic number.) -/
theorem cubic_conj_norm_lt_one (z : ℂ) (hz : z ^ 3 = z + 1) (him : z.im ≠ 0) :
    ‖z‖ < 1 := by
  sorry

/-- Every non-real root `w` of `x⁴ = x + 1` has `‖w‖ > 1`. (Classically this
denies the Pisot property to the quartic's positive real root; that reading
lies outside this statement.) -/
theorem quartic_conj_norm_gt_one (w : ℂ) (hw : w ^ 4 = w + 1) (him : w.im ≠ 0) :
    1 < ‖w‖ := by
  sorry

/-- **The root-modulus dichotomy.** For any non-real roots `z` of
`x³ = x + 1` and `w` of `x⁴ = x + 1`: `‖z‖ < 1 ∧ 1 < ‖w‖`. One flipped
inequality, driven purely by the degree. -/
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

/-- **Balanced (window-sum form).** For every real slope, any two windows of
equal length have sums differing by at most one. When `0 < β < 1` the word is
`{0,1}`-valued (`tick_two_valued`) and this is the Sturmian 1-count balance:
even, never random. -/
theorem tick_balanced (β : ℝ) (L i j : ℕ) :
    |(∑ k ∈ Finset.range L, tick β (i + k)) - (∑ k ∈ Finset.range L, tick β (j + k))| ≤ 1 := by
  sorry

/-! ## Group 3 — chirality of the Padovan substitution

The substitution is stated over the alphabet `Fin 3`, with the letters
`0, 1, 2` standing for `a, b, c`. Its incidence matrix has characteristic
polynomial `x³ − x − 1`; that orientation fact is not used or compared. -/

/-- The Padovan substitution: `0 ↦ [1]`, `1 ↦ [2]`, `2 ↦ [0, 1]`
(that is, `a ↦ b`, `b ↦ c`, `c ↦ ab`). -/
def s : Fin 3 → List (Fin 3)
  | 0 => [1]
  | 1 => [2]
  | 2 => [0, 1]

/-- Letterwise application of the substitution to a word: the concatenation
of the image blocks. -/
def S (w : List (Fin 3)) : List (Fin 3) := (w.map s).flatten

/-- **The invariant.** In every iterate `S^[n+1] [x]`, from any seed letter,
every occurrence of the letter `0` (that is, `a`) is immediately followed by
the letter `1` (that is, `b`). -/
theorem padovan_a_forces_b (n : ℕ) (x : Fin 3) (i : ℕ)
    (h : (S^[n + 1] [x])[i]? = some 0) :
    (S^[n + 1] [x])[i + 1]? = some 1 := by
  sorry

/-- **Chirality.** The word `ca` (here `[2, 0]`) IS a factor of an iterate,
while its reversal `ac` (here `[0, 2]`) is a factor of NO iterate from ANY
seed: the factor language of the substitution reads differently backwards. -/
theorem padovan_chirality (n : ℕ) (x : Fin 3) :
    ([2, 0] <:+: S^[5] [0]) ∧ ¬ [0, 2] <:+: S^[n] [x] := by
  sorry

/-- **No long palindromic factor.** No factor of length ≥ 4 of any iterate
from the seed `a` (here `0`) is a palindrome. -/
theorem padovan_no_long_palindrome (n : ℕ) (u : List (Fin 3))
    (hu : u <:+: S^[n] [0]) (hlen : 4 ≤ u.length) : ¬ u.Palindrome := by
  sorry

/-! ## Group 4 — Meyer separation on the cubic lattice -/

/-- **Meyer separation.** Let `r` be a real root and `z` a non-real root of
`x³ = x + 1`. For every nonzero integer coordinate triple `p = (p₁, p₂, p₃)`,
the real-embedding size times the squared complex-embedding size of
`p₁ + p₂ρ + p₃ρ²` is at least `1`:
distinct lattice points are never simultaneously small at both places. -/
theorem meyer_separation (r : ℝ) (hr : r ^ 3 = r + 1)
    (z : ℂ) (hz : z ^ 3 = z + 1) (him : z.im ≠ 0)
    (p : ℤ × ℤ × ℤ) (hp : p ≠ 0) :
    1 ≤ |(p.1 : ℝ) + (p.2.1 : ℝ) * r + (p.2.2 : ℝ) * r ^ 2| *
        ‖(p.1 : ℂ) + (p.2.1 : ℂ) * z + (p.2.2 : ℂ) * z ^ 2‖ ^ 2 := by
  sorry

end ArithmeticOfTime
