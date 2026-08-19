import Mathlib

/-!
# Challenge: chirality of the Padovan substitution

This module is the small, trusted surface to audit. It states the chirality
package for the Padovan substitution, with `sorry` placeholders; the proved
versions are in `Solution.lean`.

The substitution is stated over the alphabet `Fin 3`, with the letters
`0, 1, 2` standing for `a, b, c`. Its incidence matrix has characteristic
polynomial `x³ − x − 1`; that orientation fact is not used or compared.

Three results, all at the iterate-factor level (they quantify over factors
of the concrete words `S^[n] [x]`, not over an abstract subshift):

1. **The successor invariant.** In every positive iterate, from any seed
   letter, each occurrence of `0` (`a`) is immediately followed by `1` (`b`).
2. **Chirality.** The word `ca` (here `[2, 0]`) is a factor of an iterate,
   while its reversal `ac` (here `[0, 2]`) is a factor of no iterate from any
   seed: the factor language of the substitution reads differently backwards.
3. **No long palindromic factor.** No factor of length ≥ 4 of any iterate
   from any seed is a palindrome.
-/

namespace ArithmeticOfTime

/-- The Padovan substitution: `0 ↦ [1]`, `1 ↦ [2]`, `2 ↦ [0, 1]`
(that is, `a ↦ b`, `b ↦ c`, `c ↦ ab`). -/
def s : Fin 3 → List (Fin 3)
  | 0 => [1]
  | 1 => [2]
  | 2 => [0, 1]

/-- Letterwise application of the substitution to a word: the concatenation
of the image blocks. -/
def S (w : List (Fin 3)) : List (Fin 3) := (w.map s).flatten

/-- **The invariant.** In every positive iterate `S^[n+1] [x]`, from any seed
letter, every occurrence of the letter `0` (that is, `a`) is immediately
followed by the letter `1` (that is, `b`). -/
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
`S^[n] [x]`, from any seed letter and at any iterate (including `n = 0`), is
a palindrome. -/
theorem padovan_no_long_palindrome (n : ℕ) (x : Fin 3) (u : List (Fin 3))
    (hu : u <:+: S^[n] [x]) (hlen : 4 ≤ u.length) : ¬ u.Palindrome := by
  sorry

end ArithmeticOfTime
