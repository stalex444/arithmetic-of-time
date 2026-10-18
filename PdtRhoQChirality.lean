/-
# The rhoQ substitution is chiral

The substitution below has inflation factor `rhoQ`, on the 12-letter product
alphabet {p,q,r} x {1,2,3,4}: it is the tensor of the two founding
substitutions (cubic `x^3 - x - 1` and quartic `x^4 - x - 1`). Its incidence
matrix has characteristic polynomial exactly
`minpoly(rhoQ) = x^12 - 3x^9 - 2x^8 + 2x^6 - x^5 - 3x^4 - x^3 + x - 1`, which is
irreducible (both proved in `PdtCharpolyTensor` and `PdtRulerMinpoly`); that the
matrix is primitive was found by computation and is not proved here.

A computation (not part of this repository) also found that its factor language
is CHIRAL: 33 of 79 two-letter factors have a reversal the language forbids, on
a language stabilised at 2,506,218 letters. This file proves a witness pair of
that chirality in the kernel.

WHAT IS PROVED HERE: the witness pair. `q2 p1` is a factor of an iterate, while
its reversal `p1 q2` is a factor of NO iterate from ANY seed. So the factor
language is not closed under reversal — for every seed and every iterate, with no
enumeration on the forbidden side.

THE ENGINE is a successor invariant, the same shape as the 3-letter Padovan
result (`Time.Padovan.every_a_followed_by_b`): `p1` occurs in exactly one image,
`s(r4) = p1 p2 q1 q2`, at position 0, and is never the last letter of any image. So every `p1` in any concatenation of
images has its successor inside the same image, and that successor is `p2`.

WHAT IS NOT PROVED HERE, and must not be read into it: that the projection to
three letters inherits the Padovan `padovan_chirality`. It does not — the
projected word has 8 two-letter factors against the Padovan word's 7 (by
computation), so it is a different word. This file proves the 12-letter
statement on its own terms. Nor is any physical reading asserted: that this
handedness IS the arrow of time is an identification, not a theorem, and is
never asserted in the kernel.
-/

module
public import Mathlib

@[expose] public section

namespace PdtRhoQ

/-- The 12-letter product alphabet {p,q,r} x {1,2,3,4}. -/
inductive Letter
  | p1 | p2 | p3 | p4
  | q1 | q2 | q3 | q4
  | r1 | r2 | r3 | r4
  deriving DecidableEq, Repr

open Letter

/-- The substitution: the tensor of the cubic and quartic rules. Its incidence
matrix has characteristic polynomial `minpoly(rhoQ)`
(`PdtCharpolyTensor.substitution_charpoly`). -/
def s : Letter → List Letter
  | p1 => [q2]        | q1 => [r2]        | r1 => [p2, q2]
  | p2 => [q3]        | q2 => [r3]        | r2 => [p3, q3]
  | p3 => [q4]        | q3 => [r4]        | r3 => [p4, q4]
  | p4 => [q1, q2]    | q4 => [r1, r2]    | r4 => [p1, p2, q1, q2]

/-- Letterwise application. -/
def S : List Letter → List Letter
  | [] => []
  | x :: w => s x ++ S w

@[simp] theorem S_nil : S [] = [] := rfl

@[simp] theorem S_cons (x : Letter) (w : List Letter) : S (x :: w) = s x ++ S w := rfl

/-! ## The invariant: every `p1` is immediately followed by `p2` -/

/-- The pair condition: `p1` must be followed by `p2`; every other pair is
allowed. -/
def okPair : Letter → Letter → Bool
  | p1, p2 => true
  | p1, _  => false
  | _, _   => true

/-- The final-letter condition: a word may not end in `p1`. -/
def okLast : Letter → Bool
  | p1 => false
  | _  => true

/-- `good w`: every occurrence of `p1` in `w` is immediately followed by `p2` —
in particular `w` does not end in `p1`. Boolean, hence decidable. -/
def good : List Letter → Bool
  | [] => true
  | [x] => okLast x
  | x :: y :: w => okPair x y && good (y :: w)

theorem good_tail {x : Letter} {w : List Letter} (h : good (x :: w) = true) :
    good w = true := by
  cases w with
  | nil => rfl
  | cons y w' =>
    have h' : okPair x y = true ∧ good (y :: w') = true := by
      simpa [good, Bool.and_eq_true] using h
    exact h'.2

/-- If `x` may end a word it may precede anything. -/
theorem okPair_of_okLast {x : Letter} (h : okLast x = true) (y : Letter) :
    okPair x y = true := by
  revert h
  cases x <;> cases y <;> decide

theorem good_append {u v : List Letter} (hu : good u = true) (hv : good v = true) :
    good (u ++ v) = true := by
  induction u with
  | nil => simpa using hv
  | cons x u ih =>
    cases u with
    | nil =>
      cases v with
      | nil => simpa using hu
      | cons y v' =>
        have hx : okLast x = true := by simpa [good] using hu
        have hpair := okPair_of_okLast hx y
        show good (x :: y :: v') = true
        simp only [good, Bool.and_eq_true]
        exact ⟨hpair, hv⟩
    | cons y u' =>
      have h' : okPair x y = true ∧ good (y :: u') = true := by
        simpa [good, Bool.and_eq_true] using hu
      have h2 := ih h'.2
      show good (x :: ((y :: u') ++ v)) = true
      rw [List.cons_append]
      simp only [good, Bool.and_eq_true]
      exact ⟨h'.1, by rw [← List.cons_append]; exact h2⟩

/-- Every image block satisfies the invariant. This is where the arithmetic of
the substitution enters: `p1` occurs only in `s r4 = p1 p2 q1 q2`, followed by
`p2`, and ends no image. -/
theorem good_s (x : Letter) : good (s x) = true := by cases x <;> rfl

/-- **The invariant lemma (one step).** The image of ANY word satisfies the
invariant. -/
theorem good_S : ∀ w : List Letter, good (S w) = true
  | [] => rfl
  | x :: w => good_append (good_s x) (good_S w)

/-- **THE INVARIANT.** Every positive iterate from every seed satisfies it. -/
theorem good_iter (n : ℕ) (x : Letter) : good (S^[n + 1] [x]) = true := by
  rw [Function.iterate_succ_apply']
  exact good_S _

/-- Index form: in a `good` word the letter after any `p1` exists and is `p2`. -/
theorem good_getElem : ∀ {w : List Letter}, good w = true →
    ∀ i : ℕ, w[i]? = some p1 → w[i + 1]? = some p2 := by
  intro w
  induction w with
  | nil => intro _ i h; simp at h
  | cons x t ih =>
    intro hw i h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      cases t with
      | nil => exact absurd hw (by decide)
      | cons y t' =>
        have h' : okPair p1 y = true ∧ good (y :: t') = true := by
          simpa [good, Bool.and_eq_true] using hw
        have hy : y = p2 := by
          have h1 := h'.1
          revert h1
          cases y <;> decide
        subst hy
        rfl
    | succ j =>
      have h' : t[j]? = some p1 := by simpa using h
      have hres := ih (good_tail hw) j h'
      simpa using hres

/-- **EVERY `p1` IS FOLLOWED BY `p2`** — index form, every positive iterate,
every seed, every position. -/
theorem every_p1_followed_by_p2 (n : ℕ) (x : Letter) (i : ℕ)
    (h : (S^[n + 1] [x])[i]? = some p1) :
    (S^[n + 1] [x])[i + 1]? = some p2 :=
  good_getElem (good_iter n x) i h

/-! ## The chirality witness pair: `q2 p1` occurs, `p1 q2` never does -/

/-- A word containing the adjacency `p1 · q2` violates the invariant. -/
theorem not_good_p1q2 (p q : List Letter) :
    good (p ++ (p1 :: q2 :: q)) ≠ true := by
  induction p with
  | nil => simp [good, okPair]
  | cons z p' ih =>
    rw [List.cons_append]
    intro h
    exact ih (good_tail h)

/-- **`p1 q2` IS NOT A FACTOR** of any iterate from any seed — direct from the
invariant, with no enumeration on this side. -/
theorem p1q2_not_factor (n : ℕ) (x : Letter) :
    ¬ [p1, q2] <:+: S^[n] [x] := by
  cases n with
  | zero =>
    intro h
    have h2 := h.length_le
    rw [Function.iterate_zero_apply] at h2
    simp at h2
  | succ m =>
    rintro ⟨p, q, hpq⟩
    have hw := good_iter m x
    have he : p ++ (p1 :: q2 :: q) = S^[m + 1] [x] := by
      simpa [List.append_assoc] using hpq
    rw [← he] at hw
    exact not_good_p1q2 p q hw

/-- **`q2 p1` IS A FACTOR**: it occurs in the ninth iterate from seed `p3`. -/
theorem q2p1_factor : [q2, p1] <:+: S^[9] [p3] := by decide

/-! ### The invariant settles every pair `p1 · X`, not just `p1 q2`

`every_p1_followed_by_p2` forbids `p1 · X` for EVERY `X` other than `p2`. Six of
the thirty-three computed forbidden-reversal witnesses are of the form `X · p1`,
and for all six the forbidden side is settled here by the identical argument.
The remaining twenty-seven are not touched and stay computational. -/

theorem not_good_p1 (y : Letter) (hy : okPair p1 y = false) (p q : List Letter) :
    good (p ++ (p1 :: y :: q)) ≠ true := by
  induction p with
  | nil =>
    simp only [List.nil_append, good, Bool.and_eq_true, hy]
    simp
  | cons z p' ih =>
    rw [List.cons_append]
    intro h
    exact ih (good_tail h)

/-- **NO `p1 · X` IS A FACTOR** for any `X ≠ p2`, in any iterate from any seed. -/
theorem p1_pair_not_factor (y : Letter) (hy : okPair p1 y = false)
    (n : ℕ) (x : Letter) : ¬ [p1, y] <:+: S^[n] [x] := by
  cases n with
  | zero =>
    intro h
    have h2 := h.length_le
    rw [Function.iterate_zero_apply] at h2
    simp at h2
  | succ m =>
    rintro ⟨p, q, hpq⟩
    have hw := good_iter m x
    have he : p ++ (p1 :: y :: q) = S^[m + 1] [x] := by
      simpa [List.append_assoc] using hpq
    rw [← he] at hw
    exact not_good_p1 y hy p q hw

theorem p1q3_not_factor (n : ℕ) (x : Letter) : ¬ [p1, q3] <:+: S^[n] [x] :=
  p1_pair_not_factor q3 (by decide) n x

theorem p1q4_not_factor (n : ℕ) (x : Letter) : ¬ [p1, q4] <:+: S^[n] [x] :=
  p1_pair_not_factor q4 (by decide) n x

theorem p1r2_not_factor (n : ℕ) (x : Letter) : ¬ [p1, r2] <:+: S^[n] [x] :=
  p1_pair_not_factor r2 (by decide) n x

theorem p1r3_not_factor (n : ℕ) (x : Letter) : ¬ [p1, r3] <:+: S^[n] [x] :=
  p1_pair_not_factor r3 (by decide) n x

theorem p1r4_not_factor (n : ℕ) (x : Letter) : ¬ [p1, r4] <:+: S^[n] [x] :=
  p1_pair_not_factor r4 (by decide) n x

/-! ### Occurrence witnesses for the companions

Each forbidden pair `p1 · X` above has a reversal `X · p1` that DOES occur. Four
of the six (`q2 p1` above, and the three below) are cheap enough for the kernel
to decide; the seeds and iterates below are the minima over all twelve seeds.

The remaining two — `r3 p1` and `r4 p1` — have smallest witnesses of 315 and 128
letters, past what `decide` closes here. Compiled (native) evaluation is excluded
by this repository's axiom policy and is not used to reach them. Their occurrence
is established by computation only, and the entry says so rather than implying
six complete pairs. -/

theorem q3p1_factor : [q3, p1] <:+: S^[8] [p1] := by decide
theorem q4p1_factor : [q4, p1] <:+: S^[6] [p2] := by decide
theorem r2p1_factor : [r2, p1] <:+: S^[4] [q1] := by decide

/-- **CHIRALITY OF THE rhoQ SUBSTITUTION.** The witness pair: `q2 p1` is a factor
of an iterate while its reversal `p1 q2` is a factor of no iterate from any seed.
The factor language of the substitution whose inflation factor is `rhoQ` is not
closed under reversal. -/
theorem rhoQ_chirality (n : ℕ) (x : Letter) :
    ([q2, p1] <:+: S^[9] [p3]) ∧ ¬ [p1, q2] <:+: S^[n] [x] :=
  ⟨q2p1_factor, p1q2_not_factor n x⟩

end PdtRhoQ
