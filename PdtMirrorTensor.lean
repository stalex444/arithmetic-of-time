/-
# Mirroring a tensor of substitutions reverses its language

A computational MIRROR TEST (not part of this repository) attributed the
handedness of the 12-letter `rhoQ` object to its two founding polynomials by
mirroring one factor at a time and counting which one-way pairs flip: 20 flip
with the cubic, 18 with the quartic, 5 with both, and — the headline — ZERO
survive both mirrors, read as "the construction manufactures nothing". That was
an exhaustive finite computation on one stabilised language.

This file proves the general statement underneath it, for EVERY substitution on
EVERY alphabet, with no enumeration:

  `mir sigma x = (sigma x).reverse`, and `tens` is the row-major product.

  L1  `sub (mir sigma) w.reverse = (sub sigma w).reverse`
  L2  `tens (mir sigma) (mir tau) = mir (tens sigma tau)`
  T   `(sub (tens (mir sigma) (mir tau)))^[n] [z] = ((sub (tens sigma tau))^[n] [z]).reverse`

So mirroring BOTH factors reverses the tensor's whole language, at every iterate,
from every seed. The construction is EQUIVARIANT under mirroring.

TWO CONSEQUENCES, AND THEY PULL IN OPPOSITE DIRECTIONS.

`not_oneWay_both` — the sharp one, and it is bad news for how the mirror test
read its own table. Substituting `sigma := mir sigma` in T gives
`L(sigma, mir tau) = reverse L(mir sigma, tau)`: the two SINGLE-mirrored systems
have mutually reversed languages. Hence no word can be one-way in both of them,
so the "survives both mirrors" cell of the mirror-test table is EMPTY FOR EVERY PAIR
OF SUBSTITUTIONS WHATEVER. Its being empty for the `rhoQ` object is a theorem
about the tensor construction, not a measurement of that object, and cannot be
evidence that the object's handedness is inherited. (Checked: the same test
returns 0 for Fibonacci-tensor-Fibonacci, whose factors have reversal-closed
languages.)

`palindromic_reversal_closed` — the one that survives. If BOTH substitution
rules are palindromic (`mir sigma = sigma`), then every iterate of the tensor is
a palindrome and its factor set is closed under reversal. So the construction
genuinely cannot create handedness out of mirror-symmetric rules: chirality in
the product requires an asymmetric rule in a factor. That is the defensible form
of "nothing is manufactured", and it is much weaker than the test's headline — it
constrains the RULES, and says nothing about whether the factors' own LANGUAGES
were chiral.

WHAT IS NOT PROVED HERE. Which factor controls a given pair — the 20/18/5 split
— is not forced by this theorem and stays a computation. That the union of the
two columns is everything IS forced. And the theorem covers the row-major
product (column-major follows by swapping the factors); the other substitutions
with the same incidence matrix (other letter orders within the images) are
outside its scope.
-/

module
public import Mathlib

@[expose] public section

namespace PdtMirror

variable {A B : Type*}

/-! ## Substitutions and their mirrors -/

/-- Letterwise application of a substitution to a word. -/
def sub (s : A → List A) : List A → List A
  | [] => []
  | x :: w => s x ++ sub s w

@[simp] theorem sub_nil (s : A → List A) : sub s [] = [] := rfl

@[simp] theorem sub_cons (s : A → List A) (x : A) (w : List A) :
    sub s (x :: w) = s x ++ sub s w := rfl

theorem sub_append (s : A → List A) (u v : List A) :
    sub s (u ++ v) = sub s u ++ sub s v := by
  induction u with
  | nil => simp
  | cons x xs ih => simp [ih, List.append_assoc]

/-- The mirror of a substitution: every image word read backwards. -/
def mir (s : A → List A) : A → List A := fun x => (s x).reverse

@[simp] theorem mir_mir (s : A → List A) : mir (mir s) = s := by
  funext x; simp [mir]

/-! ## L1 — a mirrored substitution acts on the reversed word -/

/-- **Lemma 1.** Applying the mirrored substitution to the reversed word gives
the reverse of applying the original substitution to the word. -/
theorem sub_mir_reverse (s : A → List A) (w : List A) :
    sub (mir s) w.reverse = (sub s w).reverse := by
  induction w with
  | nil => simp
  | cons x xs ih =>
      simp [List.reverse_cons, sub_append, ih, mir]

/-- **Lemma 1, iterated.** Every iterate of the mirrored substitution on the
reversed word is the reverse of the corresponding iterate of the original. -/
theorem iterate_mir_reverse (s : A → List A) (n : ℕ) (w : List A) :
    (sub (mir s))^[n] w.reverse = ((sub s)^[n] w).reverse := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        sub_mir_reverse, ih]

/-- A one-letter seed is its own reversal, so the iterates of a mirrored
substitution from a seed reverse the iterates of the original from that seed. -/
theorem iterate_mir_seed (s : A → List A) (n : ℕ) (x : A) :
    (sub (mir s))^[n] [x] = ((sub s)^[n] [x]).reverse := by
  have := iterate_mir_reverse s n [x]; simpa using this

/-! ## L2 — the tensor commutes with mirroring -/

/-- The row-major tensor of two substitutions, on the product alphabet. -/
def tens (s : A → List A) (t : B → List B) : A × B → List (A × B) :=
  fun p => (s p.1).flatMap (fun x => (t p.2).map (fun y => (x, y)))

private theorem reverse_flatMap (l : List A) (f : A → List B) :
    (l.flatMap f).reverse = l.reverse.flatMap (fun x => (f x).reverse) := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, List.reverse_append, ih]

/-- **Lemma 2.** The tensor of the two mirrors is the mirror of the tensor:
reversing both factors' images reverses the product image exactly. -/
theorem tens_mir (s : A → List A) (t : B → List B) :
    tens (mir s) (mir t) = mir (tens s t) := by
  funext p
  simp [tens, mir, reverse_flatMap]

/-! ## The theorem -/

/-- **Mirror equivariance of the tensor.** Mirroring both factors reverses every
iterate of the product substitution, from every seed. -/
theorem iterate_tens_mir (s : A → List A) (t : B → List B) (n : ℕ) (z : A × B) :
    (sub (tens (mir s) (mir t)))^[n] [z] = ((sub (tens s t))^[n] [z]).reverse := by
  rw [tens_mir]; exact iterate_mir_seed (tens s t) n z

/-- Factor form: the words occurring in the double-mirrored system are exactly
the reversals of the words occurring in the original. -/
theorem infix_tens_mir (s : A → List A) (t : B → List B) (n : ℕ) (z : A × B)
    (u : List (A × B)) :
    u <:+: (sub (tens (mir s) (mir t)))^[n] [z] ↔
      u.reverse <:+: (sub (tens s t))^[n] [z] := by
  rw [iterate_tens_mir, ← List.reverse_infix, List.reverse_reverse]

/-! ## What the equivariance costs the mirror test -/

/-- `u` is ONE-WAY for the substitution `T` when it occurs in some iterate from
some seed and its reversal occurs in none. This is the IDEALISED predicate,
quantified over all seeds and all depths. The mirror-test table computes a weaker,
per-seed and per-depth version; that one is handled by `not_oneWayAt_both`
below, which is the statement that actually forces its table's cell empty. -/
def OneWay {C : Type*} (T : C → List C) (u : List C) : Prop :=
  (∃ n z, u <:+: (sub T)^[n] [z]) ∧ (∀ n z, ¬ u.reverse <:+: (sub T)^[n] [z])

/-- Mirroring one factor and mirroring the other give mutually reversed
languages. -/
theorem infix_single_mirrors (s : A → List A) (t : B → List B) (n : ℕ)
    (z : A × B) (u : List (A × B)) :
    u <:+: (sub (tens s (mir t)))^[n] [z] ↔
      u.reverse <:+: (sub (tens (mir s) t))^[n] [z] := by
  have h := infix_tens_mir (mir s) t n z u
  rwa [mir_mir] at h

/-- **The cost.** No word is one-way in BOTH single-mirrored systems — for any
two substitutions on any alphabets. The "survives both mirrors" cell of the
mirror-test table is empty by construction, so its emptiness for the `rhoQ` object is
not evidence about that object. -/
theorem not_oneWay_both (s : A → List A) (t : B → List B) (u : List (A × B)) :
    ¬ (OneWay (tens (mir s) t) u ∧ OneWay (tens s (mir t)) u) := by
  rintro ⟨⟨⟨n, z, hz⟩, -⟩, -, hno⟩
  exact hno n z ((infix_single_mirrors s t n z u.reverse).2 (by simpa using hz))

/-- **The cost, at the level the test computes.** At ONE fixed depth `n` and seed
`z`, no word can occur in the `s`-mirrored iterate with its reversal absent AND
occur in the `t`-mirrored iterate with its reversal absent. The mirror-test table
compares length-2 factor sets of single words at a stabilisation depth, so this —
not `not_oneWay_both` — is the theorem that forces its "survives both mirrors"
cell empty, for any two substitutions on any alphabets. -/
theorem not_oneWayAt_both (s : A → List A) (t : B → List B) (n : ℕ) (z : A × B)
    (u : List (A × B)) :
    ¬ ((u <:+: (sub (tens (mir s) t))^[n] [z] ∧
        ¬ u.reverse <:+: (sub (tens (mir s) t))^[n] [z]) ∧
       (u <:+: (sub (tens s (mir t)))^[n] [z] ∧
        ¬ u.reverse <:+: (sub (tens s (mir t)))^[n] [z])) := by
  rintro ⟨⟨-, hC⟩, hQ, -⟩
  exact hC ((infix_single_mirrors s t n z u).1 hQ)

/-- Corollary in factor-set form: at every depth and seed the two single-mirrored
iterates are exact reversals of one another. -/
theorem single_mirrors_reverse (s : A → List A) (t : B → List B) (n : ℕ) (z : A × B) :
    (sub (tens s (mir t)))^[n] [z] = ((sub (tens (mir s) t))^[n] [z]).reverse := by
  have h := iterate_tens_mir (mir s) t n z
  rwa [mir_mir] at h

/-! ## What survives: the construction manufactures nothing from symmetric rules -/

/-- **No manufacture.** If both substitution rules are palindromic, every
iterate of the tensor is a palindrome, so its factor set is closed under
reversal: the product cannot create handedness out of mirror-symmetric rules. -/
theorem palindromic_reversal_closed (s : A → List A) (t : B → List B)
    (hs : ∀ x, (s x).reverse = s x) (ht : ∀ y, (t y).reverse = t y)
    (n : ℕ) (z : A × B) (u : List (A × B)) :
    u <:+: (sub (tens s t))^[n] [z] ↔
      u.reverse <:+: (sub (tens s t))^[n] [z] := by
  have hms : mir s = s := by funext x; exact hs x
  have hmt : mir t = t := by funext y; exact ht y
  have h := infix_tens_mir s t n z u.reverse
  rw [hms, hmt, List.reverse_reverse] at h
  exact h.symm

/-- The palindrome itself, stated separately: with both rules mirror-symmetric
every iterate of the product reads the same in both directions. -/
theorem palindromic_iterate (s : A → List A) (t : B → List B)
    (hs : ∀ x, (s x).reverse = s x) (ht : ∀ y, (t y).reverse = t y)
    (n : ℕ) (z : A × B) :
    ((sub (tens s t))^[n] [z]).reverse = (sub (tens s t))^[n] [z] := by
  have hms : mir s = s := by funext x; exact hs x
  have hmt : mir t = t := by funext y; exact ht y
  have h := iterate_tens_mir s t n z
  rw [hms, hmt] at h
  exact h.symm

end PdtMirror
