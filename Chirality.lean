import Mathlib

/-!
# Chirality — the Padovan factor language is chiral

The Padovan substitution on the three-letter alphabet `{a, b, c}` is
`s : a ↦ b, b ↦ c, c ↦ ab` (its incidence matrix has characteristic
polynomial `x³ − x − 1`; that fact is named here for orientation only and is
not used or proved in this module). `S` extends `s` to words, and the words
of interest are the iterates `S^[n] [x]` from a single-letter seed. This
module kernel-verifies the combinatorial core of the language-chirality
claim:

* **THE INVARIANT** (`good_iter`, `every_a_followed_by_b`): in every image
  word `S^[n+1] [x]` — any seed letter, any `n` — every occurrence of `a`
  is immediately followed by `b`. The engine is one observation: `a` is
  produced only inside the block `s c = ab`, where `b` follows it within
  the block, and no block ends in `a`, so concatenation creates no
  violation (`good_append`, `good_S`).
* **CHIRALITY WITNESS PAIR** (`chirality`): the word `ca` IS a factor of an
  iterate (`ca_factor`: it occurs in `S^[5] [a] = cab`), while `ac` is NOT
  a factor of any iterate from any seed (`ac_not_factor` — a consequence of
  the invariant, no enumeration). The factor language reads differently
  backwards.
* **FACTOR COMPLETENESS AT LENGTH ≤ 5** (`factors_complete`): the explicit
  57-word list `F5` contains every factor of length ≤ 5 of every iterate
  `S^[n] [a]`. The engine is the window lemma (`infix_window`): a factor of
  `S w` of length `L` is contained in the `S`-image of a factor of `w` of
  length ≤ `L`, because every block `s x` is nonempty; `F5` is closed under
  taking length-≤5 windows of images (`F5_closed`, by `decide`).
* **NO PALINDROMIC FACTOR OF LENGTH ≥ 4** (`no_long_palindromic_factor`):
  a palindrome of length ≥ 4 contains a palindromic factor of length 4 or 5
  (`palindrome_has_small_core`, by stripping the outer letters), and `F5`
  contains no palindrome of length 4 or 5 (`F5_no_palindrome`, by
  `decide`). Together with completeness this rules out every palindromic
  factor of length ≥ 4, for every `n`.

## Scope (what is proved here, and what is deliberately NOT)

* All statements are about the concrete substitution `s` on the inductive
  type `Letter` and its word iterates. The identification of this language
  with any physical reading (settled-record structure, direction of a
  history) is a separate interpretive claim and is **out of scope** here.
* `ac_not_factor` and the invariant quantify over every seed letter and
  every `n`. The completeness and palindrome results are stated for the
  seed `a` (the language of the canonical iterates); primitivity of the
  substitution — which would transfer them to any seed — is not formalized.
* `F5` is used as a certificate: `factors_complete` proves every length-≤5
  factor lies IN `F5` (the direction the palindrome theorem needs). That
  every member of `F5` actually occurs as a factor (no junk) is checked
  outside the kernel and is not needed by any theorem here.
-/

namespace Time
namespace Padovan

/-- The three-letter alphabet of the Padovan substitution. -/
inductive Letter : Type
  | a | b | c
deriving DecidableEq

open Letter

/-- The Padovan substitution `s : a ↦ b, b ↦ c, c ↦ ab`. The letter `a` is
produced only inside the block `s c = ab`, immediately followed by `b`;
no block ends in `a`. -/
def s : Letter → List Letter
  | a => [b]
  | b => [c]
  | c => [a, b]

/-- `S` applies the substitution letterwise to a word (concatenating the
image blocks). -/
def S : List Letter → List Letter
  | [] => []
  | x :: w => s x ++ S w

@[simp] theorem S_nil : S [] = [] := rfl

@[simp] theorem S_cons (x : Letter) (w : List Letter) : S (x :: w) = s x ++ S w := rfl

/-- Every image block is nonempty. -/
theorem one_le_length_s (x : Letter) : 1 ≤ (s x).length := by cases x <;> simp [s]

/-- Every image block has length at most 2. -/
theorem length_s_le (x : Letter) : (s x).length ≤ 2 := by cases x <;> simp [s]

/-- The image of a word is at most twice as long. -/
theorem length_S_le : ∀ w : List Letter, (S w).length ≤ 2 * w.length := by
  intro w
  induction w with
  | nil => simp
  | cons x w ih =>
    have hx := length_s_le x
    rw [S_cons, List.length_append, List.length_cons]
    omega

/-! ## The invariant: every `a` is immediately followed by `b` -/

/-- The pair condition: `a` must be followed by `b`; every other pair is
allowed. -/
def okPair : Letter → Letter → Bool
  | a, b => true
  | a, _ => false
  | _, _ => true

/-- The final-letter condition: a word may not end in `a`. -/
def okLast : Letter → Bool
  | a => false
  | _ => true

/-- `good w`: every occurrence of `a` in `w` is immediately followed by `b`
— in particular `w` does not end in `a`. Boolean, hence decidable. -/
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
  cases x
  · exact absurd h (by decide)
  · cases y <;> rfl
  · cases y <;> rfl

/-- **Concatenation preserves the invariant.** The only new adjacency in
`u ++ v` is (last of `u`, head of `v`), and `good u` forbids `u` ending in
`a`. -/
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

/-- Every image block satisfies the invariant. -/
theorem good_s (x : Letter) : good (s x) = true := by cases x <;> rfl

/-- **The invariant lemma (one step).** The image of ANY word satisfies the
invariant: every `a` in `S w` is immediately followed by `b`, and `S w`
does not end in `a`. -/
theorem good_S : ∀ w : List Letter, good (S w) = true
  | [] => rfl
  | x :: w => good_append (good_s x) (good_S w)

/-- **THE INVARIANT.** Every iterate `S^[n+1] [x]` — any seed letter `x`,
any `n ≥ 0` — satisfies the invariant. -/
theorem good_iter (n : ℕ) (x : Letter) : good (S^[n + 1] [x]) = true := by
  rw [Function.iterate_succ_apply']
  exact good_S _

/-- Index form of the invariant: in a `good` word, the letter after any
occurrence of `a` exists and is `b`. -/
theorem good_getElem : ∀ {w : List Letter}, good w = true →
    ∀ i : ℕ, w[i]? = some Letter.a → w[i + 1]? = some Letter.b := by
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
        have h' : okPair Letter.a y = true ∧ good (y :: t') = true := by
          simpa [good, Bool.and_eq_true] using hw
        have hy : y = Letter.b := by
          have h1 := h'.1
          cases y
          · exact absurd h1 (by decide)
          · rfl
          · exact absurd h1 (by decide)
        subst hy
        rfl
    | succ j =>
      have h' : t[j]? = some Letter.a := by simpa using h
      have hres := ih (good_tail hw) j h'
      simpa using hres

/-- **EVERY `a` IS FOLLOWED BY `b`** — the headline index form, for every
iterate `S^[n+1] [x]`, every seed letter, every position. In particular no
iterate ends in `a`, and neither `aa` nor `ac` ever occurs. -/
theorem every_a_followed_by_b (n : ℕ) (x : Letter) (i : ℕ)
    (h : (S^[n + 1] [x])[i]? = some Letter.a) :
    (S^[n + 1] [x])[i + 1]? = some Letter.b :=
  good_getElem (good_iter n x) i h

/-! ## The chirality witness pair: `ca` occurs, `ac` never does -/

/-- A word containing the adjacency `a·c` violates the invariant. -/
theorem not_good_ac (p q : List Letter) :
    good (p ++ (Letter.a :: Letter.c :: q)) ≠ true := by
  induction p with
  | nil => simp [good, okPair]
  | cons z p' ih =>
    rw [List.cons_append]
    intro h
    exact ih (good_tail h)

/-- **`ac` IS NOT A FACTOR** of any iterate `S^[n] [x]`, for any seed
letter and any `n` — direct from the invariant, no enumeration. -/
theorem ac_not_factor (n : ℕ) (x : Letter) :
    ¬ [Letter.a, Letter.c] <:+: S^[n] [x] := by
  cases n with
  | zero =>
    intro h
    have h2 := h.length_le
    rw [Function.iterate_zero_apply] at h2
    simp at h2
  | succ m =>
    rintro ⟨p, q, hpq⟩
    have hw := good_iter m x
    have he : p ++ (Letter.a :: Letter.c :: q) = S^[m + 1] [x] := by
      simpa [List.append_assoc] using hpq
    rw [← he] at hw
    exact not_good_ac p q hw

/-- The fifth iterate from seed `a` is the word `cab`. -/
theorem iterate_five : S^[5] [Letter.a] = [Letter.c, Letter.a, Letter.b] := by decide

/-- **`ca` IS A FACTOR**: it occurs in `S^[5] [a] = cab`. -/
theorem ca_factor : [Letter.c, Letter.a] <:+: S^[5] [Letter.a] := by
  rw [iterate_five]
  exact ⟨[], [Letter.b], rfl⟩

/-- **CHIRALITY.** The witness pair: `ca` is a factor of an iterate while
its reversal `ac` is a factor of no iterate from any seed. The factor
language of the Padovan substitution is not closed under reversal. -/
theorem chirality (n : ℕ) (x : Letter) :
    ([Letter.c, Letter.a] <:+: S^[5] [Letter.a]) ∧
      ¬ [Letter.a, Letter.c] <:+: S^[n] [x] :=
  ⟨ca_factor, ac_not_factor n x⟩

/-! ## The window lemma: factors of images come from short factors -/

/-- Splitting an infix across an append: an infix of `l₁ ++ l₂` is an infix
of `l₁`, an infix of `l₂`, or splits as a nonempty suffix of `l₁` followed
by a prefix of `l₂`. -/
theorem infix_append_split {α : Type*} {u l₁ l₂ : List α} (h : u <:+: l₁ ++ l₂) :
    u <:+: l₁ ∨ u <:+: l₂ ∨
      ∃ u₁ u₂, u = u₁ ++ u₂ ∧ 1 ≤ u₁.length ∧ u₁ <:+ l₁ ∧ u₂ <+: l₂ := by
  obtain ⟨p, q, hpq⟩ := h
  by_cases hA : p.length + u.length ≤ l₁.length
  · left
    have htake := congrArg (List.take l₁.length) hpq
    rw [List.take_left] at htake
    rw [List.take_append, List.take_append] at htake
    have hp1 : p.length ≤ l₁.length := by omega
    have hp2 : u.length ≤ l₁.length - p.length := by omega
    rw [List.take_of_length_le hp1, List.take_of_length_le hp2] at htake
    exact ⟨p, _, htake⟩
  · by_cases hB : l₁.length ≤ p.length
    · right; left
      have hdrop := congrArg (List.drop l₁.length) hpq
      rw [List.drop_left] at hdrop
      rw [List.drop_append, List.drop_append] at hdrop
      have e1 : l₁.length - p.length = 0 := by omega
      have e2 : l₁.length - (p ++ u).length = 0 := by
        simp only [List.length_append]; omega
      rw [e1, e2] at hdrop
      simp only [List.drop_zero] at hdrop
      exact ⟨p.drop l₁.length, q, hdrop⟩
    · right; right
      refine ⟨u.take (l₁.length - p.length), u.drop (l₁.length - p.length),
        (List.take_append_drop _ u).symm, ?_, ?_, ?_⟩
      · rw [List.length_take]; omega
      · have htake := congrArg (List.take l₁.length) hpq
        rw [List.take_left] at htake
        rw [List.take_append, List.take_append] at htake
        have hp1 : p.length ≤ l₁.length := by omega
        have e2 : l₁.length - (p ++ u).length = 0 := by
          simp only [List.length_append]; omega
        rw [List.take_of_length_le hp1, e2] at htake
        simp only [List.take_zero, List.append_nil] at htake
        exact ⟨p, htake⟩
      · have hdrop := congrArg (List.drop l₁.length) hpq
        rw [List.drop_left] at hdrop
        rw [List.drop_append, List.drop_append] at hdrop
        have e2 : l₁.length - (p ++ u).length = 0 := by
          simp only [List.length_append]; omega
        have hp1 : p.length ≤ l₁.length := by omega
        rw [e2, List.drop_eq_nil_of_le hp1] at hdrop
        simp only [List.drop_zero, List.nil_append] at hdrop
        exact ⟨q, hdrop⟩

/-- **Prefix window lemma.** A prefix of `S w` is a prefix of the image of
a prefix of `w` that is no longer than it — because every block `s x` is
nonempty. -/
theorem prefix_window : ∀ (w u : List Letter), u <+: S w →
    ∃ v, v <+: w ∧ v.length ≤ u.length ∧ u <+: S v := by
  intro w
  induction w with
  | nil =>
    intro u hu
    rw [S_nil, List.prefix_nil] at hu
    subst hu
    exact ⟨[], List.nil_prefix, le_refl 0, List.nil_prefix⟩
  | cons x w' ih =>
    intro u hu
    rw [S_cons] at hu
    by_cases hlen : u.length ≤ (s x).length
    · have hux : u <+: s x :=
        List.prefix_of_prefix_length_le hu (List.prefix_append _ _) hlen
      rcases eq_or_ne u [] with rfl | hne
      · exact ⟨[], List.nil_prefix, by simp, List.nil_prefix⟩
      · have hpos : 0 < u.length := List.length_pos_iff.mpr hne
        refine ⟨[x], ⟨w', rfl⟩, ?_, ?_⟩
        · simp only [List.length_cons, List.length_nil]; omega
        · rw [S_cons, S_nil, List.append_nil]
          exact hux
    · have hlen' : (s x).length ≤ u.length := by omega
      have hsx : s x <+: u :=
        List.prefix_of_prefix_length_le (List.prefix_append _ _) hu hlen'
      obtain ⟨u₂, rfl⟩ := hsx
      have hu₂ : u₂ <+: S w' := (List.prefix_append_right_inj (s x)).1 hu
      obtain ⟨v', hv'p, hv'len, hv'⟩ := ih u₂ hu₂
      refine ⟨x :: v', ?_, ?_, ?_⟩
      · exact List.cons_prefix_cons.2 ⟨rfl, hv'p⟩
      · have h1 := one_le_length_s x
        simp only [List.length_cons, List.length_append]
        omega
      · rw [S_cons]
        exact (List.prefix_append_right_inj (s x)).2 hv'

/-- **Infix window lemma.** A nonempty factor of `S w` is a factor of the
image of a factor of `w` that is no longer than it. -/
theorem infix_window : ∀ (w u : List Letter), u <:+: S w →
    u = [] ∨ ∃ v, v <:+: w ∧ v.length ≤ u.length ∧ u <:+: S v := by
  intro w
  induction w with
  | nil =>
    intro u hu
    rw [S_nil, List.infix_nil] at hu
    exact Or.inl hu
  | cons x w' ih =>
    intro u hu
    rcases eq_or_ne u [] with rfl | hne
    · exact Or.inl rfl
    right
    rw [S_cons] at hu
    have hpos : 0 < u.length := List.length_pos_iff.mpr hne
    rcases infix_append_split hu with h | h | ⟨u₁, u₂, rfl, h1len, h1suf, h2pre⟩
    · refine ⟨[x], ⟨[], w', rfl⟩, ?_, ?_⟩
      · simp only [List.length_cons, List.length_nil]; omega
      · rw [S_cons, S_nil, List.append_nil]
        exact h
    · rcases ih u h with rfl | ⟨v, ⟨pv, qv, hpv⟩, hvlen, huv⟩
      · exact absurd rfl hne
      · exact ⟨v, ⟨x :: pv, qv, by rw [List.cons_append, List.cons_append, hpv]⟩,
          hvlen, huv⟩
    · obtain ⟨v₂, hv₂p, hv₂len, hv₂⟩ := prefix_window w' u₂ h2pre
      obtain ⟨t, ht⟩ := hv₂p
      refine ⟨x :: v₂, ⟨[], t, by rw [List.nil_append, List.cons_append, ht]⟩, ?_, ?_⟩
      · simp only [List.length_cons, List.length_append]
        omega
      · rw [S_cons]
        obtain ⟨p, hp⟩ := h1suf
        obtain ⟨r, hr⟩ := hv₂
        exact ⟨p, r, by rw [← hp, ← hr]; simp [List.append_assoc]⟩

/-! ## Factor completeness at length ≤ 5, and no long palindromic factor -/

/-- The 57 words of length ≤ 5 over `{a,b,c}` forming the length-≤5 factor
certificate: it contains every length-≤5 factor of every `S^[n] [a]`
(`factors_complete`), because it contains the seed's factors and is closed
under length-≤5 windows of images (`F5_closed`). -/
def F5 : List (List Letter) :=
  [[],
  [a], [b], [c],
  [a, b], [b, a], [b, b], [b, c], [c, a], [c, b], [c, c],
  [a, b, a], [a, b, b], [a, b, c], [b, a, b], [b, b, c], [b, c, a],
  [b, c, b], [b, c, c], [c, a, b], [c, b, c], [c, c, a],
  [a, b, a, b], [a, b, b, c], [a, b, c, a], [b, a, b, b], [b, b, c, a],
  [b, b, c, b], [b, b, c, c], [b, c, a, b], [b, c, b, c], [b, c, c, a],
  [c, a, b, a], [c, a, b, b], [c, a, b, c], [c, b, c, c], [c, c, a, b],
  [a, b, a, b, b], [a, b, b, c, a], [a, b, b, c, b], [a, b, b, c, c],
  [a, b, c, a, b], [b, a, b, b, c], [b, b, c, a, b], [b, b, c, b, c],
  [b, b, c, c, a], [b, c, a, b, a], [b, c, a, b, b], [b, c, b, c, c],
  [b, c, c, a, b], [c, a, b, a, b], [c, a, b, b, c], [c, a, b, c, a],
  [c, b, c, c, a], [c, c, a, b, a], [c, c, a, b, b], [c, c, a, b, c]]

/-- Every certificate word has length at most 5. -/
theorem F5_short : ∀ v ∈ F5, v.length ≤ 5 := by decide

/-- **Closure**: every length-≤5 window of the image of a certificate word
is again a certificate word. -/
theorem F5_closed : ∀ v ∈ F5, ∀ i < 11, ∀ j < 6, ((S v).drop i).take j ∈ F5 := by
  decide

/-- A short factor of the image of a certificate word is a certificate
word. -/
theorem mem_F5_of_infix {v u : List Letter} (hv : v ∈ F5) (huv : u <:+: S v)
    (hlen : u.length ≤ 5) : u ∈ F5 := by
  have hvlen : v.length ≤ 5 := F5_short v hv
  have hSv : (S v).length ≤ 10 := le_trans (length_S_le v) (by omega)
  obtain ⟨p, q, hpq⟩ := huv
  have hplen : p.length ≤ (S v).length := by
    have hl := congrArg List.length hpq
    simp only [List.length_append] at hl
    omega
  have hdrop : (S v).drop p.length = u ++ q := by
    rw [← hpq, List.append_assoc, List.drop_left]
  have htake : (u ++ q).take u.length = u := List.take_left
  have hmem := F5_closed v hv p.length (by omega) u.length (by omega)
  rw [hdrop, htake] at hmem
  exact hmem

/-- **FACTOR COMPLETENESS AT LENGTH ≤ 5.** Every factor of length ≤ 5 of
every iterate `S^[n] [a]` is a certificate word. -/
theorem factors_complete : ∀ (n : ℕ) (u : List Letter),
    u <:+: S^[n] [Letter.a] → u.length ≤ 5 → u ∈ F5 := by
  intro n
  induction n with
  | zero =>
    intro u hu _
    rw [Function.iterate_zero_apply] at hu
    have hlen := hu.length_le
    cases u with
    | nil => decide
    | cons x t =>
      cases t with
      | nil =>
        have hx : x ∈ ([Letter.a] : List Letter) :=
          List.IsInfix.mem (List.mem_singleton_self x) hu
        rw [List.mem_singleton] at hx
        subst hx
        decide
      | cons y t' =>
        simp only [List.length_cons, List.length_nil] at hlen
        omega
  | succ m ih =>
    intro u hu hlen
    rw [Function.iterate_succ_apply'] at hu
    rcases infix_window (S^[m] [Letter.a]) u hu with rfl | ⟨v, hvinf, hvlen, huv⟩
    · decide
    · exact mem_F5_of_infix (ih v hvinf (le_trans hvlen hlen)) huv hlen

/-- **The certificate has no palindrome of length 4 or 5** (`decide` over
the 57 words). -/
theorem F5_no_palindrome : ∀ t ∈ F5, t.length = 4 ∨ t.length = 5 →
    t.reverse ≠ t := by decide

/-- **Every palindrome of length ≥ 4 contains a palindromic factor of
length 4 or 5** — strip the outer letters (the `cons_concat` structure of
`List.Palindrome`) until the length falls to 4 or 5. -/
theorem palindrome_has_small_core :
    ∀ (N : ℕ) (u : List Letter), u.length ≤ N → u.Palindrome → 4 ≤ u.length →
      ∃ t, t <:+: u ∧ t.Palindrome ∧ (t.length = 4 ∨ t.length = 5) := by
  intro N
  induction N with
  | zero =>
    intro u hle _ hlen
    omega
  | succ M ih =>
    intro u hle hp hlen
    cases hp with
    | nil => simp at hlen
    | singleton x => simp at hlen
    | @cons_concat x l hl =>
      by_cases hsmall : l.length ≤ 3
      · refine ⟨_, List.infix_rfl, List.Palindrome.cons_concat x hl, ?_⟩
        simp only [List.length_cons, List.length_append, List.length_nil] at hlen ⊢
        omega
      · have hlink : l <:+: x :: (l ++ [x]) := ⟨[x], [x], rfl⟩
        have hlen' : l.length ≤ M := by
          simp only [List.length_cons, List.length_append, List.length_nil] at hle
          omega
        obtain ⟨t, htl, htp, hts⟩ := ih l hlen' hl (by omega)
        exact ⟨t, htl.trans hlink, htp, hts⟩

/-- **NO PALINDROMIC FACTOR OF LENGTH ≥ 4.** No iterate `S^[n] [a]` has a
palindromic factor of length ≥ 4: such a palindrome would contain a
palindromic factor of length 4 or 5 (`palindrome_has_small_core`), which
would be a certificate word (`factors_complete`) — and the certificate has
none (`F5_no_palindrome`). -/
theorem no_long_palindromic_factor (n : ℕ) (u : List Letter)
    (hu : u <:+: S^[n] [Letter.a]) (hlen : 4 ≤ u.length) : ¬ u.Palindrome := by
  intro hp
  obtain ⟨t, htu, htp, hts⟩ := palindrome_has_small_core u.length u le_rfl hp hlen
  have htS : t <:+: S^[n] [Letter.a] := htu.trans hu
  have htF : t ∈ F5 := factors_complete n t htS (by omega)
  exact F5_no_palindrome t htF hts htp.reverse_eq

end Padovan

end Time

/-! ### Axiom audit -/

#print axioms Time.Padovan.S_nil
#print axioms Time.Padovan.S_cons
#print axioms Time.Padovan.one_le_length_s
#print axioms Time.Padovan.length_s_le
#print axioms Time.Padovan.length_S_le
#print axioms Time.Padovan.good_tail
#print axioms Time.Padovan.okPair_of_okLast
#print axioms Time.Padovan.good_append
#print axioms Time.Padovan.good_s
#print axioms Time.Padovan.good_S
#print axioms Time.Padovan.good_iter
#print axioms Time.Padovan.good_getElem
#print axioms Time.Padovan.every_a_followed_by_b
#print axioms Time.Padovan.not_good_ac
#print axioms Time.Padovan.ac_not_factor
#print axioms Time.Padovan.iterate_five
#print axioms Time.Padovan.ca_factor
#print axioms Time.Padovan.chirality
#print axioms Time.Padovan.infix_append_split
#print axioms Time.Padovan.prefix_window
#print axioms Time.Padovan.infix_window
#print axioms Time.Padovan.F5_short
#print axioms Time.Padovan.F5_closed
#print axioms Time.Padovan.mem_F5_of_infix
#print axioms Time.Padovan.factors_complete
#print axioms Time.Padovan.F5_no_palindrome
#print axioms Time.Padovan.palindrome_has_small_core
#print axioms Time.Padovan.no_long_palindromic_factor
