import Chirality

/-!
# Solution: proved versions of the Challenge declarations

Each public declaration below has exactly the statement of its
`Challenge.lean` counterpart. The proofs are supplied by the project module
`Chirality` (namespace `Time.Padovan`), transported across the letter
encoding `Letter ≃ Fin 3`. The all-seed palindrome theorem reduces every
seed to the seed-`a` case: `S [0] = [1]` and `S [1] = [2]`, so an iterate
from seed `1` or `2` IS a seed-`0` iterate of shifted index.
-/

namespace ArithmeticOfTime

/-- The Padovan substitution on `Fin 3` (matches the Challenge definition). -/
def s : Fin 3 → List (Fin 3)
  | 0 => [1]
  | 1 => [2]
  | 2 => [0, 1]

/-- Letterwise application of the substitution (matches the Challenge). -/
def S (w : List (Fin 3)) : List (Fin 3) := (w.map s).flatten


private def enc : Time.Padovan.Letter → Fin 3
  | .a => 0
  | .b => 1
  | .c => 2

private def dec : Fin 3 → Time.Padovan.Letter
  | 0 => .a
  | 1 => .b
  | 2 => .c

private lemma dec_enc (x : Time.Padovan.Letter) : dec (enc x) = x := by
  cases x <;> rfl

private lemma enc_dec (y : Fin 3) : enc (dec y) = y := by
  fin_cases y <;> rfl

private lemma dec_comp_enc : dec ∘ enc = id := funext dec_enc

private lemma s_enc (x : Time.Padovan.Letter) :
    s (enc x) = (Time.Padovan.s x).map enc := by
  cases x <;> rfl

private lemma S_map_enc (w : List Time.Padovan.Letter) :
    S (w.map enc) = (Time.Padovan.S w).map enc := by
  induction w with
  | nil => rfl
  | cons x w ih =>
      simp only [List.map_cons, S, List.flatten_cons, Time.Padovan.S_cons,
        List.map_append]
      rw [s_enc]
      simp only [S] at ih
      rw [ih]

private lemma iter_map_enc (n : ℕ) (w : List Time.Padovan.Letter) :
    S^[n] (w.map enc) = (Time.Padovan.S^[n] w).map enc := by
  induction n generalizing w with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, S_map_enc, ih]

private lemma iter_single (n : ℕ) (x : Fin 3) :
    S^[n] [x] = (Time.Padovan.S^[n] [dec x]).map enc := by
  have h := iter_map_enc n [dec x]
  simpa [enc_dec] using h

/-! ### Seed shifting: every seed's iterate is a seed-`0` iterate

`S [0] = [1]` and `S [1] = [2]`, so `S^[n] [1] = S^[n+1] [0]` and
`S^[n] [2] = S^[n+2] [0]`: the words from seeds `1` and `2` are seed-`0`
words of shifted index. -/

private lemma S_seed_zero : S [(0 : Fin 3)] = [1] := by decide

private lemma S_seed_one : S [(1 : Fin 3)] = [2] := by decide

private lemma iter_seed_one (n : ℕ) : S^[n] [(1 : Fin 3)] = S^[n + 1] [0] := by
  rw [Function.iterate_succ_apply, S_seed_zero]

private lemma iter_seed_two (n : ℕ) : S^[n] [(2 : Fin 3)] = S^[n + 2] [0] := by
  show S^[n] [(2 : Fin 3)] = S^[n + 1 + 1] [0]
  rw [Function.iterate_succ_apply, S_seed_zero,
    Function.iterate_succ_apply, S_seed_one]

theorem padovan_a_forces_b (n : ℕ) (x : Fin 3) (i : ℕ)
    (h : (S^[n + 1] [x])[i]? = some 0) :
    (S^[n + 1] [x])[i + 1]? = some 1 := by
  rw [iter_single] at h ⊢
  rw [List.getElem?_map] at h ⊢
  cases hli : (Time.Padovan.S^[n + 1] [dec x])[i]? with
  | none => rw [hli] at h; simp at h
  | some y =>
      rw [hli] at h
      simp only [Option.map_some] at h
      have hy : y = Time.Padovan.Letter.a := by
        cases y <;> first | rfl | (exfalso; simp [enc] at h)
      subst hy
      have hb := Time.Padovan.every_a_followed_by_b n (dec x) i hli
      rw [hb]
      rfl

theorem padovan_chirality (n : ℕ) (x : Fin 3) :
    ([2, 0] <:+: S^[5] [0]) ∧ ¬ [0, 2] <:+: S^[n] [x] := by
  constructor
  · decide
  · intro hinf
    rw [iter_single] at hinf
    obtain ⟨s', t', hst⟩ := hinf
    apply Time.Padovan.ac_not_factor n (dec x)
    refine ⟨s'.map dec, t'.map dec, ?_⟩
    have hmap := congrArg (List.map dec) hst
    simpa [List.map_append, List.map_map, dec_comp_enc, dec] using hmap

/-- The seed-`0` case, transported from `Time.Padovan.no_long_palindromic_factor`
across the letter encoding. -/
private lemma no_long_palindrome_seed_zero (n : ℕ) (u : List (Fin 3))
    (hu : u <:+: S^[n] [0]) (hlen : 4 ≤ u.length) : ¬ u.Palindrome := by
  intro hp
  rw [iter_single] at hu
  obtain ⟨s', t', hst⟩ := hu
  have hu' : u.map dec <:+: Time.Padovan.S^[n] [dec 0] := by
    refine ⟨s'.map dec, t'.map dec, ?_⟩
    have hmap := congrArg (List.map dec) hst
    simpa [List.map_append, List.map_map, dec_comp_enc] using hmap
  exact Time.Padovan.no_long_palindromic_factor n (u.map dec) hu'
    (by simpa using hlen) (hp.map dec)

theorem padovan_no_long_palindrome (n : ℕ) (x : Fin 3) (u : List (Fin 3))
    (hu : u <:+: S^[n] [x]) (hlen : 4 ≤ u.length) : ¬ u.Palindrome := by
  rcases x with ⟨xv, hx⟩
  interval_cases xv
  · exact no_long_palindrome_seed_zero n u hu hlen
  · have hu' : u <:+: S^[n] [(1 : Fin 3)] := hu
    rw [iter_seed_one] at hu'
    exact no_long_palindrome_seed_zero (n + 1) u hu' hlen
  · have hu' : u <:+: S^[n] [(2 : Fin 3)] := hu
    rw [iter_seed_two] at hu'
    exact no_long_palindrome_seed_zero (n + 2) u hu' hlen

end ArithmeticOfTime

/-! ### Axiom audit (in-module): the three compared theorems -/

#print axioms ArithmeticOfTime.padovan_a_forces_b
#print axioms ArithmeticOfTime.padovan_chirality
#print axioms ArithmeticOfTime.padovan_no_long_palindrome
