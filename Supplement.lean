module
public import Solution
public import PdtMirrorTensor
public import PdtFourTickThreshold
public import SlowestClock
public import PdtArrowRate
public import PdtRhoQChirality
public import PdtCharpolyTensor

@[expose] public section

/-!
# Supplement: results of version 2, proved, not compared

The statements below are theorems of this repository, stated over the vocabulary of
`Challenge.lean` (`s`, `S`) and the further definitions given here (`mir`, `inc`, `sub`,
`tens`, `quart`, `rhoQSub`, `rhoQInc`), and proved here. None of them is on this
repository's compared surface: `comparator.json`, `Challenge.lean` and `Solution.lean` are
the three statements registered as PALOMAR-2026-08-19-000006 at revision `c48eb12`,
unchanged.

* The uniqueness results `padovan_minimal_unique`, `padovan_eigenvalue_unique`,
  `padovan_matrix_unique`, `pisot_ge_plastic` and `padovan_rules_chiral`, over the
  definitions `s`, `mir`, `inc` and `sub`. These five statements, over the same four
  definitions, are the compared statements of the separately registered entry
  PALOMAR-2026-10-18-000019 (stalex444/arithmetic-of-time-slowest-clock, revision
  `49eafbab4af8899b2a66469697bf74683a88ce87`); here they are proved and not compared. The
  first four come from `SlowestClock` (namespace `Time.Clock`), whose Padovan substitution
  `pad` and incidence matrix `inc` agree with `s` and `inc` here, and whose mirror is
  `PdtMirror.mir` of `PdtMirrorTensor`; `SlowestClock` uses the Mahler minima of the
  registered package of PALOMAR-2026-08-31-000004 (modules `PdtMahler*`, statements and
  proofs copied unchanged). `padovan_rules_chiral` follows from the compared
  `padovan_chirality` and `iterate_mir_seed`.
* The exact orientation threshold `padovan_exact_orientation_threshold_four` and its two
  halves, `padovan_length_three_orientation_ambiguity` and
  `padovan_reversal_forbidden_of_four_le`, transported from `PdtFourTickThreshold`
  (namespace `PDT.Padovan`, across `Letter ≃ Fin 3`, with the seed shift `S [0] = [1]`,
  `S [1] = [2]`).
* Mirrors on arbitrary alphabets: `iterate_mir_seed`, `iterate_tens_mir`,
  `single_mirrors_reverse` (list identities, transported from `PdtMirrorTensor`).
* `rate_eq_half_log`: a logarithm identity, transported from `PdtArrowRate`.
* `rhoQ_substitution_charpoly` and `rhoQ_chirality`: the characteristic polynomial and a
  chirality witness pair of the twelve-letter tensor of the Padovan and quartic
  substitutions (from `PdtCharpolyTensor` and `PdtRhoQChirality`).
-/

namespace ArithmeticOfTime

/-! ### Mirror and incidence matrix on an arbitrary alphabet -/

/-- The mirror of a substitution: every image block read backwards. -/
def mir {A : Type*} (σ : A → List A) : A → List A := fun x => (σ x).reverse

/-- The incidence matrix of a substitution `σ`: the entry at `(i, j)` counts the
occurrences of the letter `i` in the image block of `j`. -/
def inc {A : Type*} [DecidableEq A] (σ : A → List A) : Matrix A A ℤ :=
  fun i j => ((σ j).count i : ℤ)

/-! ### Substitutions on an arbitrary alphabet: transfer from `PdtMirror` -/

/-- Letterwise application of a substitution `σ` on an arbitrary alphabet: the
concatenation of the image blocks (for `σ = s` this is `S`). -/
def sub {A : Type*} (σ : A → List A) (w : List A) : List A := (w.map σ).flatten

/-- The row-major tensor of two substitutions, on the product alphabet:
`tens σ τ (x, y)` lists the pairs `(x', y')` with `x'` running through `σ x`
and, for each `x'`, `y'` running through `τ y`. -/
def tens {A B : Type*} (σ : A → List A) (τ : B → List B) : A × B → List (A × B) :=
  fun p => (σ p.1).flatMap (fun x => (τ p.2).map (fun y => (x, y)))

private lemma sub_eq_pdt {A : Type*} (σ : A → List A) : sub σ = PdtMirror.sub σ := by
  funext w
  induction w with
  | nil => rfl
  | cons x w ih =>
      rw [PdtMirror.sub_cons, ← ih]
      simp only [sub, List.map_cons, List.flatten_cons]

private lemma mir_eq_pdt {A : Type*} (σ : A → List A) : mir σ = PdtMirror.mir σ := rfl

private lemma tens_eq_pdt {A B : Type*} (σ : A → List A) (τ : B → List B) :
    tens σ τ = PdtMirror.tens σ τ := rfl

/-- **Mirroring reverses the iterates.** For any substitution on any alphabet,
every iterate of its mirror from a one-letter seed is the reversal of the
corresponding iterate of the substitution. -/
theorem iterate_mir_seed {A : Type*} (σ : A → List A) (n : ℕ) (x : A) :
    (sub (mir σ))^[n] [x] = ((sub σ)^[n] [x]).reverse := by
  simp only [sub_eq_pdt, mir_eq_pdt]
  exact PdtMirror.iterate_mir_seed σ n x

/-- **Mirror equivariance of the tensor.** Mirroring both factors reverses every
iterate of the row-major product, from every one-letter seed, for any two
substitutions on any two alphabets. -/
theorem iterate_tens_mir {A B : Type*} (σ : A → List A) (τ : B → List B) (n : ℕ)
    (z : A × B) :
    (sub (tens (mir σ) (mir τ)))^[n] [z] = ((sub (tens σ τ))^[n] [z]).reverse := by
  simp only [sub_eq_pdt, mir_eq_pdt, tens_eq_pdt]
  exact PdtMirror.iterate_tens_mir σ τ n z

/-- **The two single mirrors are mutual reversals.** At every depth and from
every one-letter seed, mirroring only the second factor gives the reversal of
the iterate obtained by mirroring only the first. -/
theorem single_mirrors_reverse {A B : Type*} (σ : A → List A) (τ : B → List B)
    (n : ℕ) (z : A × B) :
    (sub (tens σ (mir τ)))^[n] [z] = ((sub (tens (mir σ) τ))^[n] [z]).reverse := by
  simp only [sub_eq_pdt, mir_eq_pdt, tens_eq_pdt]
  exact PdtMirror.single_mirrors_reverse σ τ n z

/-! ### Minimality and uniqueness of the Padovan rule: transfer from `Time.Clock` -/

private lemma s_eq_pad : s = Time.Clock.pad := by
  funext x
  fin_cases x <;> rfl

/-- **Minimality and uniqueness of the Padovan rule.** Let `σ` be a substitution on
`k ≤ 3` letters (images may be empty) and `θ > 1` a real eigenvalue of its incidence matrix that is a
Pisot number: every other complex root of its minimal polynomial lies strictly
inside the unit circle. Then `ρ ≤ θ`, where `ρ³ = ρ + 1`; and `θ = ρ` exactly when,
after renaming the letters, `σ` is the Padovan substitution or its mirror. -/
theorem padovan_minimal_unique {k : ℕ} (hk : k ≤ 3) (σ : Fin k → List (Fin k)) (θ : ℝ)
    (hθ : Polynomial.aeval θ (inc σ).charpoly = 0) (h1 : 1 < θ)
    (hpisot : ∀ z ∈ (minpoly ℚ θ).aroots ℂ, z ≠ (θ : ℂ) → ‖z‖ < 1)
    (ρ : ℝ) (hρ : ρ ^ 3 = ρ + 1) :
    ρ ≤ θ ∧ (θ = ρ ↔ ∃ e : Fin k ≃ Fin 3,
      (∀ x, (σ x).map e = s (e x)) ∨ (∀ x, (σ x).map e = mir s (e x))) := by
  rw [s_eq_pad, mir_eq_pdt]
  exact Time.Clock.slowest_clock hk σ θ hθ h1 hpisot hρ

/-- **The classification, for every real eigenvalue.** For a substitution `σ` on
`k ≤ 3` letters and any real eigenvalue `θ` of its incidence matrix, `θ = ρ`
exactly when, after renaming the letters, `σ` is the Padovan substitution or its
mirror. -/
theorem padovan_eigenvalue_unique {k : ℕ} (hk : k ≤ 3) (σ : Fin k → List (Fin k)) (θ : ℝ)
    (hθ : Polynomial.aeval θ (inc σ).charpoly = 0) (ρ : ℝ) (hρ : ρ ^ 3 = ρ + 1) :
    θ = ρ ↔ ∃ e : Fin k ≃ Fin 3,
      (∀ x, (σ x).map e = s (e x)) ∨ (∀ x, (σ x).map e = mir s (e x)) := by
  rw [s_eq_pad, mir_eq_pdt]
  exact Time.Clock.clock_unique hk σ θ hθ hρ

/-- **The matrix classification.** A `3 × 3` matrix with entries in `ℕ` and
characteristic polynomial `x³ − x − 1` is the Padovan incidence matrix after one
simultaneous permutation of its rows and columns. -/
theorem padovan_matrix_unique (M : Matrix (Fin 3) (Fin 3) ℕ)
    (h : (M.map (Nat.cast : ℕ → ℤ)).charpoly = Polynomial.X ^ 3 - Polynomial.X - 1) :
    ∃ e : Fin 3 ≃ Fin 3, ∀ i j, M i j = !![0, 0, 1; 1, 0, 1; 0, 1, 0] (e i) (e j) :=
  Time.Clock.matrix_unique M h

/-- **Pisot numbers of degree at most three are at least `ρ`.** A real algebraic
integer `θ > 1` of degree at most `3`, every other complex conjugate of which lies
strictly inside the unit circle, satisfies `ρ ≤ θ`. -/
theorem pisot_ge_plastic (θ : ℝ) (h1 : 1 < θ) (hint : IsIntegral ℤ θ)
    (hdeg : (minpoly ℚ θ).natDegree ≤ 3)
    (hpisot : ∀ z ∈ (minpoly ℚ θ).aroots ℂ, z ≠ (θ : ℂ) → ‖z‖ < 1)
    (ρ : ℝ) (hρ : ρ ^ 3 = ρ + 1) : ρ ≤ θ :=
  Time.Clock.pisot_ge_rho h1 hint hdeg hpisot hρ

/-! ### Both minimal rules are chiral -/

/-- **Both minimal rules are chiral.** For the Padovan substitution, `[2, 0]` is a
factor of an iterate while `[0, 2]` is a factor of no iterate from any seed; for
its mirror, `[0, 2]` is a factor of an iterate while `[2, 0]` is a factor of none. -/
theorem padovan_rules_chiral :
    ((([2, 0] : List (Fin 3)) <:+: (sub s)^[5] [0]) ∧
      ∀ (n : ℕ) (x : Fin 3), ¬ ([0, 2] : List (Fin 3)) <:+: (sub s)^[n] [x]) ∧
    ((([0, 2] : List (Fin 3)) <:+: (sub (mir s))^[5] [0]) ∧
      ∀ (n : ℕ) (x : Fin 3), ¬ ([2, 0] : List (Fin 3)) <:+: (sub (mir s))^[n] [x]) := by
  have hS : sub s = S := rfl
  refine ⟨⟨?_, fun n x => ?_⟩, ⟨?_, fun n x => ?_⟩⟩
  · rw [hS]; exact (padovan_chirality 0 0).1
  · rw [hS]; exact (padovan_chirality n x).2
  · rw [iterate_mir_seed, hS]
    exact List.reverse_infix.mpr (padovan_chirality 0 0).1
  · rw [iterate_mir_seed, hS]
    intro h
    exact (padovan_chirality n x).2 (List.reverse_infix.mp h)

/-! ### Seed shifting: every seed's iterate is a seed-`0` iterate

`S [0] = [1]` and `S [1] = [2]`, so `S^[n] [1] = S^[n+1] [0]` and
`S^[n] [2] = S^[n+2] [0]` (as in `Solution.lean`, whose copies are private there). -/

private lemma S_seed_zero : S [(0 : Fin 3)] = [1] := by decide

private lemma S_seed_one : S [(1 : Fin 3)] = [2] := by decide

private lemma iter_seed_one (n : ℕ) : S^[n] [(1 : Fin 3)] = S^[n + 1] [0] := by
  rw [Function.iterate_succ_apply, S_seed_zero]

private lemma iter_seed_two (n : ℕ) : S^[n] [(2 : Fin 3)] = S^[n + 2] [0] := by
  show S^[n] [(2 : Fin 3)] = S^[n + 1 + 1] [0]
  rw [Function.iterate_succ_apply, S_seed_zero,
    Function.iterate_succ_apply, S_seed_one]

/-! ### The exact orientation threshold: transfer from `PDT.Padovan` -/

private def encP : PDT.Padovan.Letter → Fin 3
  | .a => 0
  | .b => 1
  | .c => 2

private def decP : Fin 3 → PDT.Padovan.Letter
  | 0 => .a
  | 1 => .b
  | 2 => .c

private lemma decP_encP (x : PDT.Padovan.Letter) : decP (encP x) = x := by
  cases x <;> rfl

private lemma encP_decP (y : Fin 3) : encP (decP y) = y := by
  fin_cases y <;> rfl

private lemma decP_comp_encP : decP ∘ encP = id := funext decP_encP

private lemma s_encP (x : PDT.Padovan.Letter) :
    s (encP x) = (PDT.Padovan.s x).map encP := by
  cases x <;> rfl

private lemma S_map_encP (w : List PDT.Padovan.Letter) :
    S (w.map encP) = (PDT.Padovan.S w).map encP := by
  induction w with
  | nil => rfl
  | cons x w ih =>
      simp only [List.map_cons, S, List.flatten_cons, PDT.Padovan.S_cons,
        List.map_append]
      rw [s_encP]
      simp only [S] at ih
      rw [ih]

private lemma iterP_map_encP (n : ℕ) (w : List PDT.Padovan.Letter) :
    S^[n] (w.map encP) = (PDT.Padovan.S^[n] w).map encP := by
  induction n generalizing w with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, S_map_encP, ih]

private lemma iterP_single (n : ℕ) (x : Fin 3) :
    S^[n] [x] = (PDT.Padovan.S^[n] [decP x]).map encP := by
  have h := iterP_map_encP n [decP x]
  simpa [encP_decP] using h

/-- Every seed's iterate is a seed-`0` iterate (`S [0] = [1]`, `S [1] = [2]`). -/
private lemma seed_to_zero (n : ℕ) (x : Fin 3) : ∃ k : ℕ, S^[n] [x] = S^[k] [0] := by
  rcases x with ⟨xv, hx⟩
  interval_cases xv
  · exact ⟨n, rfl⟩
  · exact ⟨n + 1, iter_seed_one n⟩
  · exact ⟨n + 2, iter_seed_two n⟩

/-- A seed-`0` factor on `Fin 3` is a factor of the canonical `PDT.Padovan` language. -/
private lemma toPDT {u : List (Fin 3)} {n : ℕ} (h : u <:+: S^[n] [0]) :
    PDT.Padovan.InLanguage (u.map decP) := by
  refine ⟨n, ?_⟩
  rw [iterP_single] at h
  have hm := h.map decP
  simpa [List.map_map, decP_comp_encP, decP] using hm

/-- A factor of the canonical `PDT.Padovan` language is a seed-`0` factor on `Fin 3`. -/
private lemma ofPDT {u : List PDT.Padovan.Letter} {n : ℕ}
    (h : u <:+: PDT.Padovan.S^[n] [PDT.Padovan.Letter.a]) :
    u.map encP <:+: S^[n] [0] := by
  rw [iterP_single]
  simpa [decP] using h.map encP

private theorem length_three_aux :
    ∃ u : List (Fin 3), (∃ n : ℕ, u <:+: S^[n] [0]) ∧ u.length = 3 ∧ u.reverse = u := by
  obtain ⟨u, ⟨n, hu⟩, hl, hr⟩ := PDT.Padovan.length_three_orientation_ambiguity
  refine ⟨u.map encP, ⟨n, ofPDT hu⟩, by simpa using hl, ?_⟩
  rw [← List.map_reverse, hr]

private theorem reversal_forbidden_aux (u : List (Fin 3)) (n : ℕ) (x : Fin 3)
    (hu : u <:+: S^[n] [x]) (hlen : 4 ≤ u.length) (m : ℕ) (y : Fin 3) :
    ¬ u.reverse <:+: S^[m] [y] := by
  intro hrev
  obtain ⟨k, hk⟩ := seed_to_zero n x
  obtain ⟨l, hl⟩ := seed_to_zero m y
  rw [hk] at hu
  rw [hl] at hrev
  have h1 := toPDT hu
  have h2 := toPDT hrev
  rw [List.map_reverse] at h2
  exact PDT.Padovan.reversal_forbidden_of_four_le (u.map decP) h1
    (by simpa using hlen) h2

/-- **The exact orientation threshold.** At length `3` some factor reads the same
in both directions, while from length `4` on every factor has a forbidden
reversal: four is the exact length from which orientation can be read from every
factor of the language. -/
theorem padovan_exact_orientation_threshold_four :
    (∃ u : List (Fin 3), (∃ n : ℕ, u <:+: S^[n] [0]) ∧ u.length = 3 ∧ u.reverse = u) ∧
      (∀ u : List (Fin 3), 4 ≤ u.length → (∃ (n : ℕ) (x : Fin 3), u <:+: S^[n] [x]) →
        ¬ ∃ (m : ℕ) (y : Fin 3), u.reverse <:+: S^[m] [y]) := by
  refine ⟨length_three_aux, ?_⟩
  rintro u hlen ⟨n, x, hu⟩ ⟨m, y, hrev⟩
  exact reversal_forbidden_aux u n x hu hlen m y hrev

/-! ### The two halves of the orientation threshold -/

/-- **Length three is orientation-ambiguous.** Some factor of length `3` of an
iterate from the seed `0` (`a`) is its own reversal. -/
theorem padovan_length_three_orientation_ambiguity :
    ∃ u : List (Fin 3), (∃ n : ℕ, u <:+: S^[n] [0]) ∧ u.length = 3 ∧ u.reverse = u :=
  padovan_exact_orientation_threshold_four.1

/-- **Reversal is forbidden from length four.** If a word of length at least `4`
is a factor of an iterate from some seed, its reversal is a factor of no iterate
from any seed. -/
theorem padovan_reversal_forbidden_of_four_le (u : List (Fin 3)) (n : ℕ) (x : Fin 3)
    (hu : u <:+: S^[n] [x]) (hlen : 4 ≤ u.length) (m : ℕ) (y : Fin 3) :
    ¬ u.reverse <:+: S^[m] [y] := fun hrev =>
  padovan_exact_orientation_threshold_four.2 u hlen ⟨n, x, hu⟩ ⟨m, y, hrev⟩

/-! ### A logarithm identity for the rate: transfer from `PDT.ArrowRate` -/

/-- **A logarithm identity for the rate.** If `ρ > 0` and a nonzero complex `σ`
satisfy `ρ · |σ|² = 1`, then `−log |σ| = ½ log ρ`. -/
theorem rate_eq_half_log (ρ : ℝ) (hρ : 0 < ρ) (σ : ℂ) (hσ : σ ≠ 0)
    (h : ρ * Complex.normSq σ = 1) :
    -Real.log ‖σ‖ = (1 / 2) * Real.log ρ :=
  PDT.ArrowRate.rate_eq_half_log ρ hρ σ hσ h

/-! ### The twelve-letter substitution: transfer from `PdtRhoQ` and `PdtCharpolyTensor` -/

/-- The quartic substitution on `Fin 4`: `0 ↦ [1]`, `1 ↦ [2]`, `2 ↦ [3]`,
`3 ↦ [0, 1]` (its incidence matrix has characteristic polynomial `x⁴ − x − 1`). -/
def quart : Fin 4 → List (Fin 4)
  | 0 => [1]
  | 1 => [2]
  | 2 => [3]
  | 3 => [0, 1]

/-- The twelve-letter substitution `tens s quart` on `Fin 3 × Fin 4`. Writing
`p, q, r` for the first coordinate `0, 1, 2` and `1, 2, 3, 4` for the second
coordinate `0, 1, 2, 3`, its images are
`p1 ↦ q2`, `p2 ↦ q3`, `p3 ↦ q4`, `p4 ↦ q1 q2`, `q1 ↦ r2`, `q2 ↦ r3`, `q3 ↦ r4`,
`q4 ↦ r1 r2`, `r1 ↦ p2 q2`, `r2 ↦ p3 q3`, `r3 ↦ p4 q4`, `r4 ↦ p1 p2 q1 q2`. -/
def rhoQSub : Fin 3 × Fin 4 → List (Fin 3 × Fin 4) := tens s quart

/-- The incidence matrix of `rhoQSub`: the entry at `(i, j)` counts the
occurrences of the letter `i` in the image block of `j`. -/
def rhoQInc : Matrix (Fin 3 × Fin 4) (Fin 3 × Fin 4) ℤ := inc rhoQSub

-- `idx : PdtRhoQ.Letter ≃ Fin 3 × Fin 4` is the letter encoding of `PdtCharpolyTensor`.
open PdtCharpolyTensor (idx)

private lemma rhoQSub_idx (j : PdtRhoQ.Letter) :
    rhoQSub (idx j) = (PdtRhoQ.s j).map idx := by
  cases j <;> decide

private lemma sub_map_idx (w : List PdtRhoQ.Letter) :
    sub rhoQSub (w.map idx) = (PdtRhoQ.S w).map idx := by
  induction w with
  | nil => rfl
  | cons x w ih =>
      simp only [sub, List.map_cons, List.flatten_cons, PdtRhoQ.S_cons,
        List.map_append] at ih ⊢
      rw [rhoQSub_idx, ih]

private lemma iter_map_idx (n : ℕ) (w : List PdtRhoQ.Letter) :
    (sub rhoQSub)^[n] (w.map idx) = (PdtRhoQ.S^[n] w).map idx := by
  induction n generalizing w with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, sub_map_idx, ih]

private lemma iter_single_idx (n : ℕ) (x : Fin 3 × Fin 4) :
    (sub rhoQSub)^[n] [x] = (PdtRhoQ.S^[n] [idx.symm x]).map idx := by
  have h := iter_map_idx n [idx.symm x]
  simpa using h

private lemma rhoQInc_idx (i j : PdtRhoQ.Letter) :
    rhoQInc (idx i) (idx j) = ((PdtCharpolyTensor.inc i j : ℕ) : ℤ) := by
  cases i <;> cases j <;> decide

private lemma rhoQInc_map :
    rhoQInc.map (Int.castRingHom ℚ) =
      (PdtCharpolyTensor.inc.map (fun n : ℕ => (n : ℚ))).reindex idx idx := by
  ext a b
  simp only [Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  have h := rhoQInc_idx (idx.symm a) (idx.symm b)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  rw [h]
  simp

open Polynomial in
/-- **The characteristic polynomial of the twelve-letter substitution.** It is
`x¹² − 3x⁹ − 2x⁸ + 2x⁶ − x⁵ − 3x⁴ − x³ + x − 1`, the minimal polynomial of `ρQ`
(that identification is `PdtRulerMinpoly`). -/
theorem rhoQ_substitution_charpoly :
    rhoQInc.charpoly =
      (X ^ 12 - 3 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 6 - X ^ 5 - 3 * X ^ 4 - X ^ 3 + X - 1 :
        ℤ[X]) := by
  apply Polynomial.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
  rw [← Matrix.charpoly_map, rhoQInc_map, PdtCharpolyTensor.substitution_charpoly]
  simp [PDT.RulerMinpoly.rulerPoly]

/-- **Chirality of the twelve-letter substitution.** The word `q2 p1` (here
`[(1, 1), (0, 0)]`) is a factor of an iterate, while its reversal `p1 q2` (here
`[(0, 0), (1, 1)]`) is a factor of no iterate from any seed. -/
theorem rhoQ_chirality (n : ℕ) (x : Fin 3 × Fin 4) :
    (([(1, 1), (0, 0)] : List (Fin 3 × Fin 4)) <:+: (sub rhoQSub)^[9] [(0, 2)]) ∧
      ¬ ([(0, 0), (1, 1)] : List (Fin 3 × Fin 4)) <:+: (sub rhoQSub)^[n] [x] := by
  obtain ⟨h1, h2⟩ := PdtRhoQ.rhoQ_chirality n (idx.symm x)
  constructor
  · have e : ([(1, 1), (0, 0)] : List (Fin 3 × Fin 4)) =
        [PdtRhoQ.Letter.q2, PdtRhoQ.Letter.p1].map idx := by decide
    have e' : ([(0, 2)] : List (Fin 3 × Fin 4)) = [PdtRhoQ.Letter.p3].map idx := by decide
    rw [e, e', iter_map_idx]
    exact h1.map idx
  · intro hinf
    rw [iter_single_idx] at hinf
    apply h2
    have e : ([(0, 0), (1, 1)] : List (Fin 3 × Fin 4)) =
        [PdtRhoQ.Letter.p1, PdtRhoQ.Letter.q2].map idx := by decide
    rw [e] at hinf
    have hm := hinf.map idx.symm
    simpa [List.map_map] using hm

end ArithmeticOfTime
