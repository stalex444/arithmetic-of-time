import PisotBoundary
import MechanicalWord
import Chirality
import Settling

/-!
# Solution: proved versions of the Challenge declarations

Each declaration below has exactly the statement of its `Challenge.lean`
counterpart. The proofs are supplied by the project modules `PisotBoundary`
(the settle/spiral dichotomy, by an elementary Vieta reduction on the
conjugate pair) and `MechanicalWord` (the Sturmian tick word), where
`ArithmeticOfTime.tick` is definitionally `Time.m`.
-/

namespace ArithmeticOfTime

theorem cubic_conj_norm_lt_one (z : ℂ) (hz : z ^ 3 = z + 1) (him : z.im ≠ 0) :
    ‖z‖ < 1 :=
  Time.cubic_conj_norm_lt_one z hz him

theorem quartic_conj_norm_gt_one (w : ℂ) (hw : w ^ 4 = w + 1) (him : w.im ≠ 0) :
    1 < ‖w‖ :=
  Time.quartic_conj_norm_gt_one w hw him

theorem pisot_boundary_dichotomy
    (z : ℂ) (hz : z ^ 3 = z + 1) (hzim : z.im ≠ 0)
    (w : ℂ) (hw : w ^ 4 = w + 1) (hwim : w.im ≠ 0) :
    ‖z‖ < 1 ∧ 1 < ‖w‖ :=
  Time.pisot_boundary_dichotomy z hz hzim w hw hwim

noncomputable def tick (β : ℝ) (n : ℕ) : ℤ := ⌊((n : ℝ) + 1) * β⌋ - ⌊(n : ℝ) * β⌋

theorem tick_two_valued (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    tick β n = 0 ∨ tick β n = 1 := by
  simpa [tick, Time.m] using Time.m_mem β hβ0 hβ1 n

theorem tick_density (β : ℝ) :
    Filter.Tendsto (fun N : ℕ => ((∑ k ∈ Finset.range N, tick β k : ℤ) : ℝ) / (N : ℝ))
      Filter.atTop (nhds β) := by
  simpa [tick, Time.m] using Time.density_tendsto β

theorem tick_aperiodic (β : ℝ) (hβ : Irrational β) :
    ¬ ∃ p : ℕ, 0 < p ∧ ∀ n : ℕ, tick β (n + p) = tick β n := by
  simpa [tick, Time.m] using Time.aperiodic β hβ

theorem tick_balanced (β : ℝ) (L i j : ℕ) :
    |(∑ k ∈ Finset.range L, tick β (i + k)) - (∑ k ∈ Finset.range L, tick β (j + k))| ≤ 1 := by
  simpa [tick, Time.m] using Time.balanced β L i j

/-! ### Chirality — transport from `Time.Padovan` across the letter encoding -/

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

theorem padovan_no_long_palindrome (n : ℕ) (u : List (Fin 3))
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

/-! ### Meyer separation — from `Settling` -/

theorem meyer_separation (r : ℝ) (hr : r ^ 3 = r + 1)
    (z : ℂ) (hz : z ^ 3 = z + 1) (him : z.im ≠ 0)
    (p : ℤ × ℤ × ℤ) (hp : p ≠ 0) :
    1 ≤ |(p.1 : ℝ) + (p.2.1 : ℝ) * r + (p.2.2 : ℝ) * r ^ 2| *
        ‖(p.1 : ℂ) + (p.2.1 : ℂ) * z + (p.2.2 : ℂ) * z ^ 2‖ ^ 2 := by
  have h := Time.meyer_separation (r := r) (z := z) hr hz him p hp
  unfold Time.embed at h
  exact h

end ArithmeticOfTime
