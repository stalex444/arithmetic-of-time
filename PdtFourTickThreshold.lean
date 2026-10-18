module
public import PdtChirality

@[expose] public section

/-!
# PdtFourTickThreshold — the exact Padovan orientation threshold

For the Padovan factor language (the factors of the iterates from the seed
`a`), reversal is uniformly excluded from length four onward, while the
length-three palindrome `aba` occurs.  Thus four is the exact worst-case word
length at which orientation can be read from the factor language.  The proof
checks the finite length-four certificate and then uses factorial closure: a
reversed long factor would contain the reversal of its length-four prefix.

The threshold is a number of letters, not a number of substitution steps.  The
`FourTick` namespace records three elementary identities of the plastic cubic
that keep the two apart: `rho^4 (rho - 1) = 1`; `rho / (rho - 1) = rho^5`; and,
for any sequence with `tail k = (rho⁻¹)^k`, `tail 4 = rho - 1 > 0`.  So a
geometric tail of ratio `rho⁻¹` has not vanished after four steps, and the
length-four threshold is not a step count after which anything vanishes.  These
identities are pure algebra; no dynamical model is formalized here.

The words "tick", "readout" and "time" are names only; no statement in this
module is about physical time.
-/

namespace PDT

namespace Padovan

/-- A finite word belongs to the canonical Padovan factor language when it is
an infix of some substitution iterate from the seed `a`. -/
def InLanguage (u : List Letter) : Prop :=
  ∃ n : ℕ, u <:+: S^[n] [Letter.a]

/-- The length-four part of the finite certificate is completely oriented:
the reversal of none of its length-four words is itself in the certificate. -/
theorem F5_no_reversal_pair_length_four :
    ∀ u ∈ F5, u.length = 4 → u.reverse ∉ F5 := by
  decide

/-- Every canonical Padovan factor of length at least four has a forbidden
reversal.  The only finite check is at length four; factor closure propagates
it to every larger length. -/
theorem reversal_forbidden_of_four_le (u : List Letter)
    (hu : InLanguage u) (hlen : 4 ≤ u.length) : ¬ InLanguage u.reverse := by
  obtain ⟨n, hun⟩ := hu
  let t := u.take 4
  have htlen : t.length = 4 := by
    simp only [t, List.length_take]
    omega
  have htu : t <:+: u := (List.take_prefix 4 u).isInfix
  have htn : t <:+: S^[n] [Letter.a] := htu.trans hun
  have htF : t ∈ F5 := factors_complete n t htn (by omega)
  intro hrev
  obtain ⟨m, hrev_m⟩ := hrev
  have htrev_u : t.reverse <:+: u.reverse := htu.reverse
  have htrev_m : t.reverse <:+: S^[m] [Letter.a] := htrev_u.trans hrev_m
  have htrevF : t.reverse ∈ F5 := factors_complete m t.reverse htrev_m (by simp [htlen])
  exact F5_no_reversal_pair_length_four t htF htlen htrevF

/-- The eighth iterate contains the palindrome `aba`. -/
theorem iterate_eight :
    S^[8] [Letter.a] =
      [Letter.c, Letter.a, Letter.b, Letter.a, Letter.b, Letter.b, Letter.c] := by
  decide

/-- A length-three factor can remain unchanged by reversal, so no uniform
orientation readout is possible at length three. -/
theorem length_three_orientation_ambiguity :
    ∃ u : List Letter, InLanguage u ∧ u.length = 3 ∧ u.reverse = u := by
  refine ⟨[Letter.a, Letter.b, Letter.a], ?_, by decide, by decide⟩
  refine ⟨8, ?_⟩
  rw [iterate_eight]
  exact ⟨[Letter.c], [Letter.b, Letter.b, Letter.c], rfl⟩

/-- **Exact threshold.** Three symbols can be reversal-ambiguous, whereas
every canonical Padovan factor of length at least four has forbidden reversal. -/
theorem exact_orientation_threshold_four :
    (∃ u : List Letter, InLanguage u ∧ u.length = 3 ∧ u.reverse = u) ∧
      (∀ u : List Letter, InLanguage u → 4 ≤ u.length → ¬ InLanguage u.reverse) :=
  ⟨length_three_orientation_ambiguity, reversal_forbidden_of_four_le⟩

end Padovan

namespace FourTick

/-- The plastic cubic gives the exact four-power gap identity. -/
theorem rho_four_gap_identity {rho : ℝ} (hrho : rho ^ 3 = rho + 1) :
    rho ^ 4 * (rho - 1) = 1 := by
  calc
    rho ^ 4 * (rho - 1) = rho ^ 5 - rho ^ 4 := by ring
    _ = (rho ^ 3 - rho - 1) * (rho ^ 2 - rho + 1) + 1 := by ring
    _ = 1 := by rw [show rho ^ 3 - rho - 1 = 0 by linarith]; ring

/-- `rho / (rho - 1) = rho^5` for the plastic number (`rho / (rho - 1)` is the
closed form of the geometric series `∑_{k ≥ 0} rho^(-k)`; only the identity is
proved). -/
theorem mean_horizon_eq_rho_five {rho : ℝ} (hrho1 : 1 < rho)
    (hrho : rho ^ 3 = rho + 1) : rho / (rho - 1) = rho ^ 5 := by
  have hgap : rho - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hrho1)
  have hfour := rho_four_gap_identity hrho
  field_simp
  nlinarith

/-- For any sequence with `tail k = (rho⁻¹)^k`, the value after four steps is
exactly `rho - 1`, hence strictly positive. -/
theorem four_step_tail_eq_gap {rho : ℝ} (hrho1 : 1 < rho)
    (hrho : rho ^ 3 = rho + 1) (tail : ℕ → ℝ)
    (htail : ∀ k, tail k = (rho⁻¹) ^ k) :
    tail 4 = rho - 1 ∧ 0 < tail 4 := by
  have hrho0 : rho ≠ 0 := ne_of_gt (lt_trans zero_lt_one hrho1)
  have hfour := rho_four_gap_identity hrho
  have heq : (rho⁻¹) ^ 4 = rho - 1 := by
    rw [inv_pow]
    exact inv_eq_of_mul_eq_one_right hfour
  rw [htail, heq]
  exact ⟨rfl, sub_pos.mpr hrho1⟩

/-- Consequently a geometric tail of ratio `rho⁻¹` is nonzero after four steps:
four is not a step count at which such a tail vanishes. -/
theorem four_is_not_universal_tail_deadline {rho : ℝ} (hrho1 : 1 < rho)
    (hrho : rho ^ 3 = rho + 1) (tail : ℕ → ℝ)
    (htail : ∀ k, tail k = (rho⁻¹) ^ k) : tail 4 ≠ 0 := by
  exact ne_of_gt (four_step_tail_eq_gap hrho1 hrho tail htail).2

end FourTick

end PDT

#print axioms PDT.Padovan.F5_no_reversal_pair_length_four
#print axioms PDT.Padovan.reversal_forbidden_of_four_le
#print axioms PDT.Padovan.iterate_eight
#print axioms PDT.Padovan.length_three_orientation_ambiguity
#print axioms PDT.Padovan.exact_orientation_threshold_four
#print axioms PDT.FourTick.rho_four_gap_identity
#print axioms PDT.FourTick.mean_horizon_eq_rho_five
#print axioms PDT.FourTick.four_step_tail_eq_gap
#print axioms PDT.FourTick.four_is_not_universal_tail_deadline
