module
public import Mathlib

@[expose] public section
/-!
# PdtSalemFamily — the plastic number as a spectral threshold

The Bedford–Kim family `χ_n(x) = x^(n+1)·(x³ − x − 1) + (x³ + x² − 1)`
(characteristic polynomials of the linear-fractional-recurrence rational
surface automorphisms, Bedford–Kim, J. Geom. Anal. 19 (2009), eq. 0.3:
`x^(n+1)·P + P*` with `P` the plastic polynomial and `P*` its reciprocal).
Kernel-verified here, with hypotheses inline and only Mathlib vocabulary
in the main statements:

* **the family's canonical root sequence increases to ρ**
  (`plastic_salem_family`): for `n ≥ 7` the canonical root of `χ_n` in
  `[117/100, ρ)` exists, is the largest root below ρ, the sequence is
  strictly increasing, and it tends to ρ — the spectral half of
  Bedford–Kim's theorem ("the λ_n increase to δ* as n → ∞", δ* the real
  root of `t³ = t + 1`);
* **nothing at or above ρ** (`family_pos_of_rho_le`): `χ_n > 0` on
  `[ρ, ∞)`;
* **Lehmer is the first rung** (`lehmer_first_rung`,
  `lehmer_root_below_plastic`): `χ_7(x) = (x − 1)·L(x)` exactly, `L`
  Lehmer's degree-10 polynomial, so Lehmer's number — whose logarithm is
  the proven minimum positive entropy of a surface automorphism
  (McMullen) — is the `n = 7` member of the plastic family, and `L` has
  a root in `[117/100, ρ)`;
* **the ruler exclusion witness** (`ruler_second_conjugate`; "ruler" is
  the source project's name for the product `ρQ`): a nonreal `z` with
  `z⁴ = z + 1` and `1 < ‖ρ·z‖ < ρ·Q` — given the conjugate
  identification formalized in `PdtRulerMinpoly`, a second conjugate of
  `ρQ` strictly outside the unit circle, so `ρQ` is neither a Pisot nor a
  Salem number.

What is CITED, not formalized: the dynamical realization (that the roots
are entropies of rational surface automorphisms), the Salem-ness of the
roots, the emptiness of the gap `(1, 117/100)` for every `n`, and the
Blanc–Cantat classification (JAMS 29 (2016)) that turns the exclusion witness into "ρQ is not a
birational surface dynamical degree".

-/

namespace PDT
namespace SalemFamily

noncomputable section
open Filter Set

/-- The plastic polynomial `x³ − x − 1` as a real function. -/
def P (x : ℝ) : ℝ := x ^ 3 - x - 1

/-- The (monic) reciprocal `x³ + x² − 1` of the plastic polynomial. -/
def Pstar (x : ℝ) : ℝ := x ^ 3 + x ^ 2 - 1

/-- The Bedford–Kim family `χ_n = x^(n+1)·P + P*`. -/
def chi (n : ℕ) (x : ℝ) : ℝ := x ^ (n + 1) * P x + Pstar x

/-! ### The recurrence, endpoint identities, elementary bounds -/

lemma chi_rec (n : ℕ) (x : ℝ) :
    chi (n + 1) x = x * chi n x + (1 - x) * Pstar x := by
  unfold chi P Pstar
  rw [pow_succ]
  ring

/-- Any real solution of `ρ³ = ρ + 1` exceeds 1, by the certificate
`1 + x − x³ = (1 − x)(1 + x)² + x²`. -/
lemma one_lt_of_cubic {rho : ℝ} (hrho : rho ^ 3 = rho + 1) : 1 < rho := by
  by_contra h
  push Not at h
  have key : (1 - rho) * (1 + rho) ^ 2 + rho ^ 2 = 0 := by linear_combination -hrho
  have h1 : 0 ≤ (1 - rho) * (1 + rho) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : rho ^ 2 = 0 := by nlinarith [sq_nonneg rho]
  have h3 : rho = 0 := (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp h2
  rw [h3] at hrho
  norm_num at hrho

lemma P_strictMono {x y : ℝ} (hy : 1 ≤ y) (hxy : y < x) : P y < P x := by
  have hfac : P x - P y = (x - y) * (x ^ 2 + x * y + y ^ 2 - 1) := by
    unfold P; ring
  have hx : 1 ≤ x := le_of_lt (lt_of_le_of_lt hy hxy)
  have hxy0 : 0 ≤ x * y := mul_nonneg (by linarith) (by linarith)
  have hpos : 0 < x ^ 2 + x * y + y ^ 2 - 1 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg x, sq_nonneg y]
  have h3 := mul_pos (sub_pos.mpr hxy) hpos
  linarith

lemma P_mono {x y : ℝ} (hy : 1 ≤ y) (hxy : y ≤ x) : P y ≤ P x := by
  rcases eq_or_lt_of_le hxy with h | h
  · rw [h]
  · exact le_of_lt (P_strictMono hy h)

lemma Pstar_mono {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) : Pstar y ≤ Pstar x := by
  have hx : 0 ≤ x := le_trans hy hxy
  have h1 : Pstar x - Pstar y = (x - y) * (x ^ 2 + x * y + y ^ 2 + x + y) := by
    unfold Pstar; ring
  have h2 : 0 ≤ (x - y) * (x ^ 2 + x * y + y ^ 2 + x + y) := by
    apply mul_nonneg (sub_nonneg.mpr hxy)
    have := mul_nonneg hx hy
    nlinarith [sq_nonneg x, sq_nonneg y]
  linarith

lemma Pstar_pos {x : ℝ} (hx : 1 ≤ x) : 0 < Pstar x := by
  have h1 : Pstar 1 ≤ Pstar x := Pstar_mono (by norm_num) hx
  unfold Pstar at h1 ⊢
  norm_num at h1
  linarith

section Rho

variable {rho : ℝ} (hrho : rho ^ 3 = rho + 1)

include hrho

lemma P_rho : P rho = 0 := by unfold P; linarith

lemma x0_lt_rho : (117 / 100 : ℝ) < rho := by
  by_contra h
  push Not at h
  have hmono := P_mono (one_lt_of_cubic hrho).le h
  rw [P_rho hrho] at hmono
  unfold P at hmono
  norm_num at hmono

lemma rho_lt_two : rho < 2 := by
  by_contra h
  push Not at h
  have hmono := P_mono (by norm_num : (1:ℝ) ≤ 2) h
  rw [P_rho hrho] at hmono
  unfold P at hmono
  norm_num at hmono

/-- `χ_n(ρ) = ρ² + ρ` exactly, for every `n`. -/
lemma chi_at_rho (n : ℕ) : chi n rho = rho ^ 2 + rho := by
  unfold chi
  rw [P_rho hrho, mul_zero, zero_add]
  unfold Pstar
  linarith

lemma chi_at_rho_pos (n : ℕ) : 0 < chi n rho := by
  rw [chi_at_rho hrho]
  have h1 : 1 < rho := one_lt_of_cubic hrho
  nlinarith

/-- Nothing at or above ρ: `χ_n` is strictly positive on `[ρ, ∞)`. -/
lemma chi_pos_of_rho_le (n : ℕ) {x : ℝ} (hx : rho ≤ x) : 0 < chi n x := by
  have h1 : 1 < rho := one_lt_of_cubic hrho
  have hx1 : 1 ≤ x := le_trans (le_of_lt h1) hx
  have hP : 0 ≤ P x := by
    have := P_mono (le_of_lt h1) hx
    rw [P_rho hrho] at this
    linarith
  have hPs : 0 < Pstar x := Pstar_pos hx1
  have hpow : 0 ≤ x ^ (n + 1) := pow_nonneg (by linarith) _
  unfold chi
  nlinarith [mul_nonneg hpow hP]

end Rho

/-- The base of the induction: `χ_7(117/100) < 0` (exact rational
arithmetic). -/
lemma chi_seven_x0_neg : chi 7 (117 / 100) < 0 := by
  unfold chi P Pstar
  norm_num

/-- `χ_n(117/100) < 0` for every `n ≥ 7`, by the recurrence. -/
lemma chi_x0_neg : ∀ {n : ℕ}, 7 ≤ n → chi n (117 / 100) < 0 := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ m ih =>
    intro hm1
    rcases Nat.lt_or_ge m 7 with hm | hm
    · have h7 : m + 1 = 7 := by omega
      rw [h7]
      exact chi_seven_x0_neg
    · have hchi := ih hm
      rw [chi_rec]
      have hPs : 0 < Pstar (117 / 100) := Pstar_pos (by norm_num)
      nlinarith

lemma chi_continuous (n : ℕ) : Continuous (chi n) := by
  unfold chi P Pstar
  fun_prop

/-! ### The canonical root: `sSup` of the root set in `[117/100, ρ]` -/

section Roots

/-- The roots of `χ_n` in `[117/100, ρ]`. -/
def rootSet (n : ℕ) (rho : ℝ) : Set ℝ :=
  {x | x ∈ Icc (117 / 100 : ℝ) rho ∧ chi n x = 0}

/-- The canonical root: the largest root of `χ_n` in `[117/100, ρ]`. -/
def lam (n : ℕ) (rho : ℝ) : ℝ := sSup (rootSet n rho)

/-- The shifted sequence `μ_k = λ_{k+7}`. -/
def mu (rho : ℝ) (k : ℕ) : ℝ := lam (k + 7) rho

variable {rho : ℝ} (hrho : rho ^ 3 = rho + 1)

include hrho

omit hrho in
lemma rootSet_isCompact (n : ℕ) : IsCompact (rootSet n rho) := by
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc (a := (117 / 100 : ℝ)) (b := rho))
  · have hrw : rootSet n rho
        = Icc (117 / 100 : ℝ) rho ∩ chi n ⁻¹' {0} := rfl
    rw [hrw]
    exact isClosed_Icc.inter (isClosed_singleton.preimage (chi_continuous n))
  · intro x hx
    exact hx.1

lemma rootSet_nonempty {n : ℕ} (hn : 7 ≤ n) : (rootSet n rho).Nonempty := by
  have hle : (117 / 100 : ℝ) ≤ rho := le_of_lt (x0_lt_rho hrho)
  have hsub := intermediate_value_Icc hle (chi_continuous n).continuousOn
  have h0 : (0 : ℝ) ∈ Icc (chi n (117 / 100)) (chi n rho) :=
    ⟨le_of_lt (chi_x0_neg hn), le_of_lt (chi_at_rho_pos hrho n)⟩
  obtain ⟨x, hx, hfx⟩ := hsub h0
  exact ⟨x, hx, hfx⟩

lemma lam_mem {n : ℕ} (hn : 7 ≤ n) : lam n rho ∈ rootSet n rho :=
  (rootSet_isCompact n).sSup_mem (rootSet_nonempty hrho hn)

lemma lam_root {n : ℕ} (hn : 7 ≤ n) : chi n (lam n rho) = 0 :=
  (lam_mem hrho hn).2

lemma lam_ge_x0 {n : ℕ} (hn : 7 ≤ n) : (117 / 100 : ℝ) ≤ lam n rho :=
  (lam_mem hrho hn).1.1

lemma lam_le_rho {n : ℕ} (hn : 7 ≤ n) : lam n rho ≤ rho :=
  (lam_mem hrho hn).1.2

lemma lam_lt_rho {n : ℕ} (hn : 7 ≤ n) : lam n rho < rho := by
  rcases eq_or_lt_of_le (lam_le_rho hrho hn) with h | h
  · exfalso
    have hr := lam_root hrho hn
    rw [h] at hr
    have := chi_at_rho_pos hrho n
    linarith
  · exact h

lemma lam_gt_one {n : ℕ} (hn : 7 ≤ n) : 1 < lam n rho :=
  lt_of_lt_of_le (by norm_num) (lam_ge_x0 hrho hn)

/-- Maximality: no roots of `χ_n` strictly between `lam n` and ρ. -/
lemma lam_max {n : ℕ} (hn : 7 ≤ n) {y : ℝ} (h1 : lam n rho < y) (h2 : y < rho) :
    chi n y ≠ 0 := by
  intro hy
  have hmem : y ∈ rootSet n rho :=
    ⟨⟨le_trans (lam_ge_x0 hrho hn) (le_of_lt h1), le_of_lt h2⟩, hy⟩
  have hbdd : BddAbove (rootSet n rho) := (rootSet_isCompact n).bddAbove
  exact absurd (le_csSup hbdd hmem) (not_le.mpr h1)

/-! ### Strict monotonicity -/

omit hrho in
/-- The heart: at a root of `χ_n`, the next member is negative —
`χ_{n+1}(λ) = (1 − λ)·P*(λ) < 0`. -/
lemma chi_succ_at_root' {n : ℕ} {y : ℝ} (h1 : 1 < y) (hy : chi n y = 0) :
    chi (n + 1) y < 0 := by
  rw [chi_rec, hy, mul_zero, zero_add]
  have hPs : 0 < Pstar y := Pstar_pos (le_of_lt h1)
  nlinarith

lemma lam_strictMono {n : ℕ} (hn : 7 ≤ n) : lam n rho < lam (n + 1) rho := by
  have hneg : chi (n + 1) (lam n rho) < 0 :=
    chi_succ_at_root' (lam_gt_one hrho hn) (lam_root hrho hn)
  have hle : lam n rho ≤ rho := lam_le_rho hrho hn
  have hsub := intermediate_value_Icc hle (chi_continuous (n + 1)).continuousOn
  have h0 : (0 : ℝ) ∈ Icc (chi (n + 1) (lam n rho)) (chi (n + 1) rho) :=
    ⟨le_of_lt hneg, le_of_lt (chi_at_rho_pos hrho (n + 1))⟩
  obtain ⟨y, hy, hfy⟩ := hsub h0
  have hyne : lam n rho ≠ y := by
    intro h
    rw [← h] at hfy
    linarith
  have hylt : lam n rho < y := lt_of_le_of_ne hy.1 hyne
  have hymem : y ∈ rootSet (n + 1) rho :=
    ⟨⟨le_trans (lam_ge_x0 hrho hn) (le_of_lt hylt), hy.2⟩, hfy⟩
  have hbdd : BddAbove (rootSet (n + 1) rho) :=
    (rootSet_isCompact (n + 1)).bddAbove
  exact lt_of_lt_of_le hylt (le_csSup hbdd hymem)

/-! ### The limit -/

lemma mu_mono : Monotone (mu rho) := by
  apply monotone_nat_of_le_succ
  intro k
  exact le_of_lt (lam_strictMono hrho (by omega))

lemma mu_lt_rho (k : ℕ) : mu rho k < rho := lam_lt_rho hrho (by omega)

lemma mu_ge_x0 (k : ℕ) : (117 / 100 : ℝ) ≤ mu rho k := lam_ge_x0 hrho (by omega)

lemma mu_root (k : ℕ) : chi (k + 7) (mu rho k) = 0 := lam_root hrho (by omega)

/-- The limit is ρ: monotone convergence plus the power blow-up against
the bounded ratio `P*/|P|` on `[117/100, L]`. -/
lemma mu_tendsto : Tendsto (mu rho) atTop (nhds rho) := by
  have hmono := mu_mono hrho
  have hbdd : BddAbove (Set.range (mu rho)) := by
    refine ⟨rho, ?_⟩
    rintro y ⟨k, rfl⟩
    exact le_of_lt (mu_lt_rho hrho k)
  have hlim := tendsto_atTop_ciSup hmono hbdd
  have hLle : (⨆ k, mu rho k) ≤ rho :=
    ciSup_le fun k => le_of_lt (mu_lt_rho hrho k)
  rcases eq_or_lt_of_le hLle with heq | hlt
  · rwa [heq] at hlim
  · exfalso
    set L : ℝ := ⨆ k, mu rho k with hL
    have hL0 : (117 / 100 : ℝ) ≤ L :=
      le_trans (mu_ge_x0 hrho 0) (le_ciSup hbdd 0)
    have hL1 : 1 < L := lt_of_lt_of_le (by norm_num) hL0
    have heps : 0 < -P L := by
      have := P_strictMono (le_of_lt hL1) hlt
      rw [P_rho hrho] at this
      linarith
    have hbound : ∀ k : ℕ, (117 / 100 : ℝ) ^ (k + 8) * (-P L) ≤ 11 := by
      intro k
      have hmuk := mu_root hrho k
      have hmu1 : (117 / 100 : ℝ) ≤ mu rho k := mu_ge_x0 hrho k
      have hmuL : mu rho k ≤ L := le_ciSup hbdd k
      have hmu2 : mu rho k < 2 :=
        lt_of_lt_of_le (mu_lt_rho hrho k) (le_of_lt (rho_lt_two hrho))
      have hroot : (mu rho k) ^ (k + 8) * (-P (mu rho k)) = Pstar (mu rho k) := by
        have hexp : (mu rho k) ^ (k + 7 + 1) * P (mu rho k) + Pstar (mu rho k) = 0 :=
          hmuk
        have harith : k + 7 + 1 = k + 8 := by omega
        rw [harith] at hexp
        linear_combination -hexp
      have hPmono : -P L ≤ -P (mu rho k) := by
        have := P_mono (le_trans (by norm_num) hmu1) hmuL
        linarith
      have hPs : Pstar (mu rho k) ≤ 11 := by
        have hm := Pstar_mono (by linarith : (0:ℝ) ≤ mu rho k) (le_of_lt hmu2)
        have h2 : Pstar 2 = 11 := by unfold Pstar; norm_num
        linarith
      have hpow : (117 / 100 : ℝ) ^ (k + 8) ≤ (mu rho k) ^ (k + 8) :=
        pow_le_pow_left₀ (by norm_num) hmu1 _
      calc (117 / 100 : ℝ) ^ (k + 8) * (-P L)
          ≤ (mu rho k) ^ (k + 8) * (-P (mu rho k)) := by
            apply mul_le_mul hpow hPmono (le_of_lt heps)
            exact pow_nonneg (by linarith) _
        _ = Pstar (mu rho k) := hroot
        _ ≤ 11 := hPs
    have hblow : Tendsto (fun k : ℕ => (117 / 100 : ℝ) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    obtain ⟨k, hk⟩ := (hblow.eventually_gt_atTop (11 / (-P L))).exists
    have hk8 : (117 / 100 : ℝ) ^ k ≤ (117 / 100 : ℝ) ^ (k + 8) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hcontra : 11 / (-P L) < (117 / 100 : ℝ) ^ (k + 8) :=
      lt_of_lt_of_le hk hk8
    rw [div_lt_iff₀ heps] at hcontra
    linarith [hbound k]

end Roots

/-! ### Lehmer is the first rung -/

/-- **The exact factorization** `χ_7(x) = (x − 1)·L(x)`, with `L` Lehmer's
polynomial, over any commutative ring: Lehmer's number — whose logarithm
is the minimal positive surface entropy — is the `n = 7` member of the
plastic family. -/
theorem lehmer_first_rung {R : Type*} [CommRing R] (x : R) :
    x ^ 8 * (x ^ 3 - x - 1) + (x ^ 3 + x ^ 2 - 1) =
    (x - 1) * (x ^ 10 + x ^ 9 - x ^ 7 - x ^ 6 - x ^ 5 - x ^ 4 - x ^ 3 + x + 1) := by
  ring

/-- Lehmer's polynomial has a root in `[117/100, ρ)`: the `n = 7`
canonical root of the plastic family. -/
theorem lehmer_root_below_plastic {rho : ℝ} (hrho : rho ^ 3 = rho + 1) :
    ∃ x : ℝ, (117 / 100 : ℝ) ≤ x ∧ x < rho ∧
      x ^ 10 + x ^ 9 - x ^ 7 - x ^ 6 - x ^ 5 - x ^ 4 - x ^ 3 + x + 1 = 0 := by
  refine ⟨lam 7 rho, lam_ge_x0 hrho le_rfl, lam_lt_rho hrho le_rfl, ?_⟩
  have hroot : (lam 7 rho) ^ 8 * ((lam 7 rho) ^ 3 - lam 7 rho - 1) +
      ((lam 7 rho) ^ 3 + (lam 7 rho) ^ 2 - 1) = 0 := lam_root hrho le_rfl
  have hfac := lehmer_first_rung (lam 7 rho)
  have hne : lam 7 rho - 1 ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (lam_gt_one hrho le_rfl))
  have h0 : (lam 7 rho - 1) *
      ((lam 7 rho) ^ 10 + (lam 7 rho) ^ 9 - (lam 7 rho) ^ 7 - (lam 7 rho) ^ 6
        - (lam 7 rho) ^ 5 - (lam 7 rho) ^ 4 - (lam 7 rho) ^ 3 + lam 7 rho + 1)
      = 0 := by
    rw [← hfac]
    exact hroot
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h hne
  · exact h

/-! ### The main statements, hypotheses inline -/

/-- **Nothing at or above ρ**: every member of the Bedford–Kim family is
strictly positive on `[ρ, ∞)`, so the canonical roots below ρ are the
largest roots altogether (modulo the cited gap `(1, 117/100)`). -/
theorem family_pos_of_rho_le {rho : ℝ} (hrho : rho ^ 3 = rho + 1)
    (n : ℕ) {y : ℝ} (hy : rho ≤ y) :
    0 < y ^ (n + 1) * (y ^ 3 - y - 1) + (y ^ 3 + y ^ 2 - 1) :=
  chi_pos_of_rho_le hrho n hy

/-- **The plastic number is the limit of the Bedford–Kim spectral
family** (the spectral half of Bedford–Kim 2009): for `n ≥ 7` the family
`χ_n(x) = x^(n+1)·(x³ − x − 1) + (x³ + x² − 1)` has a canonical root
`lam n` in `[117/100, ρ)`, the largest root below ρ; the sequence is
strictly increasing; and it tends to ρ, the real root of `x³ = x + 1`. -/
theorem plastic_salem_family {rho : ℝ} (hrho : rho ^ 3 = rho + 1) :
    ∃ lam : ℕ → ℝ,
      (∀ n, 7 ≤ n →
        (117 / 100 : ℝ) ≤ lam n ∧ lam n < rho ∧
        (lam n) ^ (n + 1) * ((lam n) ^ 3 - lam n - 1) +
          ((lam n) ^ 3 + (lam n) ^ 2 - 1) = 0 ∧
        ∀ y : ℝ, lam n < y → y < rho →
          y ^ (n + 1) * (y ^ 3 - y - 1) + (y ^ 3 + y ^ 2 - 1) ≠ 0) ∧
      (∀ n, 7 ≤ n → lam n < lam (n + 1)) ∧
      Filter.Tendsto lam Filter.atTop (nhds rho) := by
  refine ⟨fun n => SalemFamily.lam n rho, ?_, ?_, ?_⟩
  · intro n hn
    exact ⟨lam_ge_x0 hrho hn, lam_lt_rho hrho hn, lam_root hrho hn,
      fun y h1 h2 => lam_max hrho hn h1 h2⟩
  · intro n hn
    exact lam_strictMono hrho hn
  · exact (tendsto_add_atTop_iff_nat 7).mp (mu_tendsto hrho)

/-! ### The ruler exclusion witness -/

section Ruler

open Complex

lemma quartic_strictMono {x y : ℝ} (hy : 1 ≤ y) (hxy : y < x) :
    y ^ 4 - y - 1 < x ^ 4 - x - 1 := by
  have hfac : (x ^ 4 - x - 1) - (y ^ 4 - y - 1)
      = (x - y) * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 - 1) := by
    ring
  have hx : 1 ≤ x := le_of_lt (lt_of_le_of_lt hy hxy)
  have hxy0 : 0 ≤ x * y := mul_nonneg (by linarith) (by linarith)
  have hpos : 0 < x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 - 1 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg x, sq_nonneg y,
      mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ x) (by linarith : (0:ℝ) ≤ x))
        (by linarith : (0:ℝ) ≤ y)]
  have h3 := mul_pos (sub_pos.mpr hxy) hpos
  linarith

/-- The negative real root of `x⁴ = x + 1`, bracketed in
`(−73/100, −72/100)`. -/
lemma exists_r2 :
    ∃ r : ℝ, r ^ 4 = r + 1 ∧ -(73 / 100 : ℝ) < r ∧ r < -(72 / 100 : ℝ) := by
  have hcont : Continuous (fun x : ℝ => x ^ 4 - x - 1) := by fun_prop
  have hle : (-(73 / 100 : ℝ)) ≤ -(72 / 100 : ℝ) := by norm_num
  have hsub := intermediate_value_Icc' hle hcont.continuousOn
  have h0 : (0 : ℝ) ∈ Icc ((fun x : ℝ => x ^ 4 - x - 1) (-(72 / 100 : ℝ)))
      ((fun x : ℝ => x ^ 4 - x - 1) (-(73 / 100 : ℝ))) := by
    constructor <;> norm_num
  obtain ⟨r, hr, hfr⟩ := hsub h0
  have hval : r ^ 4 - r - 1 = 0 := hfr
  refine ⟨r, by linarith, ?_, ?_⟩
  · rcases eq_or_lt_of_le hr.1 with h | h
    · exfalso
      rw [← h] at hval
      norm_num at hval
    · exact h
  · rcases eq_or_lt_of_le hr.2 with h | h
    · exfalso
      rw [h] at hval
      norm_num at hval
    · exact h

variable {Q : ℝ} (hQ : Q ^ 4 = Q + 1) (hQ1 : 1 < Q)

include hQ hQ1

lemma Q_gt : (61 / 50 : ℝ) < Q := by
  by_contra h
  push Not at h
  rcases eq_or_lt_of_le h with heq | hlt
  · rw [heq] at hQ
    norm_num at hQ
  · have hm := quartic_strictMono (le_of_lt hQ1) hlt
    have hz : Q ^ 4 - Q - 1 = 0 := by linarith
    rw [hz] at hm
    norm_num at hm

omit hQ1 in
lemma Q_lt : Q < (5 / 4 : ℝ) := by
  by_contra h
  push Not at h
  rcases eq_or_lt_of_le h with heq | hlt
  · rw [← heq] at hQ
    norm_num at hQ
  · have hm := quartic_strictMono (by norm_num : (1:ℝ) ≤ 5 / 4) hlt
    have hz : Q ^ 4 - Q - 1 = 0 := by linarith
    rw [hz] at hm
    norm_num at hm

/-- **The ruler exclusion witness.** For ρ the real root of `x³ = x + 1`
and Q the root of `x⁴ = x + 1` above 1: there is a NONREAL root `z` of
`x⁴ = x + 1` with `1 < ‖ρ·z‖ < ρ·Q`. Together with the minimal
polynomial of `ρQ` formalized in `PdtRulerMinpoly` (the products of
embeddings are its conjugates in the degree-12 compositum), this
exhibits a second conjugate of `ρQ` strictly
outside the unit circle — so `ρQ` is neither a Pisot nor a Salem
number. -/
theorem ruler_second_conjugate {rho : ℝ} (hrho : rho ^ 3 = rho + 1) :
    ∃ z : ℂ, z ^ 4 = z + 1 ∧ z.im ≠ 0 ∧
      1 < ‖(rho : ℂ) * z‖ ∧ ‖(rho : ℂ) * z‖ < rho * Q := by
  have hrho1 : 1 < rho := one_lt_of_cubic hrho
  obtain ⟨r, hr, hr1, hr2⟩ := exists_r2
  have hQgt := Q_gt hQ hQ1
  have hQlt := Q_lt hQ
  set s : ℝ := Q + r with hs
  set m : ℝ := Q * r with hm
  set c : ℝ := Q ^ 2 + Q * r + r ^ 2 with hc
  have hQr : Q ≠ r := by
    intro h
    rw [← h] at hr1
    linarith
  -- REL1: Q³ + Q²r + Qr² + r³ = 1, by cancelling (Q − r)
  have hREL : Q ^ 3 + Q ^ 2 * r + Q * r ^ 2 + r ^ 3 = 1 := by
    have hne : Q - r ≠ 0 := sub_ne_zero.mpr hQr
    have hkey : (Q - r) * (Q ^ 3 + Q ^ 2 * r + Q * r ^ 2 + r ^ 3)
        = (Q - r) * 1 := by
      linear_combination hQ - hr
    exact mul_left_cancel₀ hne hkey
  -- the two Vieta scalars
  have hS1 : s * (2 * m - s ^ 2) = -1 := by
    rw [hs, hm]
    linear_combination -hREL
  have hS2 : m * (s ^ 2 - m) = -1 := by
    rw [hs, hm]
    linear_combination r * hREL - hr
  have hS1' : (s : ℂ) * (2 * (m : ℂ) - (s : ℂ) ^ 2) = -1 := by
    exact_mod_cast hS1
  have hS2' : (m : ℂ) * ((s : ℂ) ^ 2 - (m : ℂ)) = -1 := by
    exact_mod_cast hS2
  -- the factorization over ℂ
  have hfact : ∀ w : ℂ, w ^ 4 - w - 1 =
      ((w - (Q : ℂ)) * (w - (r : ℂ))) * (w ^ 2 + (s : ℂ) * w + (c : ℂ)) := by
    intro w
    have h1 : (w - (Q : ℂ)) * (w - (r : ℂ)) = w ^ 2 - (s : ℂ) * w + (m : ℂ) := by
      push_cast [hs, hm]
      ring
    have h2 : (c : ℂ) = (s : ℂ) ^ 2 - (m : ℂ) := by
      push_cast [hc, hs, hm]
      ring
    rw [h1, h2]
    linear_combination (-(w : ℂ)) * hS1' - hS2'
  -- bounds: 0 < s, s² < 4c, 1 < c, c < Q²
  have hspos : 0 < s := by
    rw [hs]
    linarith
  have hslt : s < 53 / 100 := by
    rw [hs]
    linarith
  have hcgt : 1 < c := by
    rw [hc]
    nlinarith [sq_nonneg (Q - 61 / 50), sq_nonneg (r + 73 / 100),
      mul_lt_mul_of_neg_right hQlt (show r < 0 by linarith)]
  have hclt : c < Q ^ 2 := by
    rw [hc]
    nlinarith [mul_neg_of_neg_of_pos (show r < 0 by linarith)
      (show (0:ℝ) < Q + r by linarith)]
  have hdisc : s ^ 2 < 4 * c := by
    nlinarith [sq_nonneg s]
  -- the witness
  set d : ℝ := Real.sqrt (4 * c - s ^ 2) with hd
  have hdpos : 0 < d := Real.sqrt_pos.mpr (by linarith)
  have hdsq : d ^ 2 = 4 * c - s ^ 2 := Real.sq_sqrt (by linarith)
  set z : ℂ := ((-s / 2 : ℝ) : ℂ) + ((d / 2 : ℝ) : ℂ) * Complex.I with hz
  have hzim : z.im ≠ 0 := by
    rw [hz]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
      add_zero, zero_add]
    intro h
    have : d = 0 := by linarith
    linarith
  -- z satisfies the quadratic
  have hd' : ((d : ℝ) : ℂ) ^ 2 = 4 * (c : ℂ) - (s : ℂ) ^ 2 := by
    exact_mod_cast hdsq
  have hquad : z ^ 2 + (s : ℂ) * z + (c : ℂ) = 0 := by
    rw [hz]
    push_cast
    linear_combination (((d : ℂ) ^ 2) / 4) * Complex.I_sq - (1 / 4 : ℂ) * hd'
  -- hence z is a quartic root
  have hzq : z ^ 4 = z + 1 := by
    have h := hfact z
    rw [hquad, mul_zero] at h
    linear_combination h
  -- the modulus
  have hnormsq : Complex.normSq z = c := by
    rw [hz, Complex.normSq_add_mul_I]
    nlinarith [hdsq]
  have habs : ‖z‖ ^ 2 = c := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hnormsq
  have hz1 : 1 < ‖z‖ := by
    nlinarith [norm_nonneg z, habs, hcgt, sq_nonneg (‖z‖ - 1), sq_nonneg (‖z‖ + 1)]
  have hzQ : ‖z‖ < Q := by
    by_contra hcon
    push Not at hcon
    have hsq : Q ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (by linarith) hcon 2
    linarith
  have hrhopos : (0:ℝ) < rho := by linarith
  refine ⟨z, hzq, hzim, ?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hrhopos]
    nlinarith [hz1]
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hrhopos]
    exact mul_lt_mul_of_pos_left hzQ hrhopos

end Ruler

end
end SalemFamily
end PDT
