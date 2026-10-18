/-
PdtMahlerMain — the degree-4 Mahler minimality theorem.

Assembles the certificate soundness layer (PdtMahler) and the kernel-checked
box coverage (PdtMahlerBox) into:

  `quartic_mahler_min` : among monic irreducible integer quartics with
  Mahler measure above 1, x⁴ − x − 1 attains the minimum.

Case analysis on an arbitrary monic irreducible quartic p with M > 1:
outside the box, a coefficient violates the C(4,k)·θ bound, which is a
depth-0 Graeffe certificate; inside the box, `boxD4_all` hands one of
TIE (measure equal by negation/reversal invariance), CYCLO (measure 1,
contradicting M > 1), FACTOR (contradicting irreducibility), or GRAEFFE
(M > θ ≥ M(x⁴−x−1), the upper side by the K = 5 ℓ¹ certificate).
-/
module
public import PdtMahlerBox

@[expose] public section

namespace PDT
namespace Mahler
open Polynomial

/-! ### Integer-level structure of `zq4` -/

noncomputable section

lemma coeff_int_cast_ZX (n : ℤ) (k : ℕ) :
    ((n : ℤ[X])).coeff k = if k = 0 then n else 0 := by
  rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C]
  simp

lemma zq4_monic_int (t : Z4) : (zq4 t).Monic := by
  unfold zq4; monicity!

lemma zq4_natDegree_int (t : Z4) : (zq4 t).natDegree = 4 := by
  unfold zq4; compute_degree!

lemma coeff_zq4 (t : Z4) (k : ℕ) (hk : k ≤ 4) :
    (zq4 t).coeff k = tupCoeff t k := by
  obtain ⟨a, b, c, e⟩ := t
  interval_cases k <;> simp [zq4, tupCoeff, coeff_int_cast_ZX]

/-- Every monic integer quartic is `zq4` of its coefficient tuple. -/
lemma eq_zq4_self (p : ℤ[X]) (hm : p.Monic) (hd : p.natDegree = 4) :
    p = zq4 (p.coeff 3, p.coeff 2, p.coeff 1, p.coeff 0) := by
  ext n
  by_cases hn : n ≤ 4
  · interval_cases n
    · rw [coeff_zq4 _ 0 (by norm_num)]; rfl
    · rw [coeff_zq4 _ 1 (by norm_num)]; rfl
    · rw [coeff_zq4 _ 2 (by norm_num)]; rfl
    · rw [coeff_zq4 _ 3 (by norm_num)]; rfl
    · rw [coeff_zq4 _ 4 (by norm_num)]
      show p.coeff 4 = 1
      have := hm.coeff_natDegree
      rwa [hd] at this
  · push_neg at hn
    rw [coeff_eq_zero_of_natDegree_lt (by rw [hd]; omega),
      coeff_eq_zero_of_natDegree_lt (by rw [zq4_natDegree_int]; omega)]

/-! ### Cyclotomic elements have measure one -/

lemma mahlerMeasure_X_pow_sub_one {n : ℕ} (hn : 0 < n) :
    (((X : ℂ[X]) ^ n - 1)).mahlerMeasure = 1 := by
  have hm : ((X : ℂ[X]) ^ n - 1).Monic := by
    have h := monic_X_pow_sub_C (1 : ℂ) (Nat.pos_iff_ne_zero.mp hn)
    simpa using h
  rw [mahlerMeasure_eq_prod_roots hm]
  have hone : ∀ r ∈ ((X : ℂ[X]) ^ n - 1).roots, max 1 ‖r‖ = 1 := by
    intro r hr
    have h1 : r ^ n = 1 := by
      have := isRoot_of_mem_roots hr
      simpa [IsRoot, sub_eq_zero] using this
    have h2 : ‖r‖ ^ n = 1 := by rw [← norm_pow, h1, norm_one]
    have h3 : ‖r‖ = 1 := by
      rcases lt_trichotomy ‖r‖ 1 with h | h | h
      · exfalso
        have := pow_lt_one₀ (norm_nonneg r) h (Nat.pos_iff_ne_zero.mp hn)
        rw [h2] at this
        exact lt_irrefl 1 this
      · exact h
      · exfalso
        have := one_lt_pow₀ h (Nat.pos_iff_ne_zero.mp hn)
        rw [h2] at this
        exact lt_irrefl 1 this
    simp [h3]
  rw [Multiset.map_congr rfl hone]
  simp

/-- A monic quartic dividing `Xⁿ − 1` has Mahler measure 1. -/
lemma mahler_eq_one_of_dvd_X_pow_sub_one {t : Z4} {g : ℤ[X]} {n : ℕ}
    (hn : 0 < n) (hfac : zq4 t * g = X ^ n - 1) :
    ((zq4 t).map (Int.castRingHom ℂ)).mahlerMeasure = 1 := by
  have hX : ((X : ℤ[X]) ^ n - 1) ≠ 0 := by
    have := X_pow_sub_C_ne_zero hn (1 : ℤ)
    simpa using this
  have hg : g ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hfac
    exact hX hfac.symm
  have hmapped := congrArg (Polynomial.map (Int.castRingHom ℂ)) hfac
  rw [Polynomial.map_mul] at hmapped
  have hXmap : (((X : ℤ[X]) ^ n - 1).map (Int.castRingHom ℂ))
      = (X : ℂ[X]) ^ n - 1 := by
    simp
  rw [hXmap] at hmapped
  have hM := congrArg Polynomial.mahlerMeasure hmapped
  rw [mahlerMeasure_mul, mahlerMeasure_X_pow_sub_one hn] at hM
  have h1t : 1 ≤ ((zq4 t).map (Int.castRingHom ℂ)).mahlerMeasure :=
    one_le_mahlerMeasure_of_ne_zero (zq4_monic_int t).ne_zero
  have h1g : 1 ≤ (g.map (Int.castRingHom ℂ)).mahlerMeasure :=
    one_le_mahlerMeasure_of_ne_zero hg
  have hle : ((zq4 t).map (Int.castRingHom ℂ)).mahlerMeasure ≤ 1 := by
    calc ((zq4 t).map (Int.castRingHom ℂ)).mahlerMeasure
        ≤ ((zq4 t).map (Int.castRingHom ℂ)).mahlerMeasure
            * (g.map (Int.castRingHom ℂ)).mahlerMeasure :=
          le_mul_of_one_le_right (le_trans zero_le_one h1t) h1g
      _ = 1 := hM
  exact le_antisymm hle h1t

lemma cyclo5_fac : zq4 (1, 1, 1, 1) * (X - 1) = X ^ 5 - 1 := by
  unfold zq4; simp; ring

lemma cyclo8_fac : zq4 (0, 0, 0, 1) * (X ^ 4 - 1) = X ^ 8 - 1 := by
  unfold zq4; simp; ring

lemma cyclo10_fac :
    zq4 (-1, 1, -1, 1) * (X ^ 6 + X ^ 5 - X - 1) = X ^ 10 - 1 := by
  unfold zq4; simp; ring

lemma cyclo12_fac :
    zq4 (0, -1, 0, 1) * (X ^ 8 + X ^ 6 - X ^ 2 - 1) = X ^ 12 - 1 := by
  unfold zq4; simp; ring

/-! ### Factor witnesses kill irreducibility -/

def zlin (u : ℤ) : ℤ[X] := X + C u

def zcub (v : ℤ × ℤ × ℤ) : ℤ[X] :=
  X ^ 3 + C v.1 * X ^ 2 + C v.2.1 * X + C v.2.2

def zquad (w : ℤ × ℤ) : ℤ[X] := X ^ 2 + C w.1 * X + C w.2

lemma zq4_mul13 (u : ℤ) (v : ℤ × ℤ × ℤ) :
    zq4 (mul13 u v) = zlin u * zcub v := by
  obtain ⟨v2, v1, v0⟩ := v
  unfold zq4 mul13 zlin zcub
  simp only [map_add, map_mul]
  ring

lemma zq4_mul22 (w1 w2 : ℤ × ℤ) :
    zq4 (mul22 w1 w2) = zquad w1 * zquad w2 := by
  obtain ⟨a1, a0⟩ := w1
  obtain ⟨b1, b0⟩ := w2
  unfold zq4 mul22 zquad
  simp only [map_add, map_mul]
  ring

lemma zlin_natDegree (u : ℤ) : (zlin u).natDegree = 1 := by
  unfold zlin; compute_degree!

lemma zcub_natDegree (v : ℤ × ℤ × ℤ) : (zcub v).natDegree = 3 := by
  unfold zcub; compute_degree!

lemma zquad_natDegree (w : ℤ × ℤ) : (zquad w).natDegree = 2 := by
  unfold zquad; compute_degree!

lemma not_irr_mul13 (u : ℤ) (v : ℤ × ℤ × ℤ) :
    ¬ Irreducible (zq4 (mul13 u v)) := by
  rw [zq4_mul13]
  intro hi
  rcases hi.isUnit_or_isUnit rfl with h | h
  · exact Polynomial.not_isUnit_of_natDegree_pos _
      (by rw [zlin_natDegree]; norm_num) h
  · exact Polynomial.not_isUnit_of_natDegree_pos _
      (by rw [zcub_natDegree]; norm_num) h

lemma not_irr_mul22 (w1 w2 : ℤ × ℤ) :
    ¬ Irreducible (zq4 (mul22 w1 w2)) := by
  rw [zq4_mul22]
  intro hi
  rcases hi.isUnit_or_isUnit rfl with h | h
  · exact Polynomial.not_isUnit_of_natDegree_pos _
      (by rw [zquad_natDegree]; norm_num) h
  · exact Polynomial.not_isUnit_of_natDegree_pos _
      (by rw [zquad_natDegree]; norm_num) h

/-! ### The tie orbit has equal measure -/

lemma tie_neg_eq :
    ((zq4 (0, 0, 1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure
      = ((zq4 (0, 0, -1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  rw [map_zq4, map_zq4]
  push_cast
  have h := mahlerMeasure_comp_neg (q4_monic 0 0 (-1) (-1))
  rw [q4_comp_neg] at h
  norm_num at h ⊢
  exact h

lemma tie_rev_eq :
    ((zq4 (1, 0, 0, -1)).map (Int.castRingHom ℂ)).mahlerMeasure
      = ((zq4 (0, 0, -1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  rw [map_zq4, map_zq4]
  push_cast
  have h := mahlerMeasure_q4_inv 0 0 (-1) (-1) (by norm_num)
  norm_num at h ⊢
  exact h

lemma tie_revneg_eq :
    ((zq4 (-1, 0, 0, -1)).map (Int.castRingHom ℂ)).mahlerMeasure
      = ((zq4 (0, 0, -1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  have h1 : ((zq4 (-1, 0, 0, -1)).map (Int.castRingHom ℂ)).mahlerMeasure
      = ((zq4 (0, 0, 1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure := by
    rw [map_zq4, map_zq4]
    push_cast
    have h := mahlerMeasure_q4_inv 0 0 1 (-1) (by norm_num)
    norm_num at h ⊢
    exact h
  rw [h1, tie_neg_eq]

/-! ### The upper certificate for the family and the out-of-box branch -/

/-- `M(x⁴−x−1) ≤ 139/100`, by the K = 5 ℓ¹ Graeffe certificate. -/
lemma fam_upper :
    ((zq4 (0, 0, -1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure
      ≤ (139 : ℝ) / 100 := by
  have h := upper_cert_sound (t := (0, 0, -1, -1)) (P := 139) (Q := 100)
    (by norm_num) (K := 5) (by decide)
  exact_mod_cast h

lemma mem_boxD4 {t : Z4} :
    t ∈ boxD4 ↔ |t.1| ≤ 5 ∧ |t.2.1| ≤ 8 ∧ |t.2.2.1| ≤ 5 ∧ |t.2.2.2| ≤ 1 := by
  obtain ⟨a, b, c, e⟩ := t
  simp [boxD4, Finset.mem_product, Finset.mem_Icc, abs_le]

lemma lowerCert_succ_def (fuel : ℕ) (P2 Q2 : ℤ) (s : Z4) :
    lowerCert (fuel + 1) P2 Q2 s
      = (lowerHit P2 Q2 s || lowerCert fuel (P2 ^ 2) (Q2 ^ 2) (gr4Z s)) := rfl

/-- Outside the box, some coefficient bound is violated, which is a depth-0
Graeffe certificate. -/
lemma lowerCert_of_not_mem {t : Z4} (h : t ∉ boxD4) :
    lowerCert 9 139 100 t = true := by
  obtain ⟨a, b, c, e⟩ := t
  rw [mem_boxD4] at h
  have hd : 5 < |a| ∨ 8 < |b| ∨ 5 < |c| ∨ 1 < |e| := by
    by_contra hc
    push_neg at hc
    exact h ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
  rw [lowerCert_succ_def, Bool.or_eq_true]
  left
  unfold lowerHit
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  rcases hd with h5 | h8 | h5c | h1e
  · right
    show 4 * 139 < |tupCoeff (a, b, c, e) 3| * 100
    have : tupCoeff (a, b, c, e) 3 = a := rfl
    rw [this]
    generalize |a| = m at h5 ⊢
    omega
  · left; right
    show 6 * 139 < |tupCoeff (a, b, c, e) 2| * 100
    have : tupCoeff (a, b, c, e) 2 = b := rfl
    rw [this]
    generalize |b| = m at h8 ⊢
    omega
  · left; left; right
    show 4 * 139 < |tupCoeff (a, b, c, e) 1| * 100
    have : tupCoeff (a, b, c, e) 1 = c := rfl
    rw [this]
    generalize |c| = m at h5c ⊢
    omega
  · left; left; left
    show 1 * 139 < |tupCoeff (a, b, c, e) 0| * 100
    have : tupCoeff (a, b, c, e) 0 = e := rfl
    rw [this]
    generalize |e| = m at h1e ⊢
    omega

/-! ### The main theorem -/

/-- THE DEGREE-4 MAHLER MINIMALITY THEOREM: among monic irreducible
integer quartics of Mahler measure above one, `x⁴ − x − 1` attains the
minimum. (The degree-window positive at d = 4.) -/
theorem quartic_mahler_min (p : ℤ[X]) (hm : p.Monic) (hd : p.natDegree = 4)
    (hi : Irreducible p)
    (h1 : 1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure) :
    ((zq4 (0, 0, -1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure
      ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
  have hp : p = zq4 (p.coeff 3, p.coeff 2, p.coeff 1, p.coeff 0) :=
    eq_zq4_self p hm hd
  set t : Z4 := (p.coeff 3, p.coeff 2, p.coeff 1, p.coeff 0) with ht
  rw [hp] at h1 hi ⊢
  by_cases hbox : t ∈ boxD4
  · have hOK := boxD4_all t hbox
    unfold elemOK at hOK
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hOK
    rcases hOK with ((((htie | hcyc) | hf13) | hf22) | hcert)
    · simp only [tieList, List.mem_cons, List.mem_singleton] at htie
      rcases htie with h | h | h | (h | hfalse)
      · rw [h]
      · rw [h, tie_neg_eq]
      · rw [h, tie_rev_eq]
      · rw [h, tie_revneg_eq]
      · simp at hfalse
    · simp only [cycloList, List.mem_cons, List.mem_singleton] at hcyc
      have hMone : ((zq4 t).map (Int.castRingHom ℂ)).mahlerMeasure = 1 := by
        rcases hcyc with h | h | h | (h | hfalse)
        · rw [h]; exact mahler_eq_one_of_dvd_X_pow_sub_one (by norm_num) cyclo5_fac
        · rw [h]; exact mahler_eq_one_of_dvd_X_pow_sub_one (by norm_num) cyclo8_fac
        · rw [h]; exact mahler_eq_one_of_dvd_X_pow_sub_one (by norm_num) cyclo10_fac
        · rw [h]; exact mahler_eq_one_of_dvd_X_pow_sub_one (by norm_num) cyclo12_fac
        · simp at hfalse
      rw [hMone] at h1
      exact absurd h1 (lt_irrefl 1)
    · obtain ⟨pr, _, heq⟩ := hf13
      rw [← heq] at hi
      exact absurd hi (not_irr_mul13 pr.1 pr.2)
    · obtain ⟨pr, _, heq⟩ := hf22
      rw [← heq] at hi
      exact absurd hi (not_irr_mul22 pr.1 pr.2)
    · exact fam_upper.trans (le_of_lt (lowerCert_139_sound hcert))
  · exact fam_upper.trans
      (le_of_lt (lowerCert_139_sound (lowerCert_of_not_mem hbox)))

/-- The pretty statement: `zq4 (0,0,−1,−1)` is `X⁴ − X − 1`. -/
lemma zq4_fam : zq4 (0, 0, -1, -1) = X ^ 4 - X - 1 := by
  unfold zq4; simp; ring

/-- Restatement of the minimality theorem with the family polynomial
written out. -/
theorem quartic_mahler_min' (p : ℤ[X]) (hm : p.Monic) (hd : p.natDegree = 4)
    (hi : Irreducible p)
    (h1 : 1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure) :
    ((((X : ℤ[X]) ^ 4 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure
      ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
  rw [← zq4_fam]
  exact quartic_mahler_min p hm hd hi h1

end

end Mahler
end PDT
