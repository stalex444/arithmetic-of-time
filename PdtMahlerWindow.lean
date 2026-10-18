/-
PdtMahlerWindow — the degree-window positives at d = 3 and d = 2.

Clones the d = 4 certificate architecture (PdtMahler / PdtMahlerBox /
PdtMahlerMain / PdtMahlerTheta) down the window:

  `cubic_mahler_min`  : x³ − x − 1 attains the degree-3 Mahler minimum,
  `mahler_cubic_rho`  : that minimum M satisfies M³ = M + 1, 1 < M —
                        it IS ρ, the smallest Pisot number (Siegel);
  `quadratic_mahler_min` : x² − x − 1 attains the degree-2 minimum,
  `mahler_quadratic_phi` : that minimum M satisfies M² = M + 1, 1 < M —
                        it IS the golden ratio φ.

With PdtMahlerMain/Theta this completes the degree-window POSITIVES:
the Mahler floors of degrees 2, 3, 4 are φ, ρ, θ₄.
-/
module
public import PdtMahlerTheta
public import PdtPisotBoundary
public import PdtIrreducible

@[expose] public section

namespace PDT
namespace Mahler
open Polynomial Complex

/-! ## Degree 3: the ℂ-level Graeffe layer -/

noncomputable section

def q3 (a b c : ℂ) : ℂ[X] := X ^ 3 + C a * X ^ 2 + C b * X + C c

lemma q3_monic (a b c : ℂ) : (q3 a b c).Monic := by
  unfold q3; monicity!

lemma q3_natDegree (a b c : ℂ) : (q3 a b c).natDegree = 3 := by
  unfold q3; compute_degree!

lemma q3_comp_neg (a b c : ℂ) :
    (q3 a b c).comp (-X) = -q3 (-a) b (-c) := by
  unfold q3
  simp only [add_comp, mul_comp, pow_comp, X_comp, C_comp, map_neg]
  ring

lemma q3_roots_card (a b c : ℂ) :
    Multiset.card (q3 a b c).roots = 3 := by
  have h := (IsAlgClosed.splits (k := ℂ) (q3 a b c)).natDegree_eq_card_roots
  rw [q3_natDegree] at h
  omega

lemma prod_X_add_C_roots3 (a b c : ℂ) :
    (((q3 a b c).roots).map fun r => X + C r).prod = q3 (-a) b (-c) := by
  have h := prod_X_sub_C_comp_neg (q3 a b c).roots
  rw [← monic_eq_prod_roots (q3_monic a b c), q3_comp_neg, q3_roots_card] at h
  have hodd : ((-1 : ℂ[X])) ^ (3 : ℕ) = -1 := by norm_num
  rw [hodd] at h
  have h2 : q3 (-a) b (-c)
      = ((q3 a b c).roots.map fun r => X - C (-r)).prod := by
    have := congrArg (fun p => -p) h
    simpa using this
  rw [h2]
  refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
  intro r _
  rw [map_neg, sub_neg_eq_add]

/-- The Graeffe ring identity at degree 3. -/
lemma gr3_ring (a b c : ℂ) :
    q3 a b c * q3 (-a) b (-c)
      = (q3 (2*b - a^2) (b^2 - 2*a*c) (-(c^2))).comp (X ^ 2) := by
  unfold q3
  simp only [add_comp, mul_comp, pow_comp, X_comp, C_comp]
  simp only [map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]
  ring

/-- The Graeffe measure identity at degree 3. -/
lemma mahlerMeasure_gr3 (a b c : ℂ) :
    (q3 (2*b - a^2) (b^2 - 2*a*c) (-(c^2))).mahlerMeasure
      = (q3 a b c).mahlerMeasure ^ 2 := by
  have key : q3 (2*b - a^2) (b^2 - 2*a*c) (-(c^2))
      = (((q3 a b c).roots.map fun r => r ^ 2).map fun r => X - C r).prod := by
    apply comp_X_sq_injective
    rw [multiset_prod_comp, Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def, sub_comp, X_comp, C_comp]
    rw [prod_X_sq_sub_sq, prod_X_add_C_roots3,
      ← monic_eq_prod_roots (q3_monic a b c), gr3_ring]
  rw [key, mahlerMeasure_multiset_prod_X_sub_C, Multiset.map_map,
    mahlerMeasure_eq_prod_roots (q3_monic a b c), pow_two,
    ← Multiset.prod_map_mul]
  refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
  intro r _
  exact max_one_norm_sq r

end

/-! ## Degree 3: the integer certificate layer -/

abbrev Z3 := ℤ × ℤ × ℤ

def gr3Z : Z3 → Z3
  | (a, b, c) => (2*b - a^2, b^2 - 2*a*c, -(c^2))

def tupCoeff3 : Z3 → ℕ → ℤ
  | (_, _, c), 0 => c
  | (_, b, _), 1 => b
  | (a, _, _), 2 => a
  | _, 3 => 1
  | _, _ => 0

def tupL1_3 : Z3 → ℤ
  | (a, b, c) => 1 + |a| + |b| + |c|

noncomputable section

def zq3 (t : Z3) : ℤ[X] := X ^ 3 + C t.1 * X ^ 2 + C t.2.1 * X + C t.2.2

lemma map_zq3 (t : Z3) :
    (zq3 t).map (Int.castRingHom ℂ)
      = q3 (t.1 : ℂ) (t.2.1 : ℂ) (t.2.2 : ℂ) := by
  unfold zq3 q3
  simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_C]

lemma natDegree_map_zq3 (t : Z3) :
    ((zq3 t).map (Int.castRingHom ℂ)).natDegree = 3 := by
  rw [map_zq3]; exact q3_natDegree _ _ _

lemma mahlerMeasure_map_gr3Z (t : Z3) :
    ((zq3 (gr3Z t)).map (Int.castRingHom ℂ)).mahlerMeasure
      = ((zq3 t).map (Int.castRingHom ℂ)).mahlerMeasure ^ 2 := by
  obtain ⟨a, b, c⟩ := t
  rw [map_zq3, map_zq3]
  have harg : q3 ((gr3Z (a, b, c)).1 : ℂ) ((gr3Z (a, b, c)).2.1 : ℂ)
        ((gr3Z (a, b, c)).2.2 : ℂ)
      = q3 (2*(b:ℂ) - (a:ℂ)^2) ((b:ℂ)^2 - 2*(a:ℂ)*(c:ℂ)) (-((c:ℂ)^2)) := by
    show q3 ((2*b - a^2 : ℤ) : ℂ) ((b^2 - 2*a*c : ℤ) : ℂ)
        ((-(c^2) : ℤ) : ℂ) = _
    congr 1 <;> push_cast <;> ring
  rw [harg, mahlerMeasure_gr3]

lemma mahlerMeasure_map_gr3Z_iterate (K : ℕ) (t : Z3) :
    ((zq3 (gr3Z^[K] t)).map (Int.castRingHom ℂ)).mahlerMeasure
      = ((zq3 t).map (Int.castRingHom ℂ)).mahlerMeasure ^ (2 ^ K) := by
  induction K generalizing t with
  | zero => simp
  | succ K ih =>
      rw [Function.iterate_succ_apply, ih (gr3Z t), mahlerMeasure_map_gr3Z,
        ← pow_mul]
      congr 1
      ring

lemma coeff_map_zq3 (t : Z3) (k : ℕ) (hk : k ≤ 3) :
    ((zq3 t).map (Int.castRingHom ℂ)).coeff k = (tupCoeff3 t k : ℂ) := by
  obtain ⟨a, b, c⟩ := t
  rw [map_zq3]
  interval_cases k <;> simp [q3, tupCoeff3, coeff_int_cast_CX]

lemma lower_cert3_sound {t : Z3} {P Q : ℕ} (hQ : 0 < Q) {K k : ℕ} (hk : k ≤ 3)
    (h : (Nat.choose 3 k : ℤ) * (P : ℤ) ^ (2 ^ K)
        < |tupCoeff3 (gr3Z^[K] t) k| * (Q : ℤ) ^ (2 ^ K)) :
    (P : ℝ) / Q < ((zq3 t).map (Int.castRingHom ℂ)).mahlerMeasure := by
  set M : ℝ := ((zq3 t).map (Int.castRingHom ℂ)).mahlerMeasure with hM
  have hM0 : 0 ≤ M := mahlerMeasure_nonneg _
  have hchoose : (0 : ℝ) < (Nat.choose 3 k : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos hk)
  have hQ0 : (0 : ℝ) < (Q : ℝ) ^ (2 ^ K) := by positivity
  have hbound := norm_coeff_le_choose_mul_mahlerMeasure k
      ((zq3 (gr3Z^[K] t)).map (Int.castRingHom ℂ))
  rw [natDegree_map_zq3, mahlerMeasure_map_gr3Z_iterate,
    coeff_map_zq3 _ _ hk] at hbound
  simp only [Complex.norm_intCast] at hbound
  rw [← hM] at hbound
  have hR : (Nat.choose 3 k : ℝ) * (P : ℝ) ^ (2 ^ K)
      < |((tupCoeff3 (gr3Z^[K] t) k : ℤ) : ℝ)| * (Q : ℝ) ^ (2 ^ K) := by
    exact_mod_cast h
  have step1 : (Nat.choose 3 k : ℝ) * (P : ℝ) ^ (2 ^ K)
      < (Nat.choose 3 k : ℝ) * (M ^ (2 ^ K) * (Q : ℝ) ^ (2 ^ K)) :=
    calc (Nat.choose 3 k : ℝ) * (P : ℝ) ^ (2 ^ K)
        < |((tupCoeff3 (gr3Z^[K] t) k : ℤ) : ℝ)| * (Q : ℝ) ^ (2 ^ K) := hR
      _ ≤ (Nat.choose 3 k : ℝ) * M ^ (2 ^ K) * (Q : ℝ) ^ (2 ^ K) :=
          mul_le_mul_of_nonneg_right hbound (le_of_lt hQ0)
      _ = (Nat.choose 3 k : ℝ) * (M ^ (2 ^ K) * (Q : ℝ) ^ (2 ^ K)) := by ring
  have hpow : ((P : ℝ) / Q) ^ (2 ^ K) < M ^ (2 ^ K) := by
    rw [div_pow, div_lt_iff₀ hQ0]
    exact lt_of_mul_lt_mul_left step1 (le_of_lt hchoose)
  exact lt_of_pow_lt_pow_left₀ _ hM0 hpow

lemma mahlerMeasure_map_zq3_le_l1 (s : Z3) :
    ((zq3 s).map (Int.castRingHom ℂ)).mahlerMeasure ≤ (tupL1_3 s : ℝ) := by
  refine (mahlerMeasure_le_sum_norm_coeff _).trans ?_
  rw [Polynomial.sum_def]
  have hsupp : ((zq3 s).map (Int.castRingHom ℂ)).support ⊆ Finset.range 4 := by
    intro n hn
    rw [Finset.mem_range]
    have h1 := Polynomial.le_natDegree_of_mem_supp n hn
    rw [natDegree_map_zq3] at h1
    omega
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsupp
    (fun i _ _ => norm_nonneg _)).trans ?_
  rw [show (4 : ℕ) = 3 + 1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  rw [coeff_map_zq3 _ 0 (by norm_num), coeff_map_zq3 _ 1 (by norm_num),
    coeff_map_zq3 _ 2 (by norm_num), coeff_map_zq3 _ 3 (by norm_num)]
  obtain ⟨a, b, c⟩ := s
  simp only [tupCoeff3, tupL1_3, Complex.norm_intCast]
  push_cast
  rw [abs_one]
  linarith [abs_nonneg (a : ℝ), abs_nonneg (b : ℝ), abs_nonneg (c : ℝ)]

lemma upper_cert3_sound {t : Z3} {P Q : ℕ} (hQ : 0 < Q) {K : ℕ}
    (h : tupL1_3 (gr3Z^[K] t) * (Q : ℤ) ^ (2 ^ K) ≤ (P : ℤ) ^ (2 ^ K)) :
    ((zq3 t).map (Int.castRingHom ℂ)).mahlerMeasure ≤ (P : ℝ) / Q := by
  set M : ℝ := ((zq3 t).map (Int.castRingHom ℂ)).mahlerMeasure with hM
  have hQ0 : (0 : ℝ) < (Q : ℝ) ^ (2 ^ K) := by positivity
  have hl1 := mahlerMeasure_map_zq3_le_l1 (gr3Z^[K] t)
  rw [mahlerMeasure_map_gr3Z_iterate, ← hM] at hl1
  have hR : (tupL1_3 (gr3Z^[K] t) : ℝ) * (Q : ℝ) ^ (2 ^ K)
      ≤ (P : ℝ) ^ (2 ^ K) := by exact_mod_cast h
  have hpow : M ^ (2 ^ K) ≤ ((P : ℝ) / Q) ^ (2 ^ K) := by
    rw [div_pow, le_div_iff₀ hQ0]
    exact (mul_le_mul_of_nonneg_right hl1 (le_of_lt hQ0)).trans hR
  exact le_of_pow_le_pow_left₀ (by positivity) (by positivity) hpow

end

/-! ## Degree 3: certifier, box, coverage -/

def lowerHit3 (P2 Q2 : ℤ) (s : Z3) : Bool :=
  decide (1 * P2 < |tupCoeff3 s 0| * Q2) ||
  decide (3 * P2 < |tupCoeff3 s 1| * Q2) ||
  decide (3 * P2 < |tupCoeff3 s 2| * Q2)

def lowerCert3 : ℕ → ℤ → ℤ → Z3 → Bool
  | 0, _, _, _ => false
  | fuel + 1, P2, Q2, s =>
      lowerHit3 P2 Q2 s || lowerCert3 fuel (P2 ^ 2) (Q2 ^ 2) (gr3Z s)

noncomputable section

lemma lowerHit3_sound {P Q : ℕ} (hQ : 0 < Q) {K : ℕ} {t : Z3}
    (h : lowerHit3 ((P : ℤ) ^ 2 ^ K) ((Q : ℤ) ^ 2 ^ K) (gr3Z^[K] t) = true) :
    (P : ℝ) / Q < ((zq3 t).map (Int.castRingHom ℂ)).mahlerMeasure := by
  unfold lowerHit3 at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · have hc : ((Nat.choose 3 0 : ℕ) : ℤ) = 1 := by norm_num
    exact lower_cert3_sound (K := K) (k := 0) hQ (by norm_num)
      (by rw [hc]; exact h)
  · have hc : ((Nat.choose 3 1 : ℕ) : ℤ) = 3 := by norm_num
    exact lower_cert3_sound (K := K) (k := 1) hQ (by norm_num)
      (by rw [hc]; exact h)
  · have hc : ((Nat.choose 3 2 : ℕ) : ℤ) = 3 := by norm_num [Nat.choose]
    exact lower_cert3_sound (K := K) (k := 2) hQ (by norm_num)
      (by rw [hc]; exact h)

lemma lowerCert3_sound {P Q : ℕ} (hQ : 0 < Q) :
    ∀ (fuel K : ℕ) (t : Z3),
      lowerCert3 fuel ((P : ℤ) ^ 2 ^ K) ((Q : ℤ) ^ 2 ^ K) (gr3Z^[K] t) = true →
      (P : ℝ) / Q < ((zq3 t).map (Int.castRingHom ℂ)).mahlerMeasure := by
  intro fuel
  induction fuel with
  | zero => intro K t h; simp [lowerCert3] at h
  | succ fuel ih =>
      intro K t h
      unfold lowerCert3 at h
      simp only [Bool.or_eq_true] at h
      rcases h with h1 | h2
      · exact lowerHit3_sound hQ h1
      · have e1 : ((P : ℤ) ^ 2 ^ K) ^ 2 = (P : ℤ) ^ 2 ^ (K + 1) := by
          rw [← pow_mul, pow_succ]
        have e2 : ((Q : ℤ) ^ 2 ^ K) ^ 2 = (Q : ℤ) ^ 2 ^ (K + 1) := by
          rw [← pow_mul, pow_succ]
        have e3 : gr3Z (gr3Z^[K] t) = gr3Z^[K + 1] t :=
          (Function.iterate_succ_apply' gr3Z K t).symm
        rw [e1, e2, e3] at h2
        exact ih (K + 1) t h2

lemma lowerCert3_133_sound {t : Z3} (h : lowerCert3 9 133 100 t = true) :
    (133 : ℝ) / 100 < ((zq3 t).map (Int.castRingHom ℂ)).mahlerMeasure := by
  have hs := lowerCert3_sound (P := 133) (Q := 100) (by norm_num) 9 0 t
  simp only [pow_zero, pow_one, Function.iterate_zero_apply] at hs
  have h' : lowerCert3 9 ((133 : ℕ) : ℤ) ((100 : ℕ) : ℤ) t = true := by
    exact_mod_cast h
  exact_mod_cast hs h'

end

def tieList3 : List Z3 := [(0, -1, -1), (0, -1, 1), (1, 0, -1), (-1, 0, 1)]

def mul12 (u : ℤ) (v : ℤ × ℤ) : Z3 := (v.1 + u, v.2 + u * v.1, u * v.2)

def facts12 : List (ℤ × (ℤ × ℤ)) := [
  (-1, (-2, 1)), (0, (-2, 1)), (-1, (-1, 1)), (1, (-2, 1)), (-1, (0, 0)),
  (-1, (0, 1)), (0, (-1, 1)), (-1, (1, 0)), (-1, (1, 1)), (0, (0, 0)),
  (1, (-1, 1)), (0, (0, 1)), (-1, (2, 1)), (1, (0, 0)), (0, (1, 1)),
  (1, (0, 1)), (0, (2, 1)), (1, (1, 1)), (1, (2, 1))]

def elemOK3 (t : Z3) : Bool :=
  decide (t ∈ tieList3) ||
  facts12.any (fun p => decide (mul12 p.1 p.2 = t)) ||
  lowerCert3 9 133 100 t

noncomputable def boxD3 : Finset Z3 :=
  (Finset.Icc (-3 : ℤ) 3) ×ˢ (Finset.Icc (-3 : ℤ) 3) ×ˢ (Finset.Icc (-1 : ℤ) 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- COVERAGE at degree 3: 147 kernel-checked certificates. -/
theorem boxD3_all : ∀ t ∈ boxD3, elemOK3 t = true := by decide

/-! ## Degree 3: main assembly -/

noncomputable section

lemma zq3_monic_int (t : Z3) : (zq3 t).Monic := by
  unfold zq3; monicity!

lemma zq3_natDegree_int (t : Z3) : (zq3 t).natDegree = 3 := by
  unfold zq3; compute_degree!

lemma coeff_zq3 (t : Z3) (k : ℕ) (hk : k ≤ 3) :
    (zq3 t).coeff k = tupCoeff3 t k := by
  obtain ⟨a, b, c⟩ := t
  interval_cases k <;> simp [zq3, tupCoeff3, coeff_int_cast_ZX]

lemma eq_zq3_self (p : ℤ[X]) (hm : p.Monic) (hd : p.natDegree = 3) :
    p = zq3 (p.coeff 2, p.coeff 1, p.coeff 0) := by
  ext n
  by_cases hn : n ≤ 3
  · interval_cases n
    · rw [coeff_zq3 _ 0 (by norm_num)]; rfl
    · rw [coeff_zq3 _ 1 (by norm_num)]; rfl
    · rw [coeff_zq3 _ 2 (by norm_num)]; rfl
    · rw [coeff_zq3 _ 3 (by norm_num)]
      show p.coeff 3 = 1
      have := hm.coeff_natDegree
      rwa [hd] at this
  · push_neg at hn
    rw [coeff_eq_zero_of_natDegree_lt (by rw [hd]; omega),
      coeff_eq_zero_of_natDegree_lt (by rw [zq3_natDegree_int]; omega)]

def zquad' (v : ℤ × ℤ) : ℤ[X] := X ^ 2 + C v.1 * X + C v.2

lemma zq3_mul12 (u : ℤ) (v : ℤ × ℤ) :
    zq3 (mul12 u v) = zlin u * zquad' v := by
  obtain ⟨v1, v0⟩ := v
  unfold zq3 mul12 zlin zquad'
  simp only [map_add, map_mul]
  ring

lemma zquad'_natDegree (v : ℤ × ℤ) : (zquad' v).natDegree = 2 := by
  unfold zquad'; compute_degree!

lemma not_irr_mul12 (u : ℤ) (v : ℤ × ℤ) :
    ¬ Irreducible (zq3 (mul12 u v)) := by
  rw [zq3_mul12]
  intro hi
  rcases hi.isUnit_or_isUnit rfl with h | h
  · exact Polynomial.not_isUnit_of_natDegree_pos _
      (by rw [zlin_natDegree]; norm_num) h
  · exact Polynomial.not_isUnit_of_natDegree_pos _
      (by rw [zquad'_natDegree]; norm_num) h

/-- Negation invariance for cubics, tuple-level. -/
lemma tie3_neg_eq :
    ((zq3 (0, -1, 1)).map (Int.castRingHom ℂ)).mahlerMeasure
      = ((zq3 (0, -1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  rw [map_zq3, map_zq3]
  push_cast
  have h := mahlerMeasure_comp_neg (q3_monic 0 (-1) (-1))
  rw [q3_comp_neg] at h
  have hneg : (-(q3 (-0) (-1) (-(-1)))).mahlerMeasure
      = (q3 (-0) (-1) (-(-1))).mahlerMeasure := by
    rw [show (-(q3 (-0) (-1) (-(-1)))) = C (-1) * q3 (-0) (-1) (-(-1)) by
        rw [map_neg, map_one, neg_one_mul],
      mahlerMeasure_mul, mahlerMeasure_const]
    simp
  rw [hneg] at h
  norm_num at h ⊢
  exact h

lemma q3_prod_roots (a b c : ℂ) : (q3 a b c).roots.prod = -c := by
  have h := congrArg (eval 0) (monic_eq_prod_roots (q3_monic a b c))
  rw [eval_multiset_prod, Multiset.map_map] at h
  have h2 : eval 0 (q3 a b c) = c := by simp [q3]
  have h3 : ((q3 a b c).roots.map (eval 0 ∘ fun r => X - C r))
      = (q3 a b c).roots.map fun r => -(id r) := by
    refine Multiset.map_congr rfl ?_
    intro r _
    simp
  rw [h2, h3, prod_map_neg', q3_roots_card] at h
  simp only [id] at h
  norm_num at h
  linear_combination h

/-- Cubic root-inversion (reversal) identity. -/
lemma prod_roots_inv3 (a b c : ℂ) (hc : c ≠ 0) :
    ((q3 a b c).roots.map fun r => X - C r⁻¹).prod
      = q3 (b/c) (a/c) (1/c) := by
  have hprodr : (q3 a b c).roots.prod = -c := q3_prod_roots a b c
  have hroots0 : ∀ r ∈ (q3 a b c).roots, r ≠ 0 := by
    intro r hr h0
    subst h0
    have h := isRoot_of_mem_roots hr
    simp [q3, IsRoot] at h
    exact hc h
  apply Polynomial.funext
  intro y
  rw [eval_multiset_prod, Multiset.map_map]
  have hinv : ((q3 a b c).roots.map fun r => r⁻¹).prod = -c⁻¹ := by
    rw [Multiset.prod_map_inv]
    simp [hprodr]
  by_cases hy : y = 0
  · subst hy
    have hmap : ((q3 a b c).roots.map (eval 0 ∘ fun r => X - C r⁻¹))
        = (q3 a b c).roots.map fun r => -(fun r : ℂ => r⁻¹) r := by
      refine Multiset.map_congr rfl ?_
      intro r _
      simp
    rw [hmap, prod_map_neg' _ (fun r => r⁻¹), q3_roots_card, hinv]
    simp only [q3, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    ring
  · have hstep : ((q3 a b c).roots.map
          (eval y ∘ fun r => X - C r⁻¹)).prod
        = ((q3 a b c).roots.map fun r => r⁻¹ * (r * y - 1)).prod := by
      refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
      intro r hr
      have hr0 := hroots0 r hr
      simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
      field_simp
    have hsplit : ((q3 a b c).roots.map fun r => r⁻¹ * (r * y - 1)).prod
        = ((q3 a b c).roots.map fun r => r⁻¹).prod
          * ((q3 a b c).roots.map fun r => r * y - 1).prod := by
      rw [← Multiset.prod_map_mul]
    have hfactor : ((q3 a b c).roots.map fun r => r * y - 1)
        = (q3 a b c).roots.map fun r => y * (r - y⁻¹) := by
      refine Multiset.map_congr rfl ?_
      intro r _
      field_simp
    have hconst : ((q3 a b c).roots.map fun _ => y).prod = y ^ 3 := by
      rw [Multiset.map_const', Multiset.prod_replicate, q3_roots_card]
    have hshift : ((q3 a b c).roots.map fun r => r - y⁻¹).prod
        = -eval y⁻¹ (q3 a b c) := by
      have hs : ((q3 a b c).roots.map fun r => r - y⁻¹)
          = (q3 a b c).roots.map fun r => -(fun r : ℂ => y⁻¹ - r) r := by
        refine Multiset.map_congr rfl ?_
        intro r _
        ring_nf
      rw [hs, prod_map_neg' _ (fun r => y⁻¹ - r), q3_roots_card]
      have h3 : ((-1 : ℂ)) ^ (3:ℕ) = -1 := by norm_num
      rw [h3]
      have heval : ((q3 a b c).roots.map fun r => y⁻¹ - r).prod
          = eval y⁻¹ (q3 a b c) := by
        conv_rhs => rw [monic_eq_prod_roots (q3_monic a b c)]
        rw [eval_multiset_prod, Multiset.map_map]
        refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
        intro r _
        simp
      rw [heval]
      ring
    have hG : ((q3 a b c).roots.map fun r => r * y - 1).prod
        = -(y ^ 3 * eval y⁻¹ (q3 a b c)) := by
      rw [hfactor]
      have hmul : ((q3 a b c).roots.map fun r => y * (r - y⁻¹)).prod
          = ((q3 a b c).roots.map fun _ => y).prod
            * ((q3 a b c).roots.map fun r => r - y⁻¹).prod := by
        rw [← Multiset.prod_map_mul]
      rw [hmul, hconst, hshift]
      ring
    rw [hstep, hsplit, hinv, hG]
    simp only [q3, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    field_simp
    ring

/-- Reversal invariance for cubics at unit constant term. -/
lemma mahlerMeasure_q3_inv (a b c : ℂ) (hc : ‖c‖ = 1) :
    (q3 (b/c) (a/c) (1/c)).mahlerMeasure = (q3 a b c).mahlerMeasure := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hc
    simp at hc
  have hroots0 : ∀ r ∈ (q3 a b c).roots, r ≠ 0 := by
    intro r hr h0
    subst h0
    have h := isRoot_of_mem_roots hr
    simp [q3, IsRoot] at h
    exact hc0 h
  have hmap : ((q3 a b c).roots.map fun r => X - C r⁻¹)
      = Multiset.map (fun r => X - C r) ((q3 a b c).roots.map fun r => r⁻¹) := by
    rw [Multiset.map_map]
    rfl
  rw [← prod_roots_inv3 a b c hc0, hmap, mahlerMeasure_multiset_prod_X_sub_C,
    Multiset.map_map, mahlerMeasure_eq_prod_roots (q3_monic a b c)]
  have hpt : ((q3 a b c).roots.map
        ((fun r => max 1 ‖r‖) ∘ fun r => r⁻¹))
      = (q3 a b c).roots.map fun r => max 1 ‖r‖ / ‖r‖ := by
    refine Multiset.map_congr rfl ?_
    intro r hr
    exact max_one_norm_inv (hroots0 r hr)
  rw [hpt]
  have hdiv : ((q3 a b c).roots.map fun r => max 1 ‖r‖ / ‖r‖).prod
      = ((q3 a b c).roots.map fun r => max 1 ‖r‖).prod
        / ((q3 a b c).roots.map fun r => ‖r‖).prod := by
    rw [← Multiset.prod_map_div]
  have hprodr : (q3 a b c).roots.prod = -c := q3_prod_roots a b c
  have hnorm : ((q3 a b c).roots.map fun r => ‖r‖).prod = 1 := by
    rw [← norm_prod_multiset, hprodr, norm_neg, hc]
  rw [hdiv, hnorm, div_one]

lemma tie3_rev_eq :
    ((zq3 (1, 0, -1)).map (Int.castRingHom ℂ)).mahlerMeasure
      = ((zq3 (0, -1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  rw [map_zq3, map_zq3]
  push_cast
  have h := mahlerMeasure_q3_inv 0 (-1) (-1) (by norm_num)
  norm_num at h ⊢
  exact h

lemma tie3_revneg_eq :
    ((zq3 (-1, 0, 1)).map (Int.castRingHom ℂ)).mahlerMeasure
      = ((zq3 (0, -1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  have h1 : ((zq3 (-1, 0, 1)).map (Int.castRingHom ℂ)).mahlerMeasure
      = ((zq3 (0, -1, 1)).map (Int.castRingHom ℂ)).mahlerMeasure := by
    rw [map_zq3, map_zq3]
    push_cast
    have h := mahlerMeasure_q3_inv 0 (-1) 1 (by norm_num)
    norm_num at h ⊢
    exact h
  rw [h1, tie3_neg_eq]

/-- `M(x³−x−1) ≤ 133/100`, by the K = 5 ℓ¹ certificate. -/
lemma fam3_upper :
    ((zq3 (0, -1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure
      ≤ (133 : ℝ) / 100 := by
  have h := upper_cert3_sound (t := (0, -1, -1)) (P := 133) (Q := 100)
    (by norm_num) (K := 5) (by decide)
  exact_mod_cast h

lemma mem_boxD3 {t : Z3} :
    t ∈ boxD3 ↔ |t.1| ≤ 3 ∧ |t.2.1| ≤ 3 ∧ |t.2.2| ≤ 1 := by
  obtain ⟨a, b, c⟩ := t
  simp [boxD3, Finset.mem_product, Finset.mem_Icc, abs_le]

lemma lowerCert3_succ_def (fuel : ℕ) (P2 Q2 : ℤ) (s : Z3) :
    lowerCert3 (fuel + 1) P2 Q2 s
      = (lowerHit3 P2 Q2 s || lowerCert3 fuel (P2 ^ 2) (Q2 ^ 2) (gr3Z s)) := rfl

lemma lowerCert3_of_not_mem {t : Z3} (h : t ∉ boxD3) :
    lowerCert3 9 133 100 t = true := by
  obtain ⟨a, b, c⟩ := t
  rw [mem_boxD3] at h
  have hd : 3 < |a| ∨ 3 < |b| ∨ 1 < |c| := by
    by_contra hc'
    push_neg at hc'
    exact h ⟨hc'.1, hc'.2.1, hc'.2.2⟩
  rw [lowerCert3_succ_def, Bool.or_eq_true]
  left
  unfold lowerHit3
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  rcases hd with h3 | h3b | h1c
  · right
    show 3 * 133 < |tupCoeff3 (a, b, c) 2| * 100
    have : tupCoeff3 (a, b, c) 2 = a := rfl
    rw [this]
    generalize |a| = m at h3 ⊢
    omega
  · left; right
    show 3 * 133 < |tupCoeff3 (a, b, c) 1| * 100
    have : tupCoeff3 (a, b, c) 1 = b := rfl
    rw [this]
    generalize |b| = m at h3b ⊢
    omega
  · left; left
    show 1 * 133 < |tupCoeff3 (a, b, c) 0| * 100
    have : tupCoeff3 (a, b, c) 0 = c := rfl
    rw [this]
    generalize |c| = m at h1c ⊢
    omega

/-- THE DEGREE-3 MAHLER MINIMALITY THEOREM. -/
theorem cubic_mahler_min (p : ℤ[X]) (hm : p.Monic) (hd : p.natDegree = 3)
    (hi : Irreducible p)
    (h1 : 1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure) :
    ((zq3 (0, -1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure
      ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
  have hp : p = zq3 (p.coeff 2, p.coeff 1, p.coeff 0) := eq_zq3_self p hm hd
  set t : Z3 := (p.coeff 2, p.coeff 1, p.coeff 0) with ht
  rw [hp] at h1 hi ⊢
  by_cases hbox : t ∈ boxD3
  · have hOK := boxD3_all t hbox
    unfold elemOK3 at hOK
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hOK
    rcases hOK with ((htie | hf12) | hcert)
    · simp only [tieList3, List.mem_cons, List.mem_singleton] at htie
      rcases htie with h | h | h | (h | hfalse)
      · rw [h]
      · rw [h, tie3_neg_eq]
      · rw [h, tie3_rev_eq]
      · rw [h, tie3_revneg_eq]
      · simp at hfalse
    · obtain ⟨pr, _, heq⟩ := hf12
      rw [← heq] at hi
      exact absurd hi (not_irr_mul12 pr.1 pr.2)
    · exact fam3_upper.trans (le_of_lt (lowerCert3_133_sound hcert))
  · exact fam3_upper.trans
      (le_of_lt (lowerCert3_133_sound (lowerCert3_of_not_mem hbox)))

end

/-! ## Degree 3: the exact constant is ρ, the smallest Pisot number -/

/-- Real roots of `x³ = x + 1` lie in `(33/25, 3/2)`: there is only the
one real root, ρ. -/
lemma rho_real_root_cases (x : ℝ) (hx : x ^ 3 = x + 1) :
    33/25 < x ∧ x < 3/2 := by
  constructor
  · by_contra hle
    push_neg at hle
    rcases le_or_gt x (-1) with h | h
    · nlinarith [hx, mul_nonneg (mul_nonneg
        (by linarith : (0:ℝ) ≤ -x) (by linarith : (0:ℝ) ≤ 1 - x))
        (by linarith : (0:ℝ) ≤ -1 - x)]
    · rcases le_or_gt x 0 with h0 | h0
      · nlinarith [hx, (by linarith : (0:ℝ) < x + 1),
          mul_nonneg (neg_nonneg.2 h0) (mul_self_nonneg x)]
      · rcases le_or_gt x 1 with h1 | h1
        · nlinarith [hx, mul_nonneg h0.le (by nlinarith : (0:ℝ) ≤ 1 - x^2)]
        · have hsq : x^2 ≤ (33/25)^2 := by nlinarith
          nlinarith [hx, mul_le_mul hle hsq (by positivity) (by norm_num)]
  · by_contra hle
    push_neg at hle
    have hsq : (3/2:ℝ)^2 ≤ x^2 := by nlinarith
    nlinarith [hx, mul_le_mul hle hsq (by positivity) (by linarith)]

lemma rho_real_root_unique {x y : ℝ} (hx : x ^ 3 = x + 1) (h1x : 1 < x)
    (hy : y ^ 3 = y + 1) (h1y : 1 < y) : x = y := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · nlinarith [hx, hy, mul_pos (sub_pos.2 h)
      (by nlinarith : (0:ℝ) < y^2 + y*x + x^2 - 1)]
  · nlinarith [hx, hy, mul_pos (sub_pos.2 h)
      (by nlinarith : (0:ℝ) < x^2 + x*y + y^2 - 1)]

noncomputable section

lemma fam3_lower_11 :
    (11 : ℝ) / 10
      < ((zq3 (0, -1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  have hs := lowerCert3_sound (P := 11) (Q := 10) (by norm_num) 9 0 (0, -1, -1)
  simp only [pow_zero, pow_one, Function.iterate_zero_apply] at hs
  have h' : lowerCert3 9 ((11 : ℕ) : ℤ) ((10 : ℕ) : ℤ) (0, -1, -1) = true := by
    exact_mod_cast (by decide : lowerCert3 9 (11 : ℤ) (10 : ℤ) (0, -1, -1) = true)
  exact_mod_cast hs h'

/-- **The exact constant at degree 3.** The minimal cubic Mahler measure
satisfies `M³ = M + 1` with `M > 1` — it IS ρ, the smallest Pisot number,
the Siegel constant. -/
theorem mahler_cubic_rho :
    (((zq3 (0, -1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure) ^ 3
        = ((zq3 (0, -1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure + 1
      ∧ 1 < ((zq3 (0, -1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  have hswitch : ((zq3 (0, -1, -1)).map (Int.castRingHom ℂ)) = q3 0 (-1) (-1) := by
    rw [map_zq3]
    norm_num
  rw [hswitch]
  set G : ℂ[X] := q3 0 (-1) (-1) with hG
  have hroot_eq : ∀ r ∈ G.roots, r ^ 3 = r + 1 := by
    intro r hr
    have h := isRoot_of_mem_roots hr
    simp only [hG, IsRoot, q3, eval_add, eval_mul, eval_pow, eval_X, eval_C,
      map_neg, map_one, eval_neg, eval_one] at h
    linear_combination h
  have hMup : G.mahlerMeasure ≤ 133/100 := by
    rw [← hswitch]
    exact_mod_cast fam3_upper
  have hMlow : 11/10 < G.mahlerMeasure := by
    rw [← hswitch]
    exact_mod_cast fam3_lower_11
  have hMform : G.mahlerMeasure = (G.roots.map fun r => max 1 ‖r‖).prod :=
    mahlerMeasure_eq_prod_roots (q3_monic _ _ _)
  have hexists : ∃ r ∈ G.roots, 1 < ‖r‖ := by
    by_contra hall
    push_neg at hall
    have hone : ∀ r ∈ G.roots, max 1 ‖r‖ = 1 := fun r hr =>
      max_eq_left (hall r hr)
    rw [hMform, Multiset.map_congr rfl hone] at hMlow
    simp at hMlow
    linarith
  obtain ⟨rstar, hrmem, hrbig⟩ := hexists
  have hrim : rstar.im = 0 := by
    by_contra him
    exact absurd (PDT.cubic_conj_norm_lt_one rstar (hroot_eq rstar hrmem) him)
      (not_lt.mpr hrbig.le)
  have hrre : rstar = ((rstar.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hrim]
  set x : ℝ := rstar.re with hxdef
  have hxroot : x ^ 3 = x + 1 := by
    have h := hroot_eq rstar hrmem
    rw [hrre] at h
    exact_mod_cast h
  have hxcases := rho_real_root_cases x hxroot
  have hx1 : 1 < x := by linarith [hxcases.1]
  have hxpos : 0 < x := by linarith
  have hnormx : ‖rstar‖ = x := by
    have h1 : ‖rstar‖ = |x| := by rw [hrre]; exact Complex.norm_real _
    rw [h1, abs_of_pos hxpos]
  have hcount : Multiset.count rstar G.roots = 1 := by
    have hge : 1 ≤ Multiset.count rstar G.roots :=
      Multiset.one_le_count_iff_mem.mpr hrmem
    by_contra hne
    have h2 : 2 ≤ Multiset.count rstar G.roots := by omega
    have hrep : Multiset.replicate 2 rstar ≤ G.roots :=
      Multiset.le_count_iff_replicate_le.mp h2
    obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp hrep
    have hform2 : (G.roots.map fun r => max 1 ‖r‖).prod
        = (max 1 ‖rstar‖) ^ 2 * (u.map fun r => max 1 ‖r‖).prod := by
      rw [hu, Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
        Multiset.prod_replicate]
    rw [hform2] at hMform
    have hsq : (max 1 ‖rstar‖) ^ 2 = x ^ 2 := by
      rw [hnormx, max_eq_right hx1.le]
    rw [hsq] at hMform
    have hx2 : (33/25 : ℝ)^2 < x ^ 2 := by nlinarith [hxcases.1]
    nlinarith [hMform, hMup, one_le_prod_max u, hx2]
  have herase : ∀ r ∈ G.roots.erase rstar, max 1 ‖r‖ = 1 := by
    intro r hr
    have hrmem' : r ∈ G.roots := Multiset.mem_of_mem_erase hr
    have hrne : r ≠ rstar := by
      intro h
      subst h
      have hcz : Multiset.count r (G.roots.erase r) = 0 := by
        simp [Multiset.count_erase_self, hcount]
      exact absurd hr (Multiset.count_eq_zero.mp hcz)
    apply max_eq_left
    by_cases him : r.im = 0
    · have hre : r = ((r.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
      have hroot' : r.re ^ 3 = r.re + 1 := by
        have h := hroot_eq r hrmem'
        rw [hre] at h
        exact_mod_cast h
      exfalso
      apply hrne
      rw [hre, hrre]
      norm_cast
      exact rho_real_root_unique hroot'
        (by linarith [(rho_real_root_cases _ hroot').1]) hxroot hx1
    · exact (PDT.cubic_conj_norm_lt_one r (hroot_eq r hrmem') him).le
  have hMx : G.mahlerMeasure = x := by
    rw [hMform, ← Multiset.prod_map_erase (f := fun r => max 1 ‖r‖) hrmem]
    rw [Multiset.map_congr rfl herase]
    simp [hnormx, max_eq_right hx1.le]
  constructor
  · rw [hMx]; exact hxroot
  · rw [hMx]; exact hx1

/-- Pretty statement: `zq3 (0,−1,−1)` is `X³ − X − 1`. -/
lemma zq3_fam : zq3 (0, -1, -1) = X ^ 3 - X - 1 := by
  unfold zq3; simp; ring

theorem cubic_mahler_min' (p : ℤ[X]) (hm : p.Monic) (hd : p.natDegree = 3)
    (hi : Irreducible p)
    (h1 : 1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure) :
    ((((X : ℤ[X]) ^ 3 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure
      ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
  rw [← zq3_fam]
  exact cubic_mahler_min p hm hd hi h1

end

/-! ## Degree 2: the full stack -/

noncomputable section

def q2 (a b : ℂ) : ℂ[X] := X ^ 2 + C a * X + C b

lemma q2_monic (a b : ℂ) : (q2 a b).Monic := by
  unfold q2; monicity!

lemma q2_natDegree (a b : ℂ) : (q2 a b).natDegree = 2 := by
  unfold q2; compute_degree!

lemma q2_comp_neg (a b : ℂ) : (q2 a b).comp (-X) = q2 (-a) b := by
  unfold q2
  simp only [add_comp, mul_comp, pow_comp, X_comp, C_comp, map_neg]
  ring

lemma q2_roots_card (a b : ℂ) : Multiset.card (q2 a b).roots = 2 := by
  have h := (IsAlgClosed.splits (k := ℂ) (q2 a b)).natDegree_eq_card_roots
  rw [q2_natDegree] at h
  omega

lemma prod_X_add_C_roots2 (a b : ℂ) :
    (((q2 a b).roots).map fun r => X + C r).prod = q2 (-a) b := by
  have h := prod_X_sub_C_comp_neg (q2 a b).roots
  rw [← monic_eq_prod_roots (q2_monic a b), q2_comp_neg, q2_roots_card,
    Even.neg_one_pow (by decide : Even 2), one_mul] at h
  rw [h]
  refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
  intro r _
  rw [map_neg, sub_neg_eq_add]

lemma gr2_ring (a b : ℂ) :
    q2 a b * q2 (-a) b = (q2 (2*b - a^2) (b^2)).comp (X ^ 2) := by
  unfold q2
  simp only [add_comp, mul_comp, pow_comp, X_comp, C_comp]
  simp only [map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]
  ring

lemma mahlerMeasure_gr2 (a b : ℂ) :
    (q2 (2*b - a^2) (b^2)).mahlerMeasure = (q2 a b).mahlerMeasure ^ 2 := by
  have key : q2 (2*b - a^2) (b^2)
      = (((q2 a b).roots.map fun r => r ^ 2).map fun r => X - C r).prod := by
    apply comp_X_sq_injective
    rw [multiset_prod_comp, Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def, sub_comp, X_comp, C_comp]
    rw [prod_X_sq_sub_sq, prod_X_add_C_roots2,
      ← monic_eq_prod_roots (q2_monic a b), gr2_ring]
  rw [key, mahlerMeasure_multiset_prod_X_sub_C, Multiset.map_map,
    mahlerMeasure_eq_prod_roots (q2_monic a b), pow_two,
    ← Multiset.prod_map_mul]
  refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
  intro r _
  exact max_one_norm_sq r

end

abbrev Z2 := ℤ × ℤ

def gr2Z : Z2 → Z2
  | (a, b) => (2*b - a^2, b^2)

def tupCoeff2 : Z2 → ℕ → ℤ
  | (_, b), 0 => b
  | (a, _), 1 => a
  | _, 2 => 1
  | _, _ => 0

def tupL1_2 : Z2 → ℤ
  | (a, b) => 1 + |a| + |b|

noncomputable section

def zq2 (t : Z2) : ℤ[X] := X ^ 2 + C t.1 * X + C t.2

lemma map_zq2 (t : Z2) :
    (zq2 t).map (Int.castRingHom ℂ) = q2 (t.1 : ℂ) (t.2 : ℂ) := by
  unfold zq2 q2
  simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_C]

lemma natDegree_map_zq2 (t : Z2) :
    ((zq2 t).map (Int.castRingHom ℂ)).natDegree = 2 := by
  rw [map_zq2]; exact q2_natDegree _ _

lemma mahlerMeasure_map_gr2Z (t : Z2) :
    ((zq2 (gr2Z t)).map (Int.castRingHom ℂ)).mahlerMeasure
      = ((zq2 t).map (Int.castRingHom ℂ)).mahlerMeasure ^ 2 := by
  obtain ⟨a, b⟩ := t
  rw [map_zq2, map_zq2]
  have harg : q2 ((gr2Z (a, b)).1 : ℂ) ((gr2Z (a, b)).2 : ℂ)
      = q2 (2*(b:ℂ) - (a:ℂ)^2) ((b:ℂ)^2) := by
    show q2 ((2*b - a^2 : ℤ) : ℂ) ((b^2 : ℤ) : ℂ) = _
    congr 1 <;> push_cast <;> ring
  rw [harg, mahlerMeasure_gr2]

lemma mahlerMeasure_map_gr2Z_iterate (K : ℕ) (t : Z2) :
    ((zq2 (gr2Z^[K] t)).map (Int.castRingHom ℂ)).mahlerMeasure
      = ((zq2 t).map (Int.castRingHom ℂ)).mahlerMeasure ^ (2 ^ K) := by
  induction K generalizing t with
  | zero => simp
  | succ K ih =>
      rw [Function.iterate_succ_apply, ih (gr2Z t), mahlerMeasure_map_gr2Z,
        ← pow_mul]
      congr 1
      ring

lemma coeff_map_zq2 (t : Z2) (k : ℕ) (hk : k ≤ 2) :
    ((zq2 t).map (Int.castRingHom ℂ)).coeff k = (tupCoeff2 t k : ℂ) := by
  obtain ⟨a, b⟩ := t
  rw [map_zq2]
  interval_cases k <;> simp [q2, tupCoeff2, coeff_int_cast_CX]

lemma lower_cert2_sound {t : Z2} {P Q : ℕ} (hQ : 0 < Q) {K k : ℕ} (hk : k ≤ 2)
    (h : (Nat.choose 2 k : ℤ) * (P : ℤ) ^ (2 ^ K)
        < |tupCoeff2 (gr2Z^[K] t) k| * (Q : ℤ) ^ (2 ^ K)) :
    (P : ℝ) / Q < ((zq2 t).map (Int.castRingHom ℂ)).mahlerMeasure := by
  set M : ℝ := ((zq2 t).map (Int.castRingHom ℂ)).mahlerMeasure with hM
  have hM0 : 0 ≤ M := mahlerMeasure_nonneg _
  have hchoose : (0 : ℝ) < (Nat.choose 2 k : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos hk)
  have hQ0 : (0 : ℝ) < (Q : ℝ) ^ (2 ^ K) := by positivity
  have hbound := norm_coeff_le_choose_mul_mahlerMeasure k
      ((zq2 (gr2Z^[K] t)).map (Int.castRingHom ℂ))
  rw [natDegree_map_zq2, mahlerMeasure_map_gr2Z_iterate,
    coeff_map_zq2 _ _ hk] at hbound
  simp only [Complex.norm_intCast] at hbound
  rw [← hM] at hbound
  have hR : (Nat.choose 2 k : ℝ) * (P : ℝ) ^ (2 ^ K)
      < |((tupCoeff2 (gr2Z^[K] t) k : ℤ) : ℝ)| * (Q : ℝ) ^ (2 ^ K) := by
    exact_mod_cast h
  have step1 : (Nat.choose 2 k : ℝ) * (P : ℝ) ^ (2 ^ K)
      < (Nat.choose 2 k : ℝ) * (M ^ (2 ^ K) * (Q : ℝ) ^ (2 ^ K)) :=
    calc (Nat.choose 2 k : ℝ) * (P : ℝ) ^ (2 ^ K)
        < |((tupCoeff2 (gr2Z^[K] t) k : ℤ) : ℝ)| * (Q : ℝ) ^ (2 ^ K) := hR
      _ ≤ (Nat.choose 2 k : ℝ) * M ^ (2 ^ K) * (Q : ℝ) ^ (2 ^ K) :=
          mul_le_mul_of_nonneg_right hbound (le_of_lt hQ0)
      _ = (Nat.choose 2 k : ℝ) * (M ^ (2 ^ K) * (Q : ℝ) ^ (2 ^ K)) := by ring
  have hpow : ((P : ℝ) / Q) ^ (2 ^ K) < M ^ (2 ^ K) := by
    rw [div_pow, div_lt_iff₀ hQ0]
    exact lt_of_mul_lt_mul_left step1 (le_of_lt hchoose)
  exact lt_of_pow_lt_pow_left₀ _ hM0 hpow

lemma mahlerMeasure_map_zq2_le_l1 (s : Z2) :
    ((zq2 s).map (Int.castRingHom ℂ)).mahlerMeasure ≤ (tupL1_2 s : ℝ) := by
  refine (mahlerMeasure_le_sum_norm_coeff _).trans ?_
  rw [Polynomial.sum_def]
  have hsupp : ((zq2 s).map (Int.castRingHom ℂ)).support ⊆ Finset.range 3 := by
    intro n hn
    rw [Finset.mem_range]
    have h1 := Polynomial.le_natDegree_of_mem_supp n hn
    rw [natDegree_map_zq2] at h1
    omega
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsupp
    (fun i _ _ => norm_nonneg _)).trans ?_
  rw [show (3 : ℕ) = 2 + 1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one]
  rw [coeff_map_zq2 _ 0 (by norm_num), coeff_map_zq2 _ 1 (by norm_num),
    coeff_map_zq2 _ 2 (by norm_num)]
  obtain ⟨a, b⟩ := s
  simp only [tupCoeff2, tupL1_2, Complex.norm_intCast]
  push_cast
  rw [abs_one]
  linarith [abs_nonneg (a : ℝ), abs_nonneg (b : ℝ)]

lemma upper_cert2_sound {t : Z2} {P Q : ℕ} (hQ : 0 < Q) {K : ℕ}
    (h : tupL1_2 (gr2Z^[K] t) * (Q : ℤ) ^ (2 ^ K) ≤ (P : ℤ) ^ (2 ^ K)) :
    ((zq2 t).map (Int.castRingHom ℂ)).mahlerMeasure ≤ (P : ℝ) / Q := by
  set M : ℝ := ((zq2 t).map (Int.castRingHom ℂ)).mahlerMeasure with hM
  have hQ0 : (0 : ℝ) < (Q : ℝ) ^ (2 ^ K) := by positivity
  have hl1 := mahlerMeasure_map_zq2_le_l1 (gr2Z^[K] t)
  rw [mahlerMeasure_map_gr2Z_iterate, ← hM] at hl1
  have hR : (tupL1_2 (gr2Z^[K] t) : ℝ) * (Q : ℝ) ^ (2 ^ K)
      ≤ (P : ℝ) ^ (2 ^ K) := by exact_mod_cast h
  have hpow : M ^ (2 ^ K) ≤ ((P : ℝ) / Q) ^ (2 ^ K) := by
    rw [div_pow, le_div_iff₀ hQ0]
    exact (mul_le_mul_of_nonneg_right hl1 (le_of_lt hQ0)).trans hR
  exact le_of_pow_le_pow_left₀ (by positivity) (by positivity) hpow

end

def lowerHit2 (P2 Q2 : ℤ) (s : Z2) : Bool :=
  decide (1 * P2 < |tupCoeff2 s 0| * Q2) ||
  decide (2 * P2 < |tupCoeff2 s 1| * Q2)

def lowerCert2 : ℕ → ℤ → ℤ → Z2 → Bool
  | 0, _, _, _ => false
  | fuel + 1, P2, Q2, s =>
      lowerHit2 P2 Q2 s || lowerCert2 fuel (P2 ^ 2) (Q2 ^ 2) (gr2Z s)

noncomputable section

lemma lowerHit2_sound {P Q : ℕ} (hQ : 0 < Q) {K : ℕ} {t : Z2}
    (h : lowerHit2 ((P : ℤ) ^ 2 ^ K) ((Q : ℤ) ^ 2 ^ K) (gr2Z^[K] t) = true) :
    (P : ℝ) / Q < ((zq2 t).map (Int.castRingHom ℂ)).mahlerMeasure := by
  unfold lowerHit2 at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · have hc : ((Nat.choose 2 0 : ℕ) : ℤ) = 1 := by norm_num
    exact lower_cert2_sound (K := K) (k := 0) hQ (by norm_num)
      (by rw [hc]; exact h)
  · have hc : ((Nat.choose 2 1 : ℕ) : ℤ) = 2 := by norm_num
    exact lower_cert2_sound (K := K) (k := 1) hQ (by norm_num)
      (by rw [hc]; exact h)

lemma lowerCert2_sound {P Q : ℕ} (hQ : 0 < Q) :
    ∀ (fuel K : ℕ) (t : Z2),
      lowerCert2 fuel ((P : ℤ) ^ 2 ^ K) ((Q : ℤ) ^ 2 ^ K) (gr2Z^[K] t) = true →
      (P : ℝ) / Q < ((zq2 t).map (Int.castRingHom ℂ)).mahlerMeasure := by
  intro fuel
  induction fuel with
  | zero => intro K t h; simp [lowerCert2] at h
  | succ fuel ih =>
      intro K t h
      unfold lowerCert2 at h
      simp only [Bool.or_eq_true] at h
      rcases h with h1 | h2
      · exact lowerHit2_sound hQ h1
      · have e1 : ((P : ℤ) ^ 2 ^ K) ^ 2 = (P : ℤ) ^ 2 ^ (K + 1) := by
          rw [← pow_mul, pow_succ]
        have e2 : ((Q : ℤ) ^ 2 ^ K) ^ 2 = (Q : ℤ) ^ 2 ^ (K + 1) := by
          rw [← pow_mul, pow_succ]
        have e3 : gr2Z (gr2Z^[K] t) = gr2Z^[K + 1] t :=
          (Function.iterate_succ_apply' gr2Z K t).symm
        rw [e1, e2, e3] at h2
        exact ih (K + 1) t h2

lemma lowerCert2_81_sound {t : Z2} (h : lowerCert2 9 81 50 t = true) :
    (81 : ℝ) / 50 < ((zq2 t).map (Int.castRingHom ℂ)).mahlerMeasure := by
  have hs := lowerCert2_sound (P := 81) (Q := 50) (by norm_num) 9 0 t
  simp only [pow_zero, pow_one, Function.iterate_zero_apply] at hs
  have h' : lowerCert2 9 ((81 : ℕ) : ℤ) ((50 : ℕ) : ℤ) t = true := by
    exact_mod_cast h
  exact_mod_cast hs h'

end

def tieList2 : List Z2 := [(-1, -1), (1, -1)]

def cycloList2 : List Z2 := [(1, 1), (0, 1), (-1, 1)]

def mul11 (u v : ℤ) : Z2 := (u + v, u * v)

def facts11 : List (ℤ × ℤ) := [(-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 1)]

def elemOK2 (t : Z2) : Bool :=
  decide (t ∈ tieList2) || decide (t ∈ cycloList2) ||
  facts11.any (fun p => decide (mul11 p.1 p.2 = t)) ||
  lowerCert2 9 81 50 t

noncomputable def boxD2 : Finset Z2 :=
  (Finset.Icc (-3 : ℤ) 3) ×ˢ (Finset.Icc (-1 : ℤ) 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- COVERAGE at degree 2: 21 kernel-checked certificates. -/
theorem boxD2_all : ∀ t ∈ boxD2, elemOK2 t = true := by decide

noncomputable section

lemma zq2_monic_int (t : Z2) : (zq2 t).Monic := by
  unfold zq2; monicity!

lemma zq2_natDegree_int (t : Z2) : (zq2 t).natDegree = 2 := by
  unfold zq2; compute_degree!

lemma coeff_zq2 (t : Z2) (k : ℕ) (hk : k ≤ 2) :
    (zq2 t).coeff k = tupCoeff2 t k := by
  obtain ⟨a, b⟩ := t
  interval_cases k <;> simp [zq2, tupCoeff2, coeff_int_cast_ZX]

lemma eq_zq2_self (p : ℤ[X]) (hm : p.Monic) (hd : p.natDegree = 2) :
    p = zq2 (p.coeff 1, p.coeff 0) := by
  ext n
  by_cases hn : n ≤ 2
  · interval_cases n
    · rw [coeff_zq2 _ 0 (by norm_num)]; rfl
    · rw [coeff_zq2 _ 1 (by norm_num)]; rfl
    · rw [coeff_zq2 _ 2 (by norm_num)]
      show p.coeff 2 = 1
      have := hm.coeff_natDegree
      rwa [hd] at this
  · push_neg at hn
    rw [coeff_eq_zero_of_natDegree_lt (by rw [hd]; omega),
      coeff_eq_zero_of_natDegree_lt (by rw [zq2_natDegree_int]; omega)]

lemma zq2_mul11 (u v : ℤ) : zq2 (mul11 u v) = zlin u * zlin v := by
  unfold zq2 mul11 zlin
  simp only [map_add, map_mul]
  ring

lemma not_irr_mul11 (u v : ℤ) : ¬ Irreducible (zq2 (mul11 u v)) := by
  rw [zq2_mul11]
  intro hi
  rcases hi.isUnit_or_isUnit rfl with h | h
  · exact Polynomial.not_isUnit_of_natDegree_pos _
      (by rw [zlin_natDegree]; norm_num) h
  · exact Polynomial.not_isUnit_of_natDegree_pos _
      (by rw [zlin_natDegree]; norm_num) h

/-- A monic quadratic dividing `Xⁿ − 1` has Mahler measure 1. -/
lemma mahler2_eq_one_of_dvd {t : Z2} {g : ℤ[X]} {n : ℕ}
    (hn : 0 < n) (hfac : zq2 t * g = X ^ n - 1) :
    ((zq2 t).map (Int.castRingHom ℂ)).mahlerMeasure = 1 := by
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
  have h1t : 1 ≤ ((zq2 t).map (Int.castRingHom ℂ)).mahlerMeasure :=
    one_le_mahlerMeasure_of_ne_zero (zq2_monic_int t).ne_zero
  have h1g : 1 ≤ (g.map (Int.castRingHom ℂ)).mahlerMeasure :=
    one_le_mahlerMeasure_of_ne_zero hg
  have hle : ((zq2 t).map (Int.castRingHom ℂ)).mahlerMeasure ≤ 1 := by
    calc ((zq2 t).map (Int.castRingHom ℂ)).mahlerMeasure
        ≤ ((zq2 t).map (Int.castRingHom ℂ)).mahlerMeasure
            * (g.map (Int.castRingHom ℂ)).mahlerMeasure :=
          le_mul_of_one_le_right (le_trans zero_le_one h1t) h1g
      _ = 1 := hM
  exact le_antisymm hle h1t

lemma cyclo3_fac2 : zq2 (1, 1) * (X - 1) = X ^ 3 - 1 := by
  unfold zq2; simp; ring

lemma cyclo4_fac2 : zq2 (0, 1) * (X ^ 2 - 1) = X ^ 4 - 1 := by
  unfold zq2; simp; ring

lemma cyclo6_fac2 :
    zq2 (-1, 1) * (X ^ 4 + X ^ 3 - X - 1) = X ^ 6 - 1 := by
  unfold zq2; simp; ring

lemma tie2_neg_eq :
    ((zq2 (1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure
      = ((zq2 (-1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  rw [map_zq2, map_zq2]
  push_cast
  have h := mahlerMeasure_comp_neg (q2_monic (-1) (-1))
  rw [q2_comp_neg] at h
  norm_num at h ⊢
  exact h

lemma fam2_upper :
    ((zq2 (-1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure
      ≤ (81 : ℝ) / 50 := by
  have h := upper_cert2_sound (t := (-1, -1)) (P := 81) (Q := 50)
    (by norm_num) (K := 4) (by decide)
  exact_mod_cast h

lemma mem_boxD2 {t : Z2} :
    t ∈ boxD2 ↔ |t.1| ≤ 3 ∧ |t.2| ≤ 1 := by
  obtain ⟨a, b⟩ := t
  simp [boxD2, Finset.mem_product, Finset.mem_Icc, abs_le]

lemma lowerCert2_succ_def (fuel : ℕ) (P2 Q2 : ℤ) (s : Z2) :
    lowerCert2 (fuel + 1) P2 Q2 s
      = (lowerHit2 P2 Q2 s || lowerCert2 fuel (P2 ^ 2) (Q2 ^ 2) (gr2Z s)) := rfl

lemma lowerCert2_of_not_mem {t : Z2} (h : t ∉ boxD2) :
    lowerCert2 9 81 50 t = true := by
  obtain ⟨a, b⟩ := t
  rw [mem_boxD2] at h
  have hd : 3 < |a| ∨ 1 < |b| := by
    by_contra hc'
    push_neg at hc'
    exact h ⟨hc'.1, hc'.2⟩
  rw [lowerCert2_succ_def, Bool.or_eq_true]
  left
  unfold lowerHit2
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  rcases hd with h3 | h1b
  · right
    show 2 * 81 < |tupCoeff2 (a, b) 1| * 50
    have : tupCoeff2 (a, b) 1 = a := rfl
    rw [this]
    generalize |a| = m at h3 ⊢
    omega
  · left
    show 1 * 81 < |tupCoeff2 (a, b) 0| * 50
    have : tupCoeff2 (a, b) 0 = b := rfl
    rw [this]
    generalize |b| = m at h1b ⊢
    omega

/-- THE DEGREE-2 MAHLER MINIMALITY THEOREM. -/
theorem quadratic_mahler_min (p : ℤ[X]) (hm : p.Monic) (hd : p.natDegree = 2)
    (hi : Irreducible p)
    (h1 : 1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure) :
    ((zq2 (-1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure
      ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
  have hp : p = zq2 (p.coeff 1, p.coeff 0) := eq_zq2_self p hm hd
  set t : Z2 := (p.coeff 1, p.coeff 0) with ht
  rw [hp] at h1 hi ⊢
  by_cases hbox : t ∈ boxD2
  · have hOK := boxD2_all t hbox
    unfold elemOK2 at hOK
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hOK
    rcases hOK with (((htie | hcyc) | hf11) | hcert)
    · simp only [tieList2, List.mem_cons, List.mem_singleton] at htie
      rcases htie with h | (h | hfalse)
      · rw [h]
      · rw [h, tie2_neg_eq]
      · simp at hfalse
    · simp only [cycloList2, List.mem_cons, List.mem_singleton] at hcyc
      have hMone : ((zq2 t).map (Int.castRingHom ℂ)).mahlerMeasure = 1 := by
        rcases hcyc with h | (h | (h | hfalse))
        · rw [h]; exact mahler2_eq_one_of_dvd (by norm_num) cyclo3_fac2
        · rw [h]; exact mahler2_eq_one_of_dvd (by norm_num) cyclo4_fac2
        · rw [h]; exact mahler2_eq_one_of_dvd (by norm_num) cyclo6_fac2
        · simp at hfalse
      rw [hMone] at h1
      exact absurd h1 (lt_irrefl 1)
    · obtain ⟨pr, _, heq⟩ := hf11
      rw [← heq] at hi
      exact absurd hi (not_irr_mul11 pr.1 pr.2)
    · exact fam2_upper.trans (le_of_lt (lowerCert2_81_sound hcert))
  · exact fam2_upper.trans
      (le_of_lt (lowerCert2_81_sound (lowerCert2_of_not_mem hbox)))

/-! ### Degree 2: the exact constant is the golden ratio -/

/-- The quadratic `x² = x + 1` has no non-real roots. -/
lemma phi_no_nonreal (r : ℂ) (hr : r ^ 2 = r + 1) : r.im = 0 := by
  by_contra him
  have h1 := congrArg Complex.im hr
  have h2 := congrArg Complex.re hr
  simp only [pow_two, Complex.mul_im, Complex.mul_re, Complex.add_im,
    Complex.add_re, Complex.one_im, Complex.one_re] at h1 h2
  have hre : r.re = 1/2 := by
    have : r.im * (2 * r.re - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h him
    · linarith
  rw [hre] at h2
  nlinarith [sq_nonneg r.im]

lemma phi_real_root_cases (x : ℝ) (hx : x ^ 2 = x + 1) :
    (-1 < x ∧ x < 0) ∨ (8/5 < x ∧ x < 2) := by
  have hne0 : x ≠ 0 := by intro h; rw [h] at hx; norm_num at hx
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · left
    refine ⟨?_, hneg⟩
    by_contra hle
    push_neg at hle
    nlinarith [hx]
  · exact absurd hzero hne0
  · right
    constructor
    · by_contra hle
      push_neg at hle
      nlinarith [hx, hpos]
    · by_contra hle
      push_neg at hle
      nlinarith [hx]

lemma phi_real_root_unique {x y : ℝ} (hx : x ^ 2 = x + 1) (h1x : 1 < x)
    (hy : y ^ 2 = y + 1) (h1y : 1 < y) : x = y := by
  nlinarith [hx, hy, sq_nonneg (x - y), sq_nonneg (x + y)]

lemma fam2_lower_11 :
    (11 : ℝ) / 10
      < ((zq2 (-1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  have hs := lowerCert2_sound (P := 11) (Q := 10) (by norm_num) 9 0 (-1, -1)
  simp only [pow_zero, pow_one, Function.iterate_zero_apply] at hs
  have h' : lowerCert2 9 ((11 : ℕ) : ℤ) ((10 : ℕ) : ℤ) (-1, -1) = true := by
    exact_mod_cast (by decide : lowerCert2 9 (11 : ℤ) (10 : ℤ) (-1, -1) = true)
  exact_mod_cast hs h'

/-- **The exact constant at degree 2.** The minimal quadratic Mahler measure
satisfies `M² = M + 1` with `M > 1` — it IS the golden ratio φ. -/
theorem mahler_quadratic_phi :
    (((zq2 (-1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure) ^ 2
        = ((zq2 (-1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure + 1
      ∧ 1 < ((zq2 (-1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  have hswitch : ((zq2 (-1, -1)).map (Int.castRingHom ℂ)) = q2 (-1) (-1) := by
    rw [map_zq2]
    norm_num
  rw [hswitch]
  set G : ℂ[X] := q2 (-1) (-1) with hG
  have hroot_eq : ∀ r ∈ G.roots, r ^ 2 = r + 1 := by
    intro r hr
    have h := isRoot_of_mem_roots hr
    simp only [hG, IsRoot, q2, eval_add, eval_mul, eval_pow, eval_X, eval_C,
      map_neg, map_one, eval_neg, eval_one] at h
    linear_combination h
  have hMup : G.mahlerMeasure ≤ 81/50 := by
    rw [← hswitch]
    exact_mod_cast fam2_upper
  have hMlow : 11/10 < G.mahlerMeasure := by
    rw [← hswitch]
    exact_mod_cast fam2_lower_11
  have hMform : G.mahlerMeasure = (G.roots.map fun r => max 1 ‖r‖).prod :=
    mahlerMeasure_eq_prod_roots (q2_monic _ _)
  have hexists : ∃ r ∈ G.roots, 1 < ‖r‖ := by
    by_contra hall
    push_neg at hall
    have hone : ∀ r ∈ G.roots, max 1 ‖r‖ = 1 := fun r hr =>
      max_eq_left (hall r hr)
    rw [hMform, Multiset.map_congr rfl hone] at hMlow
    simp at hMlow
    linarith
  obtain ⟨rstar, hrmem, hrbig⟩ := hexists
  have hrim : rstar.im = 0 := phi_no_nonreal rstar (hroot_eq rstar hrmem)
  have hrre : rstar = ((rstar.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hrim]
  set x : ℝ := rstar.re with hxdef
  have hxroot : x ^ 2 = x + 1 := by
    have h := hroot_eq rstar hrmem
    rw [hrre] at h
    exact_mod_cast h
  have hxbig : 8/5 < x ∧ x < 2 := by
    rcases phi_real_root_cases x hxroot with ⟨ha, hb⟩ | h
    · exfalso
      have h1 : ‖rstar‖ = |x| := by rw [hrre]; exact Complex.norm_real _
      rw [h1] at hrbig
      have : |x| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
      linarith
    · exact h
  have hx1 : 1 < x := by linarith [hxbig.1]
  have hxpos : 0 < x := by linarith
  have hnormx : ‖rstar‖ = x := by
    have h1 : ‖rstar‖ = |x| := by rw [hrre]; exact Complex.norm_real _
    rw [h1, abs_of_pos hxpos]
  have hcount : Multiset.count rstar G.roots = 1 := by
    have hge : 1 ≤ Multiset.count rstar G.roots :=
      Multiset.one_le_count_iff_mem.mpr hrmem
    by_contra hne
    have h2 : 2 ≤ Multiset.count rstar G.roots := by omega
    have hrep : Multiset.replicate 2 rstar ≤ G.roots :=
      Multiset.le_count_iff_replicate_le.mp h2
    obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp hrep
    have hform2 : (G.roots.map fun r => max 1 ‖r‖).prod
        = (max 1 ‖rstar‖) ^ 2 * (u.map fun r => max 1 ‖r‖).prod := by
      rw [hu, Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
        Multiset.prod_replicate]
    rw [hform2] at hMform
    have hsq : (max 1 ‖rstar‖) ^ 2 = x ^ 2 := by
      rw [hnormx, max_eq_right hx1.le]
    rw [hsq] at hMform
    have hx2 : (8/5 : ℝ)^2 < x ^ 2 := by nlinarith [hxbig.1]
    nlinarith [hMform, hMup, one_le_prod_max u, hx2]
  have herase : ∀ r ∈ G.roots.erase rstar, max 1 ‖r‖ = 1 := by
    intro r hr
    have hrmem' : r ∈ G.roots := Multiset.mem_of_mem_erase hr
    have hrne : r ≠ rstar := by
      intro h
      subst h
      have hcz : Multiset.count r (G.roots.erase r) = 0 := by
        simp [Multiset.count_erase_self, hcount]
      exact absurd hr (Multiset.count_eq_zero.mp hcz)
    apply max_eq_left
    have him : r.im = 0 := phi_no_nonreal r (hroot_eq r hrmem')
    have hre : r = ((r.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
    have hroot' : r.re ^ 2 = r.re + 1 := by
      have h := hroot_eq r hrmem'
      rw [hre] at h
      exact_mod_cast h
    have hnr : ‖r‖ = |r.re| := by rw [hre]; exact Complex.norm_real _
    rcases phi_real_root_cases r.re hroot' with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [hnr]
      rw [abs_le]
      constructor <;> linarith
    · exfalso
      apply hrne
      rw [hre, hrre]
      norm_cast
      exact phi_real_root_unique hroot' (by linarith) hxroot hx1
  have hMx : G.mahlerMeasure = x := by
    rw [hMform, ← Multiset.prod_map_erase (f := fun r => max 1 ‖r‖) hrmem]
    rw [Multiset.map_congr rfl herase]
    simp [hnormx, max_eq_right hx1.le]
  constructor
  · rw [hMx]; exact hxroot
  · rw [hMx]; exact hx1

/-- Pretty statement: `zq2 (−1,−1)` is `X² − X − 1`. -/
lemma zq2_fam : zq2 (-1, -1) = X ^ 2 - X - 1 := by
  unfold zq2; simp; ring

theorem quadratic_mahler_min' (p : ℤ[X]) (hm : p.Monic) (hd : p.natDegree = 2)
    (hi : Irreducible p)
    (h1 : 1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure) :
    ((((X : ℤ[X]) ^ 2 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure
      ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure := by
  rw [← zq2_fam]
  exact quadratic_mahler_min p hm hd hi h1

end

/-! ### The minimizers are in the competitor class: irreducibility
(mock-referee finding 2: put attainment on the compared surface) -/

noncomputable section

/-- `x² − x − 1` is irreducible over ℤ (reduction mod 2). -/
lemma fam2_irreducible : Irreducible ((X : ℤ[X]) ^ 2 - X - 1) := by
  have hm : ((X : ℤ[X]) ^ 2 - X - 1).Monic := by monicity!
  apply hm.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2))
  have hmap : ((X : ℤ[X]) ^ 2 - X - 1).map (Int.castRingHom (ZMod 2))
      = X ^ 2 + X + 1 := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one]
    have h2 : (2 : (ZMod 2)[X]) = 0 := by
      have e : (2 : ZMod 2) = 0 := by decide
      calc (2 : (ZMod 2)[X]) = C (2 : ZMod 2) := (C_ofNat 2).symm
        _ = C (0 : ZMod 2) := by rw [e]
        _ = 0 := by simp
    linear_combination (-(X : (ZMod 2)[X]) - 1) * h2
  rw [hmap]
  exact PDT.quad_irred_zmod2

/-- `x³ − x − 1` is irreducible over ℤ (PdtIrreducible, reduction mod 2). -/
lemma fam3_irreducible : Irreducible ((X : ℤ[X]) ^ 3 - X - 1) := by
  have h := PDT.cubicZ_irred
  rwa [show PDT.cubicZ = (X : ℤ[X]) ^ 3 - X - 1 from rfl] at h

/-- `x⁴ − x − 1` is irreducible over ℤ (PdtIrreducible, reduction mod 2). -/
lemma fam4_irreducible : Irreducible ((X : ℤ[X]) ^ 4 - X - 1) := by
  have h := PDT.quarticZ_irred
  rwa [show PDT.quarticZ = (X : ℤ[X]) ^ 4 - X - 1 from rfl] at h

end

end Mahler
end PDT


