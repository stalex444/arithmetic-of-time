/-
PdtMahler — the degree-window Mahler extremality, positives (Lean side).

Target:
  for d ∈ {2,3,4}: min{ M(f) : f monic irreducible in ℤ[x], deg f = d,
  M(f) > 1 } is attained by x^d − x − 1.

Architecture (validated first on a prototype): coefficient-bound box at rational θ + per-element integer
certificates (TIE / CYCLO / FACTOR / GRAEFFE), all sound via
M(graeffe e) = M(e)² and Mathlib's `norm_coeff_le_choose_mul_mahlerMeasure`.

Phase A: the workhorse (M of a product of monic linear factors), the
explicit monic quartic, negation invariance.
-/
module
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.NumberTheory.MahlerMeasure

@[expose] public section

namespace PDT
namespace Mahler
open Polynomial

noncomputable section

/-- The Mahler measure of a product of monic linear factors is the product
of `max 1 ‖root‖`: the workhorse identity behind every invariance lemma. -/
lemma mahlerMeasure_multiset_prod_X_sub_C (s : Multiset ℂ) :
    ((s.map fun r => X - C r).prod).mahlerMeasure
      = (s.map fun r => max 1 ‖r‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [mahlerMeasure_one]
  | cons r s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, mahlerMeasure_mul,
        mahlerMeasure_X_sub_C, ih]

/-- A monic complex polynomial is the product of `X - C r` over its roots. -/
lemma monic_eq_prod_roots {p : ℂ[X]} (hm : p.Monic) :
    p = (p.roots.map fun r => X - C r).prod :=
  (IsAlgClosed.splits p).eq_prod_roots_of_monic hm

/-- Mahler measure of a monic polynomial as a product over its roots. -/
lemma mahlerMeasure_eq_prod_roots {p : ℂ[X]} (hm : p.Monic) :
    p.mahlerMeasure = (p.roots.map fun r => max 1 ‖r‖).prod := by
  conv_lhs => rw [monic_eq_prod_roots hm]
  exact mahlerMeasure_multiset_prod_X_sub_C _

/-- The monic quartic with the given (descending) coefficients. -/
def q4 (a b c e : ℂ) : ℂ[X] :=
  X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C c * X + C e

lemma q4_monic (a b c e : ℂ) : (q4 a b c e).Monic := by
  unfold q4; monicity!

lemma q4_natDegree (a b c e : ℂ) : (q4 a b c e).natDegree = 4 := by
  unfold q4; compute_degree!

/-- Composition with `-X` on the explicit quartic flips the odd coefficients. -/
lemma q4_comp_neg (a b c e : ℂ) :
    (q4 a b c e).comp (-X) = q4 (-a) b (-c) e := by
  unfold q4
  simp only [add_comp, mul_comp, pow_comp, X_comp, C_comp, map_neg]
  ring

/-- Composition with `-X` of a product of monic linear factors, sign tracked. -/
lemma prod_X_sub_C_comp_neg (s : Multiset ℂ) :
    ((s.map fun r => X - C r).prod).comp (-X)
      = (-1) ^ (Multiset.card s) * (s.map fun r => X - C (-r)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, mul_comp, sub_comp,
        X_comp, C_comp, ih, Multiset.card_cons, map_neg]
      ring

/-- Negation invariance of the Mahler measure for monic polynomials. -/
lemma mahlerMeasure_comp_neg {p : ℂ[X]} (hm : p.Monic) :
    (p.comp (-X)).mahlerMeasure = p.mahlerMeasure := by
  conv_lhs => rw [monic_eq_prod_roots hm]
  have hmap : (Multiset.map (fun r => X - C (-r)) p.roots)
      = Multiset.map (fun r => X - C r) (p.roots.map fun r => -r) := by
    rw [Multiset.map_map]; rfl
  rw [prod_X_sub_C_comp_neg, mahlerMeasure_mul, hmap,
    mahlerMeasure_multiset_prod_X_sub_C, mahlerMeasure_eq_prod_roots hm]
  have h1 : ((-1 : ℂ[X]) ^ Multiset.card p.roots).mahlerMeasure = 1 := by
    rcases Nat.even_or_odd (Multiset.card p.roots) with h | h
    · rw [h.neg_one_pow, mahlerMeasure_one]
    · rw [h.neg_one_pow, show ((-1 : ℂ[X])) = C (-1) by simp,
        mahlerMeasure_const]
      simp
  rw [h1, one_mul, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl ?_
  intro r _
  simp

/-! ## Phase B: the Graeffe transform at degree 4 and M(G p) = M(p)² -/

/-- Composition with `X²` is injective over ℂ (every complex number is a square). -/
lemma comp_X_sq_injective {f g : ℂ[X]} (h : f.comp (X ^ 2) = g.comp (X ^ 2)) :
    f = g := by
  apply Polynomial.funext
  intro y
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y zero_lt_two
  have h2 := congrArg (eval x) h
  simpa [eval_comp, hx] using h2

/-- The Graeffe ring identity at degree 4, coefficient-explicit:
`q(x)·q(−x) = (Graeffe q)(x²)`. -/
lemma gr4_ring (a b c e : ℂ) :
    q4 a b c e * q4 (-a) b (-c) e
      = (q4 (2*b - a^2) (b^2 - 2*a*c + 2*e) (2*b*e - c^2) (e^2)).comp (X ^ 2) := by
  unfold q4
  simp only [add_comp, mul_comp, pow_comp, X_comp, C_comp]
  simp only [map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]
  ring

/-- `∏(X² − r²) = ∏(X − r) · ∏(X + r)`. -/
lemma prod_X_sq_sub_sq (s : Multiset ℂ) :
    (s.map fun r => X ^ 2 - C (r ^ 2)).prod
      = (s.map fun r => X - C r).prod * (s.map fun r => X + C r).prod := by
  rw [← Multiset.prod_map_mul]
  refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
  intro r _
  simp only [map_pow]
  ring

lemma q4_roots_card (a b c e : ℂ) :
    Multiset.card (q4 a b c e).roots = 4 := by
  have h := (IsAlgClosed.splits (k := ℂ) (q4 a b c e)).natDegree_eq_card_roots
  rw [q4_natDegree] at h
  omega

/-- `∏(X + C r)` over the roots of a monic quartic is the sign-flipped quartic. -/
lemma prod_X_add_C_roots (a b c e : ℂ) :
    (((q4 a b c e).roots).map fun r => X + C r).prod = q4 (-a) b (-c) e := by
  have h := prod_X_sub_C_comp_neg (q4 a b c e).roots
  rw [← monic_eq_prod_roots (q4_monic a b c e), q4_comp_neg, q4_roots_card,
    Even.neg_one_pow (by decide : Even 4), one_mul] at h
  rw [h]
  refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
  intro r _
  rw [map_neg, sub_neg_eq_add]

lemma max_one_norm_sq (r : ℂ) : max 1 ‖r ^ 2‖ = max 1 ‖r‖ * max 1 ‖r‖ := by
  rw [norm_pow]
  rcases le_total ‖r‖ 1 with h | h
  · rw [max_eq_left (pow_le_one₀ (norm_nonneg r) h), max_eq_left h, one_mul]
  · rw [max_eq_right (one_le_pow₀ h), max_eq_right h, pow_two]

/-- The Graeffe measure identity at degree 4: the transformed quartic has
Mahler measure the square of the original. The heart of every certificate. -/
lemma mahlerMeasure_gr4 (a b c e : ℂ) :
    (q4 (2*b - a^2) (b^2 - 2*a*c + 2*e) (2*b*e - c^2) (e^2)).mahlerMeasure
      = (q4 a b c e).mahlerMeasure ^ 2 := by
  have key : q4 (2*b - a^2) (b^2 - 2*a*c + 2*e) (2*b*e - c^2) (e^2)
      = (((q4 a b c e).roots.map fun r => r ^ 2).map fun r => X - C r).prod := by
    apply comp_X_sq_injective
    rw [multiset_prod_comp, Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def, sub_comp, X_comp, C_comp]
    rw [prod_X_sq_sub_sq, prod_X_add_C_roots,
      ← monic_eq_prod_roots (q4_monic a b c e), gr4_ring]
  rw [key, mahlerMeasure_multiset_prod_X_sub_C, Multiset.map_map,
    mahlerMeasure_eq_prod_roots (q4_monic a b c e), pow_two,
    ← Multiset.prod_map_mul]
  refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
  intro r _
  exact max_one_norm_sq r

end

/-! ## Phase C: the integer certificate layer -/

/-- Integer coefficient tuples `(a, b, c, e)` for monic quartics
`x⁴ + a x³ + b x² + c x + e`. -/
abbrev Z4 := ℤ × ℤ × ℤ × ℤ

/-- The Graeffe step on integer coefficient tuples (degree 4). -/
def gr4Z : Z4 → Z4
  | (a, b, c, e) => (2*b - a^2, b^2 - 2*a*c + 2*e, 2*b*e - c^2, e^2)

/-- Coefficient selector: `tupCoeff t k` is the `x^k` coefficient of the
monic quartic with tuple `t`. -/
def tupCoeff : Z4 → ℕ → ℤ
  | (_, _, _, e), 0 => e
  | (_, _, c, _), 1 => c
  | (_, b, _, _), 2 => b
  | (a, _, _, _), 3 => a
  | _, 4 => 1
  | _, _ => 0

/-- ℓ¹ size of the monic quartic with tuple `t` (leading 1 included). -/
def tupL1 : Z4 → ℤ
  | (a, b, c, e) => 1 + |a| + |b| + |c| + |e|

noncomputable section

/-- The integer monic quartic with tuple `t`. -/
def zq4 (t : Z4) : ℤ[X] :=
  X ^ 4 + C t.1 * X ^ 3 + C t.2.1 * X ^ 2 + C t.2.2.1 * X + C t.2.2.2

/-- Casting the integer quartic to ℂ gives `q4` of the cast coefficients. -/
lemma map_zq4 (t : Z4) :
    (zq4 t).map (Int.castRingHom ℂ)
      = q4 (t.1 : ℂ) (t.2.1 : ℂ) (t.2.2.1 : ℂ) (t.2.2.2 : ℂ) := by
  unfold zq4 q4
  simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_C]

lemma natDegree_map_zq4 (t : Z4) :
    ((zq4 t).map (Int.castRingHom ℂ)).natDegree = 4 := by
  rw [map_zq4]; exact q4_natDegree _ _ _ _

/-- One Graeffe step at the tuple level squares the Mahler measure. -/
lemma mahlerMeasure_map_gr4Z (t : Z4) :
    ((zq4 (gr4Z t)).map (Int.castRingHom ℂ)).mahlerMeasure
      = ((zq4 t).map (Int.castRingHom ℂ)).mahlerMeasure ^ 2 := by
  obtain ⟨a, b, c, e⟩ := t
  rw [map_zq4, map_zq4]
  have harg : q4 ((gr4Z (a, b, c, e)).1 : ℂ) ((gr4Z (a, b, c, e)).2.1 : ℂ)
        ((gr4Z (a, b, c, e)).2.2.1 : ℂ) ((gr4Z (a, b, c, e)).2.2.2 : ℂ)
      = q4 (2*(b:ℂ) - (a:ℂ)^2) ((b:ℂ)^2 - 2*(a:ℂ)*(c:ℂ) + 2*(e:ℂ))
          (2*(b:ℂ)*(e:ℂ) - (c:ℂ)^2) ((e:ℂ)^2) := by
    show q4 ((2*b - a^2 : ℤ) : ℂ) ((b^2 - 2*a*c + 2*e : ℤ) : ℂ)
        ((2*b*e - c^2 : ℤ) : ℂ) ((e^2 : ℤ) : ℂ) = _
    congr 1 <;> push_cast <;> ring
  rw [harg, mahlerMeasure_gr4]

/-- `K` Graeffe steps raise the Mahler measure to the `2^K`-th power. -/
lemma mahlerMeasure_map_gr4Z_iterate (K : ℕ) (t : Z4) :
    ((zq4 (gr4Z^[K] t)).map (Int.castRingHom ℂ)).mahlerMeasure
      = ((zq4 t).map (Int.castRingHom ℂ)).mahlerMeasure ^ (2 ^ K) := by
  induction K generalizing t with
  | zero => simp
  | succ K ih =>
      rw [Function.iterate_succ_apply, ih (gr4Z t), mahlerMeasure_map_gr4Z,
        ← pow_mul]
      congr 1
      ring

lemma coeff_int_cast_CX (n : ℤ) (k : ℕ) :
    ((n : ℂ[X])).coeff k = if k = 0 then (n : ℂ) else 0 := by
  rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C]

/-- The `x^k` coefficient of the cast quartic is the cast tuple entry. -/
lemma coeff_map_zq4 (t : Z4) (k : ℕ) (hk : k ≤ 4) :
    ((zq4 t).map (Int.castRingHom ℂ)).coeff k = (tupCoeff t k : ℂ) := by
  obtain ⟨a, b, c, e⟩ := t
  rw [map_zq4]
  interval_cases k <;> simp [q4, tupCoeff, coeff_int_cast_CX]

/-- Soundness of the LOWER Graeffe certificate: an integer coefficient
inequality on the `K`-th Graeffe iterate forces `M > P/Q`. -/
lemma lower_cert_sound {t : Z4} {P Q : ℕ} (hQ : 0 < Q) {K k : ℕ} (hk : k ≤ 4)
    (h : (Nat.choose 4 k : ℤ) * (P : ℤ) ^ (2 ^ K)
        < |tupCoeff (gr4Z^[K] t) k| * (Q : ℤ) ^ (2 ^ K)) :
    (P : ℝ) / Q < ((zq4 t).map (Int.castRingHom ℂ)).mahlerMeasure := by
  set M : ℝ := ((zq4 t).map (Int.castRingHom ℂ)).mahlerMeasure with hM
  have hM0 : 0 ≤ M := mahlerMeasure_nonneg _
  have hchoose : (0 : ℝ) < (Nat.choose 4 k : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos hk)
  have hQ0 : (0 : ℝ) < (Q : ℝ) ^ (2 ^ K) := by positivity
  -- the Mathlib coefficient bound at the K-th iterate
  have hbound := norm_coeff_le_choose_mul_mahlerMeasure k
      ((zq4 (gr4Z^[K] t)).map (Int.castRingHom ℂ))
  rw [natDegree_map_zq4, mahlerMeasure_map_gr4Z_iterate,
    coeff_map_zq4 _ _ hk] at hbound
  simp only [Complex.norm_intCast] at hbound
  rw [← hM] at hbound
  -- cast the integer hypothesis to ℝ
  have hR : (Nat.choose 4 k : ℝ) * (P : ℝ) ^ (2 ^ K)
      < |((tupCoeff (gr4Z^[K] t) k : ℤ) : ℝ)| * (Q : ℝ) ^ (2 ^ K) := by
    exact_mod_cast h
  -- assemble: (P/Q)^(2^K) < M^(2^K)
  have step1 : (Nat.choose 4 k : ℝ) * (P : ℝ) ^ (2 ^ K)
      < (Nat.choose 4 k : ℝ) * (M ^ (2 ^ K) * (Q : ℝ) ^ (2 ^ K)) :=
    calc (Nat.choose 4 k : ℝ) * (P : ℝ) ^ (2 ^ K)
        < |((tupCoeff (gr4Z^[K] t) k : ℤ) : ℝ)| * (Q : ℝ) ^ (2 ^ K) := hR
      _ ≤ (Nat.choose 4 k : ℝ) * M ^ (2 ^ K) * (Q : ℝ) ^ (2 ^ K) :=
          mul_le_mul_of_nonneg_right hbound (le_of_lt hQ0)
      _ = (Nat.choose 4 k : ℝ) * (M ^ (2 ^ K) * (Q : ℝ) ^ (2 ^ K)) := by ring
  have hpow : ((P : ℝ) / Q) ^ (2 ^ K) < M ^ (2 ^ K) := by
    rw [div_pow, div_lt_iff₀ hQ0]
    exact lt_of_mul_lt_mul_left step1 (le_of_lt hchoose)
  exact lt_of_pow_lt_pow_left₀ _ hM0 hpow

/-- The ℓ¹ bound: the Mahler measure of the cast quartic is at most the
ℓ¹ size of the tuple (Mathlib's `mahlerMeasure_le_sum_norm_coeff`). -/
lemma mahlerMeasure_map_zq4_le_l1 (s : Z4) :
    ((zq4 s).map (Int.castRingHom ℂ)).mahlerMeasure ≤ (tupL1 s : ℝ) := by
  refine (mahlerMeasure_le_sum_norm_coeff _).trans ?_
  rw [Polynomial.sum_def]
  have hsupp : ((zq4 s).map (Int.castRingHom ℂ)).support ⊆ Finset.range 5 := by
    intro n hn
    rw [Finset.mem_range]
    have h1 := Polynomial.le_natDegree_of_mem_supp n hn
    rw [natDegree_map_zq4] at h1
    omega
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsupp
    (fun i _ _ => norm_nonneg _)).trans ?_
  rw [show (5 : ℕ) = 4 + 1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  rw [coeff_map_zq4 _ 0 (by norm_num), coeff_map_zq4 _ 1 (by norm_num),
    coeff_map_zq4 _ 2 (by norm_num), coeff_map_zq4 _ 3 (by norm_num),
    coeff_map_zq4 _ 4 (by norm_num)]
  obtain ⟨a, b, c, e⟩ := s
  simp only [tupCoeff, tupL1, Complex.norm_intCast]
  push_cast
  rw [abs_one]
  linarith [abs_nonneg (a : ℝ), abs_nonneg (b : ℝ), abs_nonneg (c : ℝ),
    abs_nonneg (e : ℝ)]

/-- Soundness of the UPPER ℓ¹ certificate: an integer ℓ¹ inequality on the
`K`-th Graeffe iterate forces `M ≤ P/Q`. -/
lemma upper_cert_sound {t : Z4} {P Q : ℕ} (hQ : 0 < Q) {K : ℕ}
    (h : tupL1 (gr4Z^[K] t) * (Q : ℤ) ^ (2 ^ K) ≤ (P : ℤ) ^ (2 ^ K)) :
    ((zq4 t).map (Int.castRingHom ℂ)).mahlerMeasure ≤ (P : ℝ) / Q := by
  set M : ℝ := ((zq4 t).map (Int.castRingHom ℂ)).mahlerMeasure with hM
  have hQ0 : (0 : ℝ) < (Q : ℝ) ^ (2 ^ K) := by positivity
  have hl1 := mahlerMeasure_map_zq4_le_l1 (gr4Z^[K] t)
  rw [mahlerMeasure_map_gr4Z_iterate, ← hM] at hl1
  have hR : (tupL1 (gr4Z^[K] t) : ℝ) * (Q : ℝ) ^ (2 ^ K)
      ≤ (P : ℝ) ^ (2 ^ K) := by exact_mod_cast h
  have hpow : M ^ (2 ^ K) ≤ ((P : ℝ) / Q) ^ (2 ^ K) := by
    rw [div_pow, le_div_iff₀ hQ0]
    exact (mul_le_mul_of_nonneg_right hl1 (le_of_lt hQ0)).trans hR
  exact le_of_pow_le_pow_left₀ (by positivity) (by positivity) hpow

/-! ## Root inversion: the reversal ties -/

lemma q4_roots_ne_zero {a b c e : ℂ} (he : e ≠ 0) {r : ℂ}
    (hr : r ∈ (q4 a b c e).roots) : r ≠ 0 := by
  rintro rfl
  have h0 : (q4 a b c e).IsRoot 0 := isRoot_of_mem_roots hr
  simp [q4, IsRoot] at h0
  exact he h0

/-- Pulling a negation out of a multiset product. -/
lemma prod_map_neg' (s : Multiset ℂ) (f : ℂ → ℂ) :
    (s.map fun r => -(f r)).prod
      = (-1) ^ (Multiset.card s) * (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih => simp only [Multiset.map_cons, Multiset.prod_cons, ih,
      Multiset.card_cons]; ring

/-- The product of the roots of a monic quartic is its constant term. -/
lemma q4_prod_roots (a b c e : ℂ) : (q4 a b c e).roots.prod = e := by
  have h := congrArg (eval 0) (monic_eq_prod_roots (q4_monic a b c e))
  rw [eval_multiset_prod, Multiset.map_map] at h
  have h2 : eval 0 (q4 a b c e) = e := by simp [q4]
  have h3 : ((q4 a b c e).roots.map (eval 0 ∘ fun r => X - C r))
      = (q4 a b c e).roots.map fun r => -(id r) := by
    refine Multiset.map_congr rfl ?_
    intro r _
    simp
  rw [h2, h3, prod_map_neg', q4_roots_card,
    Even.neg_one_pow (by decide : Even 4), one_mul] at h
  simpa using h.symm

lemma norm_prod_multiset (s : Multiset ℂ) :
    ‖s.prod‖ = (s.map fun z => ‖z‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih => simp [norm_mul, ih]

lemma max_one_norm_inv {r : ℂ} (hr : r ≠ 0) :
    max 1 ‖r⁻¹‖ = max 1 ‖r‖ / ‖r‖ := by
  have h0 : (0 : ℝ) < ‖r‖ := norm_pos_iff.mpr hr
  rw [norm_inv]
  rcases le_total ‖r‖ 1 with h | h
  · rw [max_eq_right ((one_le_inv₀ h0).mpr h), max_eq_left h, one_div]
  · rw [max_eq_left ((inv_le_one₀ h0).mpr h), max_eq_right h,
      div_self (ne_of_gt h0)]

/-- Root-inversion identity: the monic quartic with inverted roots is the
coefficient-reversed quartic (constant term nonzero). -/
lemma prod_roots_inv (a b c e : ℂ) (he : e ≠ 0) :
    ((q4 a b c e).roots.map fun r => X - C r⁻¹).prod
      = q4 (c/e) (b/e) (a/e) (1/e) := by
  apply Polynomial.funext
  intro y
  rw [eval_multiset_prod, Multiset.map_map]
  have hinv : ((q4 a b c e).roots.map fun r => r⁻¹).prod = e⁻¹ := by
    rw [Multiset.prod_map_inv]
    simp [q4_prod_roots]
  by_cases hy : y = 0
  · subst hy
    have hmap : ((q4 a b c e).roots.map (eval 0 ∘ fun r => X - C r⁻¹))
        = (q4 a b c e).roots.map fun r => -(fun r : ℂ => r⁻¹) r := by
      refine Multiset.map_congr rfl ?_
      intro r _
      simp
    rw [hmap, prod_map_neg' _ (fun r => r⁻¹), q4_roots_card,
      Even.neg_one_pow (by decide : Even 4), one_mul, hinv]
    simp only [q4, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    ring_nf
  · have hstep : ((q4 a b c e).roots.map
          ((fun p => eval y p) ∘ fun r => X - C r⁻¹)).prod
        = ((q4 a b c e).roots.map fun r => r⁻¹ * (r * y - 1)).prod := by
      refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
      intro r hr
      have hr0 := q4_roots_ne_zero he hr
      simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
      field_simp
    have hsplit : ((q4 a b c e).roots.map fun r => r⁻¹ * (r * y - 1)).prod
        = ((q4 a b c e).roots.map fun r => r⁻¹).prod
          * ((q4 a b c e).roots.map fun r => r * y - 1).prod := by
      rw [← Multiset.prod_map_mul]
    have hfactor : ((q4 a b c e).roots.map fun r => r * y - 1)
        = (q4 a b c e).roots.map fun r => y * (r - y⁻¹) := by
      refine Multiset.map_congr rfl ?_
      intro r _
      field_simp
    have hconst : ((q4 a b c e).roots.map fun _ => y).prod = y ^ 4 := by
      rw [Multiset.map_const', Multiset.prod_replicate, q4_roots_card]
    have hshift : ((q4 a b c e).roots.map fun r => r - y⁻¹).prod
        = eval y⁻¹ (q4 a b c e) := by
      conv_rhs => rw [monic_eq_prod_roots (q4_monic a b c e)]
      rw [eval_multiset_prod, Multiset.map_map]
      have : ((q4 a b c e).roots.map
            (eval y⁻¹ ∘ fun r => X - C r))
          = (q4 a b c e).roots.map fun r => -(fun r : ℂ => r - y⁻¹) r := by
        refine Multiset.map_congr rfl ?_
        intro r _
        simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
        ring
      rw [this, prod_map_neg' _ (fun r => r - y⁻¹), q4_roots_card,
        Even.neg_one_pow (by decide : Even 4), one_mul]
    have hG : ((q4 a b c e).roots.map fun r => r * y - 1).prod
        = y ^ 4 * eval y⁻¹ (q4 a b c e) := by
      rw [hfactor]
      have hmul : ((q4 a b c e).roots.map fun r => y * (r - y⁻¹)).prod
          = ((q4 a b c e).roots.map fun _ => y).prod
            * ((q4 a b c e).roots.map fun r => r - y⁻¹).prod := by
        rw [← Multiset.prod_map_mul]
      rw [hmul, hconst, hshift]
    rw [hstep, hsplit, hinv, hG]
    simp only [q4, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    field_simp
    ring

/-- Reversal invariance at unit constant term: the Mahler measure of the
coefficient-reversed quartic equals the original's. -/
lemma mahlerMeasure_q4_inv (a b c e : ℂ) (he : ‖e‖ = 1) :
    (q4 (c/e) (b/e) (a/e) (1/e)).mahlerMeasure = (q4 a b c e).mahlerMeasure := by
  have he0 : e ≠ 0 := by
    intro h
    rw [h] at he
    simp at he
  have hmap : ((q4 a b c e).roots.map fun r => X - C r⁻¹)
      = Multiset.map (fun r => X - C r) ((q4 a b c e).roots.map fun r => r⁻¹) := by
    rw [Multiset.map_map]
    rfl
  rw [← prod_roots_inv a b c e he0, hmap, mahlerMeasure_multiset_prod_X_sub_C,
    Multiset.map_map, mahlerMeasure_eq_prod_roots (q4_monic a b c e)]
  have hpt : ((q4 a b c e).roots.map
        ((fun r => max 1 ‖r‖) ∘ fun r => r⁻¹))
      = (q4 a b c e).roots.map fun r => max 1 ‖r‖ / ‖r‖ := by
    refine Multiset.map_congr rfl ?_
    intro r hr
    exact max_one_norm_inv (q4_roots_ne_zero he0 hr)
  rw [hpt]
  have hdiv : ((q4 a b c e).roots.map fun r => max 1 ‖r‖ / ‖r‖).prod
      = ((q4 a b c e).roots.map fun r => max 1 ‖r‖).prod
        / ((q4 a b c e).roots.map fun r => ‖r‖).prod := by
    rw [← Multiset.prod_map_div]
  have hnorm : ((q4 a b c e).roots.map fun r => ‖r‖).prod = 1 := by
    rw [← norm_prod_multiset, q4_prod_roots, he]
  rw [hdiv, hnorm, div_one]

end

/-! ## Phase D: the boolean certifier and its soundness -/

/-- One LOWER-certificate hit: some coefficient of the current iterate
beats the binomial threshold `C(4,k)·P2` against `|coeff|·Q2`. -/
def lowerHit (P2 Q2 : ℤ) (s : Z4) : Bool :=
  decide (1 * P2 < |tupCoeff s 0| * Q2) ||
  decide (4 * P2 < |tupCoeff s 1| * Q2) ||
  decide (6 * P2 < |tupCoeff s 2| * Q2) ||
  decide (4 * P2 < |tupCoeff s 3| * Q2)

/-- Iterated LOWER certificate with fuel: test, then Graeffe-step with
squared thresholds. -/
def lowerCert : ℕ → ℤ → ℤ → Z4 → Bool
  | 0, _, _, _ => false
  | fuel + 1, P2, Q2, s =>
      lowerHit P2 Q2 s || lowerCert fuel (P2 ^ 2) (Q2 ^ 2) (gr4Z s)

noncomputable section

lemma lowerHit_sound {P Q : ℕ} (hQ : 0 < Q) {K : ℕ} {t : Z4}
    (h : lowerHit ((P : ℤ) ^ 2 ^ K) ((Q : ℤ) ^ 2 ^ K) (gr4Z^[K] t) = true) :
    (P : ℝ) / Q < ((zq4 t).map (Int.castRingHom ℂ)).mahlerMeasure := by
  unfold lowerHit at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ((h | h) | h) | h
  · have hc : ((Nat.choose 4 0 : ℕ) : ℤ) = 1 := by norm_num
    exact lower_cert_sound (K := K) (k := 0) hQ (by norm_num)
      (by rw [hc]; exact h)
  · have hc : ((Nat.choose 4 1 : ℕ) : ℤ) = 4 := by norm_num
    exact lower_cert_sound (K := K) (k := 1) hQ (by norm_num)
      (by rw [hc]; exact h)
  · have hc : ((Nat.choose 4 2 : ℕ) : ℤ) = 6 := by norm_num [Nat.choose]
    exact lower_cert_sound (K := K) (k := 2) hQ (by norm_num)
      (by rw [hc]; exact h)
  · have hc : ((Nat.choose 4 3 : ℕ) : ℤ) = 4 := by norm_num [Nat.choose]
    exact lower_cert_sound (K := K) (k := 3) hQ (by norm_num)
      (by rw [hc]; exact h)

lemma lowerCert_sound {P Q : ℕ} (hQ : 0 < Q) :
    ∀ (fuel K : ℕ) (t : Z4),
      lowerCert fuel ((P : ℤ) ^ 2 ^ K) ((Q : ℤ) ^ 2 ^ K) (gr4Z^[K] t) = true →
      (P : ℝ) / Q < ((zq4 t).map (Int.castRingHom ℂ)).mahlerMeasure := by
  intro fuel
  induction fuel with
  | zero => intro K t h; simp [lowerCert] at h
  | succ fuel ih =>
      intro K t h
      unfold lowerCert at h
      simp only [Bool.or_eq_true] at h
      rcases h with h1 | h2
      · exact lowerHit_sound hQ h1
      · have e1 : ((P : ℤ) ^ 2 ^ K) ^ 2 = (P : ℤ) ^ 2 ^ (K + 1) := by
          rw [← pow_mul, pow_succ]
        have e2 : ((Q : ℤ) ^ 2 ^ K) ^ 2 = (Q : ℤ) ^ 2 ^ (K + 1) := by
          rw [← pow_mul, pow_succ]
        have e3 : gr4Z (gr4Z^[K] t) = gr4Z^[K + 1] t :=
          (Function.iterate_succ_apply' gr4Z K t).symm
        rw [e1, e2, e3] at h2
        exact ih (K + 1) t h2

/-- Top-level LOWER certificate at θ = 139/100 with fuel 9 (K ≤ 8). -/
lemma lowerCert_139_sound {t : Z4} (h : lowerCert 9 139 100 t = true) :
    (139 : ℝ) / 100 < ((zq4 t).map (Int.castRingHom ℂ)).mahlerMeasure := by
  have hs := lowerCert_sound (P := 139) (Q := 100) (by norm_num) 9 0 t
  simp only [pow_zero, pow_one, Function.iterate_zero_apply] at hs
  have h' : lowerCert 9 ((139 : ℕ) : ℤ) ((100 : ℕ) : ℤ) t = true := by
    exact_mod_cast h
  exact_mod_cast hs h'

end

end Mahler
end PDT
