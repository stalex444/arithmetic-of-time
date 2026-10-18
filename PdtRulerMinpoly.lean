module
public import Mathlib
public import PdtIrreducible
public import PdtSalemFamily

@[expose] public section
/-!
# PdtRulerMinpoly — the minimal polynomial of the ruler product `ρQ`

Let `ρ` be the real root of the cubic `x³ = x + 1`, `Q` the real root of the
PDT quartic `x⁴ = x + 1`, and `t = ρ·Q` the ruler product.  This module proves,
in the kernel, that the explicit degree-12 monic

  `rulerPoly = X¹² − 3X⁹ − 2X⁸ + 2X⁶ − X⁵ − 3X⁴ − X³ + X − 1`

(the resultant eliminating `y` from `y³ − y − 1` and `x⁴ − x·y³ − y⁴`) IS the
minimal polynomial of `ρQ` over `ℚ`, and draws the consequences this entry needs.

## Main results

* `ruler_root` — `rulerPoly` vanishes at `r·q` for ANY `r, q` in ANY commutative
  ring with `r³ = r + 1` and `q⁴ = q + 1`.  The proof is an ideal membership in
  `ℤ[r, q]`, so the statement applies verbatim to every pair of embeddings of the
  two generators — over `ℂ` in particular.
* `ruler_generates` — the reverse elimination: `53·r` is an explicit
  `ℤ`-polynomial in `r·q`, again over any commutative ring.  Hence `ρ`, and then
  `Q = (ρQ)/ρ`, lie in `ℚ(ρQ)`.
* `ruler_minpoly` — `minpoly ℚ (ρ·Q) = rulerPoly`.  The proof is a degree
  argument, not a factorization search: `minpoly ∣ rulerPoly` gives `deg ≤ 12`,
  while `ℚ(ρ) ≤ ℚ(ρQ)` and `ℚ(Q) ≤ ℚ(ρQ)` give `3 ∣ deg` and `4 ∣ deg`, so
  `12 ∣ deg ≤ 12`.
* `rulerPoly_irreducible` — hence `rulerPoly` is irreducible over `ℚ`.
* `ruler_adjoin_eq`, `ruler_finrank` — `ℚ(ρQ) = ℚ(ρ, Q)`, of degree 12 over `ℚ`:
  the ruler product GENERATES the degree-12 compositum.
* `embedding_product_is_conjugate` — for every root `w` of the cubic and every
  root `z` of the quartic in `ℂ`, the product `w·z` is a root of
  `minpoly ℚ (ρQ)`, i.e. IS a conjugate of `ρQ`.
* `ruler_factorization`, `root_is_embedding_product`,
  `conjugates_eq_embedding_products` — the converse, and hence the full
  identification: a complex number is a root of `minpoly ℚ (ρQ)` IF AND ONLY IF
  it is a product `w·z` with `w³ = w + 1` and `z⁴ = z + 1`.  The conjugates of
  `ρQ` are EXACTLY the products of embeddings.
* `ruler_conjugates_card`, `mem_ruler_rootSet` — and there are exactly TWELVE of
  them: the root set of `minpoly ℚ (ρQ)` in `ℂ` has `Fintype.card = 12`, and
  membership in it is exactly "is a product of embeddings".
* `ruler_two_conjugates_outside` — `ρQ > 1`, `ρQ` is a root of its own minimal
  polynomial, and there is a SECOND root of that same minimal polynomial with
  modulus `> 1`.  A Pisot number has every other conjugate of modulus `< 1` and
  a Salem number every other of modulus `≤ 1`, so `ρQ` is neither.
* `ruler_unit` — `ρQ` times an explicit degree-11 integer cofactor equals `1`,
  over any commutative ring: the ruler product is an algebraic unit.
* `rulerPoly_nonreciprocal` — the coefficient list of `rulerPoly` is neither its
  own reversal nor the negation of its reversal.
* `ruler_degree_multiplicative` — `deg minpoly(ρQ) = deg minpoly(ρ) ·
  deg minpoly(Q)`, i.e. `12 = 3 · 4`.
* `ruler_compositum_sup`, `ruler_compositum_finrank`, `ruler_linearDisjoint` —
  `ℚ(ρ) ⊔ ℚ(Q) = ℚ(ρQ)` of degree 12, and the two simple extensions are
  linearly disjoint (near-automatic from their coprime degrees — disclosed).

Everything here is elementary algebra of the two defining equations together with
standard field theory.  No physical claim appears in any statement.
-/

namespace PDT
namespace RulerMinpoly

open Polynomial IntermediateField

/-- The explicit degree-12 monic candidate for the minimal polynomial of the
ruler product `ρQ`, over `ℚ`. -/
noncomputable def rulerPoly : ℚ[X] :=
  X ^ 12 - 3 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 6 - X ^ 5 - 3 * X ^ 4 - X ^ 3 + X - 1

lemma rulerPoly_monic : rulerPoly.Monic := by
  unfold rulerPoly
  monicity!

lemma rulerPoly_natDegree : rulerPoly.natDegree = 12 := by
  unfold rulerPoly
  compute_degree!

lemma rulerPoly_ne_zero : rulerPoly ≠ 0 := rulerPoly_monic.ne_zero

/-! ### The ruler product is a root -/

/-- **The ruler product is a root of `rulerPoly`.**  The identity is an ideal
membership in `ℤ[r, q]`: the degree-12 expression in `r·q` is an explicit
combination of `r³ − r − 1` and `q⁴ − q − 1`, so it holds over EVERY commutative
ring — hence for every pair of embeddings of the two generators. -/
theorem ruler_root {R : Type*} [CommRing R] (r q : R)
    (hr : r ^ 3 = r + 1) (hq : q ^ 4 = q + 1) :
    (r * q) ^ 12 - 3 * (r * q) ^ 9 - 2 * (r * q) ^ 8 + 2 * (r * q) ^ 6 - (r * q) ^ 5
      - 3 * (r * q) ^ 4 - (r * q) ^ 3 + (r * q) - 1 = 0 := by
  linear_combination
    (r ^ 9 * q ^ 12 + r ^ 7 * q ^ 12 + r ^ 6 * q ^ 12 - 3 * r ^ 6 * q ^ 9 + r ^ 5 * q ^ 12
      - 2 * r ^ 5 * q ^ 8 + 2 * r ^ 4 * q ^ 12 - 3 * r ^ 4 * q ^ 9 + 2 * r ^ 3 * q ^ 12
      - 3 * r ^ 3 * q ^ 9 - 2 * r ^ 3 * q ^ 8 + 2 * r ^ 3 * q ^ 6 + 3 * r ^ 2 * q ^ 12
      - 3 * r ^ 2 * q ^ 9 - 2 * r ^ 2 * q ^ 8 - r ^ 2 * q ^ 5 + 4 * r * q ^ 12
      - 6 * r * q ^ 9 - 2 * r * q ^ 8 + 2 * r * q ^ 6 - 3 * r * q ^ 4 + 5 * q ^ 12
      - 6 * q ^ 9 - 4 * q ^ 8 + 2 * q ^ 6 - q ^ 5 - q ^ 3) * hr
    + (7 * r ^ 2 * q ^ 8 - 2 * r ^ 2 * q ^ 5 + 3 * r ^ 2 * q ^ 4 + 9 * r * q ^ 8
      - 3 * r * q ^ 5 + 3 * r * q ^ 4 + r * q ^ 2 - r * q + 5 * q ^ 8 - q ^ 5 + q ^ 4
      + q ^ 2 - q + 1) * hq

/-- `rulerPoly` evaluated at the ruler product is zero, in any `ℚ`-algebra. -/
theorem aeval_rulerPoly {A : Type*} [CommRing A] [Algebra ℚ A] (r q : A)
    (hr : r ^ 3 = r + 1) (hq : q ^ 4 = q + 1) :
    aeval (r * q) rulerPoly = 0 := by
  have h := ruler_root r q hr hq
  simp only [rulerPoly, map_sub, map_add, map_pow, map_mul, map_ofNat, map_one, aeval_X]
  linear_combination h

/-! ### The reverse elimination — the ruler product recovers `ρ` -/

/-- **The ruler product recovers its cubic factor.**  `53·r` is an explicit
integer polynomial in `r·q`: another ideal membership, valid over every
commutative ring.  (`53` is the index-type constant thrown up by the
elimination; `disc(rulerPoly) = −23⁴·53²·283³`.) -/
theorem ruler_generates {R : Type*} [CommRing R] (r q : R)
    (hr : r ^ 3 = r + 1) (hq : q ^ 4 = q + 1) :
    53 * r = -17 - 35 * (r * q) - 26 * (r * q) ^ 2 - 56 * (r * q) ^ 3
      + 24 * (r * q) ^ 4 + 19 * (r * q) ^ 5 - 17 * (r * q) ^ 6 - 105 * (r * q) ^ 7
      - 59 * (r * q) ^ 8 - 7 * (r * q) ^ 9 + 16 * (r * q) ^ 10 + 24 * (r * q) ^ 11 := by
  linear_combination
    (-24 * r ^ 8 * q ^ 11 - 16 * r ^ 7 * q ^ 10 - 24 * r ^ 6 * q ^ 11 + 7 * r ^ 6 * q ^ 9
      - 24 * r ^ 5 * q ^ 11 - 16 * r ^ 5 * q ^ 10 + 59 * r ^ 5 * q ^ 8 - 24 * r ^ 4 * q ^ 11
      - 16 * r ^ 4 * q ^ 10 + 7 * r ^ 4 * q ^ 9 + 105 * r ^ 4 * q ^ 7 - 48 * r ^ 3 * q ^ 11
      - 16 * r ^ 3 * q ^ 10 + 7 * r ^ 3 * q ^ 9 + 59 * r ^ 3 * q ^ 8 + 17 * r ^ 3 * q ^ 6
      - 48 * r ^ 2 * q ^ 11 - 32 * r ^ 2 * q ^ 10 + 7 * r ^ 2 * q ^ 9 + 59 * r ^ 2 * q ^ 8
      + 105 * r ^ 2 * q ^ 7 - 19 * r ^ 2 * q ^ 5 - 72 * r * q ^ 11 - 32 * r * q ^ 10
      + 14 * r * q ^ 9 + 59 * r * q ^ 8 + 105 * r * q ^ 7 + 17 * r * q ^ 6 - 24 * r * q ^ 4
      - 96 * q ^ 11 - 48 * q ^ 10 + 14 * q ^ 9 + 118 * q ^ 8 + 105 * q ^ 7 + 17 * q ^ 6
      - 19 * q ^ 5 + 56 * q ^ 3) * hr
    + (-120 * r ^ 2 * q ^ 7 - 64 * r ^ 2 * q ^ 6 + 21 * r ^ 2 * q ^ 5 - 2 * r ^ 2 * q ^ 4
      + 26 * r ^ 2 * q ^ 3 - 26 * r ^ 2 * q ^ 2 - 168 * r * q ^ 7 - 80 * r * q ^ 6
      + 28 * r * q ^ 5 + 9 * r * q ^ 4 - 38 * r * q ^ 3 - 18 * r * q ^ 2 + 18 * r * q
      - 53 * r - 96 * q ^ 7 - 48 * q ^ 6 + 14 * q ^ 5 + 22 * q ^ 4 - 39 * q ^ 3
      - 17 * q ^ 2 + 17 * q - 17) * hq

/-! ### The minimal polynomial -/

/-- The `ℚ`-polynomial expressing `ρ` as a polynomial in the ruler product. -/
noncomputable def rhoOfRuler : ℚ[X] :=
  C (-17/53) + C (-35/53) * X + C (-26/53) * X ^ 2 + C (-56/53) * X ^ 3
    + C (24/53) * X ^ 4 + C (19/53) * X ^ 5 + C (-17/53) * X ^ 6 + C (-105/53) * X ^ 7
    + C (-59/53) * X ^ 8 + C (-7/53) * X ^ 9 + C (16/53) * X ^ 10 + C (24/53) * X ^ 11

private lemma aeval_mem {S : IntermediateField ℚ ℝ} {t : ℝ} (ht : t ∈ S) (p : ℚ[X]) :
    (aeval t p : ℝ) ∈ S := by
  have h : Algebra.adjoin ℚ ({t} : Set ℝ) ≤ S.toSubalgebra := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact ht
  have hmem : (aeval t p : ℝ) ∈ Algebra.adjoin ℚ ({t} : Set ℝ) := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨p, rfl⟩
  exact h hmem

/-- `ρ` lies in `ℚ(ρQ)`. -/
theorem rho_mem_adjoin {rho QQ : ℝ} (hr : rho ^ 3 = rho + 1) (hq : QQ ^ 4 = QQ + 1) :
    rho ∈ ℚ⟮rho * QQ⟯ := by
  have h := aeval_mem (IntermediateField.mem_adjoin_simple_self ℚ (rho * QQ)) rhoOfRuler
  have he : (aeval (rho * QQ) rhoOfRuler : ℝ) = rho := by
    simp only [rhoOfRuler, map_add, map_mul, map_pow, aeval_C, aeval_X, eq_ratCast]
    push_cast
    linear_combination (-1/53 : ℝ) * ruler_generates rho QQ hr hq
  rwa [he] at h

/-- `Q` lies in `ℚ(ρQ)`. -/
theorem Q_mem_adjoin {rho QQ : ℝ} (hr : rho ^ 3 = rho + 1) (hq : QQ ^ 4 = QQ + 1) :
    QQ ∈ ℚ⟮rho * QQ⟯ := by
  have hrho0 : rho ≠ 0 := by
    intro h
    rw [h] at hr
    norm_num at hr
  have h : rho * QQ / rho ∈ ℚ⟮rho * QQ⟯ :=
    div_mem (IntermediateField.mem_adjoin_simple_self ℚ (rho * QQ)) (rho_mem_adjoin hr hq)
  have he : rho * QQ / rho = QQ := by field_simp
  rwa [he] at h

/-- **The minimal polynomial of the ruler product is `rulerPoly`.**  Degree
argument: `minpoly ∣ rulerPoly` bounds the degree by 12, and `ℚ(ρ) ≤ ℚ(ρQ)`,
`ℚ(Q) ≤ ℚ(ρQ)` force `3 ∣ deg` and `4 ∣ deg`, hence `12 ∣ deg`. -/
theorem ruler_minpoly {rho QQ : ℝ} (hr : rho ^ 3 = rho + 1) (hq : QQ ^ 4 = QQ + 1) :
    minpoly ℚ (rho * QQ) = rulerPoly := by
  have hP : (aeval (rho * QQ) rulerPoly : ℝ) = 0 := aeval_rulerPoly rho QQ hr hq
  have hInt : IsIntegral ℚ (rho * QQ) := ⟨rulerPoly, rulerPoly_monic, by rwa [← aeval_def]⟩
  have hIntr : IsIntegral ℚ rho := by
    refine ⟨X ^ 3 - X - 1, by monicity!, ?_⟩
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]
    linear_combination hr
  have hIntq : IsIntegral ℚ QQ := by
    refine ⟨X ^ 4 - X - 1, by monicity!, ?_⟩
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]
    linear_combination hq
  have hmr : minpoly ℚ rho = X ^ 3 - X - 1 := by
    refine (minpoly.eq_of_irreducible_of_monic PDT.cubicQ_irreducible ?_ (by monicity!)).symm
    simp only [map_sub, map_pow, aeval_X, map_one]
    linear_combination hr
  have hmq : minpoly ℚ QQ = X ^ 4 - X - 1 := by
    refine (minpoly.eq_of_irreducible_of_monic PDT.quarticQ_irreducible ?_ (by monicity!)).symm
    simp only [map_sub, map_pow, aeval_X, map_one]
    linear_combination hq
  have hfr3 : Module.finrank ℚ ℚ⟮rho⟯ = 3 := by
    rw [IntermediateField.adjoin.finrank hIntr, hmr]
    compute_degree!
  have hfr4 : Module.finrank ℚ ℚ⟮QQ⟯ = 4 := by
    rw [IntermediateField.adjoin.finrank hIntq, hmq]
    compute_degree!
  have hd3 : 3 ∣ Module.finrank ℚ ℚ⟮rho * QQ⟯ := by
    have h := IntermediateField.finrank_dvd_of_le_right
      (IntermediateField.adjoin_simple_le_iff.mpr (rho_mem_adjoin hr hq))
    rwa [hfr3] at h
  have hd4 : 4 ∣ Module.finrank ℚ ℚ⟮rho * QQ⟯ := by
    have h := IntermediateField.finrank_dvd_of_le_right
      (IntermediateField.adjoin_simple_le_iff.mpr (Q_mem_adjoin hr hq))
    rwa [hfr4] at h
  have hd12 : 12 ∣ Module.finrank ℚ ℚ⟮rho * QQ⟯ := by
    have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 3 4) hd3 hd4
    simpa using h
  have hfrt : Module.finrank ℚ ℚ⟮rho * QQ⟯ = (minpoly ℚ (rho * QQ)).natDegree :=
    IntermediateField.adjoin.finrank hInt
  have hdvd : minpoly ℚ (rho * QQ) ∣ rulerPoly := minpoly.dvd ℚ (rho * QQ) hP
  have hle : (minpoly ℚ (rho * QQ)).natDegree ≤ 12 := by
    have h := Polynomial.natDegree_le_of_dvd hdvd rulerPoly_ne_zero
    rwa [rulerPoly_natDegree] at h
  have hpos : 0 < (minpoly ℚ (rho * QQ)).natDegree := minpoly.natDegree_pos hInt
  have hge : 12 ≤ (minpoly ℚ (rho * QQ)).natDegree := by
    rw [hfrt] at hd12
    exact Nat.le_of_dvd hpos hd12
  have hdeg : (minpoly ℚ (rho * QQ)).natDegree = 12 := le_antisymm hle hge
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hInt) rulerPoly_monic
    hdvd (by simp [rulerPoly_natDegree, hdeg])).symm

/-! ### Non-vacuity: the two generators exist -/

/-- The PDT cubic has a real root. -/
theorem exists_cubic_root : ∃ x : ℝ, x ^ 3 = x + 1 := by
  have hc : ContinuousOn (fun y : ℝ => y ^ 3 - y - 1) (Set.Icc 1 2) := by fun_prop
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc (by norm_num : (1:ℝ) ≤ 2) hc
    (show (0:ℝ) ∈ Set.Icc ((1:ℝ) ^ 3 - 1 - 1) ((2:ℝ) ^ 3 - 2 - 1) by norm_num)
  exact ⟨x, by simp only at hx; linarith⟩

/-- The PDT quartic has a real root above `1`. -/
theorem exists_quartic_root : ∃ x : ℝ, x ^ 4 = x + 1 ∧ 1 < x := by
  have hc : ContinuousOn (fun y : ℝ => y ^ 4 - y - 1) (Set.Icc (6 / 5) (13 / 10)) := by fun_prop
  obtain ⟨x, hxm, hx⟩ := intermediate_value_Icc (by norm_num : (6 / 5 : ℝ) ≤ 13 / 10) hc
    (show (0:ℝ) ∈ Set.Icc ((6 / 5 : ℝ) ^ 4 - 6 / 5 - 1) ((13 / 10 : ℝ) ^ 4 - 13 / 10 - 1) by
      norm_num)
  refine ⟨x, by simp only at hx; linarith, ?_⟩
  have h1 := hxm.1
  linarith

/-- **`rulerPoly` is irreducible over `ℚ`** — it is a minimal polynomial. -/
theorem rulerPoly_irreducible : Irreducible rulerPoly := by
  obtain ⟨rho, hr⟩ := exists_cubic_root
  obtain ⟨QQ, hq, -⟩ := exists_quartic_root
  have hInt : IsIntegral ℚ (rho * QQ) :=
    ⟨rulerPoly, rulerPoly_monic, by
      rw [← aeval_def]
      exact aeval_rulerPoly rho QQ hr hq⟩
  rw [← ruler_minpoly hr hq]
  exact minpoly.irreducible hInt

/-! ### The ruler product generates the compositum -/

/-- **`ℚ(ρQ) = ℚ(ρ, Q)`** — the ruler product generates the compositum. -/
theorem ruler_adjoin_eq {rho QQ : ℝ} (hr : rho ^ 3 = rho + 1) (hq : QQ ^ 4 = QQ + 1) :
    ℚ⟮rho * QQ⟯ = ℚ⟮rho, QQ⟯ := by
  apply le_antisymm
  · refine IntermediateField.adjoin_simple_le_iff.mpr ?_
    exact mul_mem (IntermediateField.subset_adjoin ℚ _ (by simp))
      (IntermediateField.subset_adjoin ℚ _ (by simp))
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro x (rfl | rfl)
    · exact rho_mem_adjoin hr hq
    · exact Q_mem_adjoin hr hq

/-- **The compositum has degree 12 over `ℚ`**, with `ρQ` as a primitive element. -/
theorem ruler_finrank {rho QQ : ℝ} (hr : rho ^ 3 = rho + 1) (hq : QQ ^ 4 = QQ + 1) :
    Module.finrank ℚ ℚ⟮rho, QQ⟯ = 12 := by
  have hInt : IsIntegral ℚ (rho * QQ) :=
    ⟨rulerPoly, rulerPoly_monic, by
      rw [← aeval_def]
      exact aeval_rulerPoly rho QQ hr hq⟩
  rw [← ruler_adjoin_eq hr hq, IntermediateField.adjoin.finrank hInt, ruler_minpoly hr hq,
    rulerPoly_natDegree]

/-! ### The conjugates -/

/-- **Every product of embeddings is a conjugate of `ρQ`.**  For every root `w`
of the cubic and every root `z` of the quartic in `ℂ`, the product `w·z`
is a root of the minimal polynomial of `ρQ` over `ℚ`.  This is the step the
entry cites; it is now kernel-held. -/
theorem embedding_product_is_conjugate {rho QQ : ℝ} (hr : rho ^ 3 = rho + 1)
    (hq : QQ ^ 4 = QQ + 1) (w z : ℂ) (hw : w ^ 3 = w + 1) (hz : z ^ 4 = z + 1) :
    aeval (w * z) (minpoly ℚ (rho * QQ)) = 0 := by
  rw [ruler_minpoly hr hq]
  exact aeval_rulerPoly w z hw hz

/-- **`ρQ` is neither a Pisot nor a Salem number.**  `ρQ > 1`, it is a root of
its own minimal polynomial over `ℚ`, and that minimal polynomial has a SECOND
root of modulus `> 1`.  A Pisot number has every other conjugate of modulus
`< 1`, a Salem number every other of modulus `≤ 1`; `ρQ` has a second conjugate
strictly outside the unit circle, so it is neither. -/
theorem ruler_two_conjugates_outside {rho QQ : ℝ} (hr : rho ^ 3 = rho + 1)
    (hq : QQ ^ 4 = QQ + 1) (hq1 : 1 < QQ) :
    1 < rho * QQ ∧ aeval ((rho * QQ : ℝ) : ℂ) (minpoly ℚ (rho * QQ)) = 0 ∧
      ∃ z : ℂ, aeval z (minpoly ℚ (rho * QQ)) = 0 ∧ z ≠ ((rho * QQ : ℝ) : ℂ) ∧ 1 < ‖z‖ := by
  obtain ⟨z, hz4, -, hz1, hz2⟩ := PDT.SalemFamily.ruler_second_conjugate hq hq1 hr
  have hrC : ((rho : ℂ)) ^ 3 = (rho : ℂ) + 1 := by exact_mod_cast hr
  have hqC : ((QQ : ℂ)) ^ 4 = (QQ : ℂ) + 1 := by exact_mod_cast hq
  have hgt : 1 < rho * QQ := lt_trans hz1 hz2
  refine ⟨hgt, ?_, ⟨(rho : ℂ) * z, embedding_product_is_conjugate hr hq _ _ hrC hz4, ?_, hz1⟩⟩
  · have h := embedding_product_is_conjugate hr hq (rho : ℂ) (QQ : ℂ) hrC hqC
    push_cast
    exact h
  · intro hEq
    rw [hEq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0:ℝ) < rho * QQ)] at hz2
    exact lt_irrefl _ hz2

/-! ### The conjugates are EXACTLY the twelve products -/

/-- If `w1³ = w1 + 1` and `y` is a root of the quadratic cofactor
`y² + w1·y + w1² = 1`, then `y` too is a root of the cubic: indeed
`y³ − y − 1 = (y − w1)(y² + w1·y + w1² − 1) + (w1³ − w1 − 1)`. -/
theorem cubic_of_quadratic {R : Type*} [CommRing R] (w1 y : R) (h1 : w1 ^ 3 = w1 + 1)
    (h2 : y ^ 2 + w1 * y + w1 ^ 2 = 1) : y ^ 3 = y + 1 := by
  linear_combination (y - w1) * h2 + h1

/-- **`rulerPoly` factors as the resultant product.**  If `w1` is a root of the
PDT cubic and `w2` a root of its quadratic cofactor — so that `w1, w2, −(w1+w2)`
is a complete root system of `x³ − x − 1` — then

  `rulerPoly(x) = ∏ᵢ (x⁴ − x·wᵢ³ − wᵢ⁴)`,

the resultant `Res_y(y³ − y − 1, x⁴ − x·y³ − y⁴)` written out.  Each factor is
`wᵢ⁴·((x/wᵢ)⁴ − (x/wᵢ) − 1)`, so its roots are exactly the four products
`wᵢ·z` with `z⁴ = z + 1`. -/
theorem ruler_factorization {R : Type*} [CommRing R] (x w1 w2 : R)
    (h1 : w1 ^ 3 = w1 + 1) (h2 : w2 ^ 2 + w1 * w2 + w1 ^ 2 = 1) :
    x ^ 12 - 3 * x ^ 9 - 2 * x ^ 8 + 2 * x ^ 6 - x ^ 5 - 3 * x ^ 4 - x ^ 3 + x - 1
      = (x ^ 4 - x * w1 ^ 3 - w1 ^ 4) * (x ^ 4 - x * w2 ^ 3 - w2 ^ 4)
        * (x ^ 4 - x * (-(w1 + w2)) ^ 3 - (-(w1 + w2)) ^ 4) := by
  linear_combination
    (
      -3 * w1 * x ^ 9 + 2 * w1 ^ 2 * x ^ 8 + 2 * w1 * w2 * x ^ 8 + 2 * w2 ^ 2 * x ^ 8
      + 2 * x ^ 8 + 4 * w1 ^ 4 * x ^ 6 - w1 ^ 3 * w2 * x ^ 6 - 2 * w1 ^ 2 * x ^ 6 + 2
      * w1 * w2 ^ 3 * x ^ 6 + w1 * w2 * x ^ 6 + w2 ^ 4 * x ^ 6 + w2 ^ 2 * x ^ 6 + x ^
      6 - w1 ^ 4 * w2 * x ^ 5 - 2 * w1 ^ 3 * w2 ^ 2 * x ^ 5 - 2 * w1 ^ 2 * w2 ^ 3 * x
      ^ 5 - w1 ^ 2 * w2 * x ^ 5 - w1 * w2 ^ 4 * x ^ 5 - w1 * w2 ^ 2 * x ^ 5 - w1 * x ^
      5 - w1 ^ 6 * x ^ 4 - 3 * w1 ^ 5 * w2 * x ^ 4 - 2 * w1 ^ 4 * w2 ^ 2 * x ^ 4 - 5 *
      w1 ^ 4 * x ^ 4 + w1 ^ 3 * w2 ^ 3 * x ^ 4 + 2 * w1 ^ 3 * w2 * x ^ 4 - 2 * w1 ^ 2
      * w2 ^ 4 * x ^ 4 + w1 ^ 2 * w2 ^ 2 * x ^ 4 + 3 * w1 ^ 2 * x ^ 4 - 3 * w1 * w2 ^
      5 * x ^ 4 - 2 * w1 * w2 ^ 3 * x ^ 4 - w1 * w2 * x ^ 4 - w2 ^ 6 * x ^ 4 - w2 ^ 4
      * x ^ 4 - w2 ^ 2 * x ^ 4 - x ^ 4 - w1 ^ 7 * x ^ 3 + w1 ^ 6 * w2 * x ^ 3 + 2 * w1
      ^ 5 * x ^ 3 - 2 * w1 ^ 4 * w2 ^ 3 * x ^ 3 - w1 ^ 4 * w2 * x ^ 3 - w1 ^ 3 * w2 ^
      4 * x ^ 3 - w1 ^ 3 * w2 ^ 2 * x ^ 3 - w1 ^ 3 * x ^ 3 + w1 ^ 7 * x + w1 ^ 6 * w2
      ^ 3 * x - w1 ^ 6 * w2 * x + 3 * w1 ^ 5 * w2 ^ 4 * x - 2 * w1 ^ 5 * x + 3 * w1 ^
      4 * w2 ^ 5 * x + 2 * w1 ^ 4 * w2 ^ 3 * x + w1 ^ 4 * w2 * x + w1 ^ 3 * w2 ^ 6 * x
      + w1 ^ 3 * w2 ^ 4 * x + w1 ^ 3 * w2 ^ 2 * x + w1 ^ 3 * x - w1 ^ 10 + w1 ^ 9 * w2
      + 3 * w1 ^ 8 - w1 ^ 7 * w2 ^ 3 - 2 * w1 ^ 7 * w2 + 2 * w1 ^ 6 * w2 ^ 4 - w1 ^ 6
      * w2 ^ 2 - 3 * w1 ^ 6 + 3 * w1 ^ 5 * w2 ^ 5 + 2 * w1 ^ 5 * w2 ^ 3 + w1 ^ 5 * w2
      + w1 ^ 4 * w2 ^ 6 + w1 ^ 4 * w2 ^ 4 + w1 ^ 4 * w2 ^ 2 + w1 ^ 4) * h2
    + (
      3 * x ^ 9 - 3 * w1 ^ 3 * x ^ 6 + 3 * w1 * x ^ 6 - 3 * x ^ 6 + x ^ 5 + 4 * w1 ^ 3
      * x ^ 4 - 4 * w1 * x ^ 4 + 4 * x ^ 4 + w1 ^ 6 * x ^ 3 - 2 * w1 ^ 4 * x ^ 3 + w1
      ^ 3 * x ^ 3 + w1 ^ 2 * x ^ 3 - w1 * x ^ 3 + x ^ 3 - w1 ^ 6 * x + 2 * w1 ^ 4 * x
      - w1 ^ 3 * x - w1 ^ 2 * x + w1 * x - x + w1 ^ 9 - 3 * w1 ^ 7 + w1 ^ 6 + 3 * w1 ^
      5 - 2 * w1 ^ 4 + w1 ^ 2 - w1 + 1) * h1

/-- The PDT cubic has a real root in `[5/4, 3/2]`. -/
theorem exists_cubic_root_mem : ∃ x : ℝ, x ^ 3 = x + 1 ∧ 5 / 4 ≤ x ∧ x ≤ 3 / 2 := by
  have hc : ContinuousOn (fun y : ℝ => y ^ 3 - y - 1) (Set.Icc (5 / 4) (3 / 2)) := by fun_prop
  obtain ⟨x, hxm, hx⟩ := intermediate_value_Icc (by norm_num : (5 / 4 : ℝ) ≤ 3 / 2) hc
    (show (0:ℝ) ∈ Set.Icc ((5 / 4 : ℝ) ^ 3 - 5 / 4 - 1) ((3 / 2 : ℝ) ^ 3 - 3 / 2 - 1) by
      norm_num)
  exact ⟨x, by simp only at hx; linarith, hxm.1, hxm.2⟩

/-- A complete root system of the cubic exists over `ℂ`, in the triangular
form `ruler_factorization` needs: the real root together with a root of the
quadratic cofactor. -/
theorem exists_cubic_pair : ∃ w1 w2 : ℂ, w1 ^ 3 = w1 + 1 ∧ w2 ^ 2 + w1 * w2 + w1 ^ 2 = 1 := by
  obtain ⟨r, hr, hr1, hr2⟩ := exists_cubic_root_mem
  have hd : (0:ℝ) ≤ 3 * r ^ 2 - 4 := by nlinarith
  have hd2 : (Real.sqrt (3 * r ^ 2 - 4)) ^ 2 = 3 * r ^ 2 - 4 := Real.sq_sqrt hd
  refine ⟨(r : ℂ), -(r : ℂ) / 2 + ((Real.sqrt (3 * r ^ 2 - 4) : ℝ) : ℂ) / 2 * Complex.I,
    by exact_mod_cast hr, ?_⟩
  have hI : (Complex.I) ^ 2 = -1 := Complex.I_sq
  have hd2C : ((Real.sqrt (3 * r ^ 2 - 4) : ℝ) : ℂ) ^ 2 = 3 * (r : ℂ) ^ 2 - 4 := by
    exact_mod_cast hd2
  linear_combination (((Real.sqrt (3 * r ^ 2 - 4) : ℝ) : ℂ) ^ 2 / 4) * hI - (1 / 4 : ℂ) * hd2C

private lemma factor_to_pair {w zeta : ℂ} (hw : w ^ 3 = w + 1)
    (hf : zeta ^ 4 - zeta * w ^ 3 - w ^ 4 = 0) :
    ∃ a b : ℂ, a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ zeta = a * b := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    norm_num at hw
  have h4 : zeta ^ 4 = zeta * w ^ 3 + w ^ 4 := by linear_combination hf
  refine ⟨w, zeta / w, hw, ?_, by field_simp⟩
  field_simp
  linear_combination h4

/-- **Every root of `rulerPoly` is a product of embeddings.**  The converse of
`ruler_root`: if `ζ` is a complex root of `rulerPoly` then `ζ = w·z` for some
root `w` of the cubic and some root `z` of the quartic. -/
theorem root_is_embedding_product (zeta : ℂ)
    (hz : zeta ^ 12 - 3 * zeta ^ 9 - 2 * zeta ^ 8 + 2 * zeta ^ 6 - zeta ^ 5
      - 3 * zeta ^ 4 - zeta ^ 3 + zeta - 1 = 0) :
    ∃ a b : ℂ, a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ zeta = a * b := by
  obtain ⟨w1, w2, h1, h2⟩ := exists_cubic_pair
  have hfac := ruler_factorization zeta w1 w2 h1 h2
  rw [hz] at hfac
  have h2' : w2 ^ 3 = w2 + 1 := cubic_of_quadratic w1 w2 h1 h2
  have h3q : (-(w1 + w2)) ^ 2 + w1 * (-(w1 + w2)) + w1 ^ 2 = 1 := by linear_combination h2
  have h3' : (-(w1 + w2)) ^ 3 = -(w1 + w2) + 1 := cubic_of_quadratic w1 _ h1 h3q
  rcases mul_eq_zero.mp hfac.symm with hAB | hC
  · rcases mul_eq_zero.mp hAB with hA | hB
    · exact factor_to_pair h1 hA
    · exact factor_to_pair h2' hB
  · exact factor_to_pair h3' hC

/-- `aeval` of `rulerPoly`, written out. -/
theorem aeval_rulerPoly_eq {A : Type*} [CommRing A] [Algebra ℚ A] (a : A) :
    aeval a rulerPoly =
      a ^ 12 - 3 * a ^ 9 - 2 * a ^ 8 + 2 * a ^ 6 - a ^ 5 - 3 * a ^ 4 - a ^ 3 + a - 1 := by
  simp only [rulerPoly, map_sub, map_add, map_pow, map_mul, map_ofNat, map_one, aeval_X]

/-- **The conjugates of `ρQ` are EXACTLY the products of embeddings.**  A complex
number is a root of `minpoly ℚ (ρQ)` if and only if it is a product `w·z` of a
root `w` of the cubic with a root `z` of the quartic.  This is the
identification this entry cited without formalizing, in both
directions. -/
theorem conjugates_eq_embedding_products {rho QQ : ℝ} (hr : rho ^ 3 = rho + 1)
    (hq : QQ ^ 4 = QQ + 1) (zeta : ℂ) :
    aeval zeta (minpoly ℚ (rho * QQ)) = 0 ↔
      ∃ w z : ℂ, w ^ 3 = w + 1 ∧ z ^ 4 = z + 1 ∧ zeta = w * z := by
  rw [ruler_minpoly hr hq, aeval_rulerPoly_eq]
  constructor
  · exact root_is_embedding_product zeta
  · rintro ⟨w, z, hw, hzz, rfl⟩
    have h := aeval_rulerPoly w z hw hzz
    rw [aeval_rulerPoly_eq] at h
    exact h

/-- **There are exactly twelve conjugates.**  `minpoly ℚ (ρQ) = rulerPoly` is
irreducible over a field of characteristic zero, hence separable, and splits over
`ℂ`: its root set has exactly `12` elements. -/
theorem ruler_conjugates_card : Fintype.card (rulerPoly.rootSet ℂ) = 12 := by
  have h := card_rootSet_eq_natDegree (K := ℂ) rulerPoly_irreducible.separable
    (IsAlgClosed.splits _)
  rwa [rulerPoly_natDegree] at h

/-- **The twelve conjugates of `ρQ` ARE the products of embeddings.**  Combined
with `ruler_conjugates_card` this is the full cited identification: the root set
of `minpoly ℚ (ρQ)` in `ℂ` has exactly twelve elements, and a complex number
belongs to it precisely when it is a product `w·z` of a root of the cubic
with a root of the quartic. -/
theorem mem_ruler_rootSet {rho QQ : ℝ} (hr : rho ^ 3 = rho + 1) (hq : QQ ^ 4 = QQ + 1)
    (zeta : ℂ) :
    zeta ∈ rulerPoly.rootSet ℂ ↔ ∃ w z : ℂ, w ^ 3 = w + 1 ∧ z ^ 4 = z + 1 ∧ zeta = w * z := by
  rw [Polynomial.mem_rootSet, ← ruler_minpoly hr hq]
  constructor
  · rintro ⟨-, h⟩
    exact (conjugates_eq_embedding_products hr hq zeta).mp h
  · intro h
    refine ⟨?_, (conjugates_eq_embedding_products hr hq zeta).mpr h⟩
    rw [ruler_minpoly hr hq]
    exact rulerPoly_ne_zero

/-! ### The ruler product is a unit -/

/-- **The ruler product is an algebraic unit.**  Over any commutative ring with
`r³ = r + 1` and `q⁴ = q + 1`, the product `r·q` times an explicit degree-11
integer-coefficient cofactor equals `1`: `rulerPoly` has constant term `−1`, so
`ρQ` is a unit (its norm is `−1`).  In particular `ρ·Q·(ρQ)⁻¹ = 1` realizes the
degree triple `(3, 4, 12)` in the normal form `α·β·γ = 1`. -/
theorem ruler_unit {R : Type*} [CommRing R] (r q : R)
    (hr : r ^ 3 = r + 1) (hq : q ^ 4 = q + 1) :
    (r * q) * ((r * q) ^ 11 - 3 * (r * q) ^ 8 - 2 * (r * q) ^ 7 + 2 * (r * q) ^ 5
      - (r * q) ^ 4 - 3 * (r * q) ^ 3 - (r * q) ^ 2 + 1) = 1 := by
  linear_combination ruler_root r q hr hq

/-! ### `rulerPoly` is not reciprocal -/

/-- The coefficient of `X⁹` in `rulerPoly` is `−3`. -/
lemma rulerPoly_coeff_nine : rulerPoly.coeff 9 = -3 := by
  norm_num [rulerPoly, coeff_X_pow, coeff_X, coeff_one]

/-- The coefficient of `X³` in `rulerPoly` is `−1`. -/
lemma rulerPoly_coeff_three : rulerPoly.coeff 3 = -1 := by
  norm_num [rulerPoly, coeff_X_pow, coeff_X, coeff_one]

/-- **`rulerPoly` is not reciprocal.**  Its coefficient list is neither its own
reversal nor the negation of its reversal: both comparisons already fail at the
coefficient of `X³`, where the reversal carries `−3` against `−1` (resp. `1`).
So the minimal polynomial of `ρQ` lies in the nonreciprocal regime. -/
theorem rulerPoly_nonreciprocal :
    rulerPoly.reverse ≠ rulerPoly ∧ rulerPoly.reverse ≠ -rulerPoly := by
  have hrev : rulerPoly.reverse.coeff 3 = -3 := by
    rw [Polynomial.coeff_reverse, rulerPoly_natDegree,
      Polynomial.revAt_le (by norm_num : (3:ℕ) ≤ 12)]
    simpa using rulerPoly_coeff_nine
  constructor
  · intro h
    rw [h, rulerPoly_coeff_three] at hrev
    norm_num at hrev
  · intro h
    rw [h, Polynomial.coeff_neg, rulerPoly_coeff_three] at hrev
    norm_num at hrev

/-! ### Degree multiplicativity -/

/-- The minimal polynomial of any real root of the cubic is `X³ − X − 1`. -/
theorem cubic_minpoly {rho : ℝ} (hr : rho ^ 3 = rho + 1) :
    minpoly ℚ rho = X ^ 3 - X - 1 := by
  refine (minpoly.eq_of_irreducible_of_monic PDT.cubicQ_irreducible ?_ (by monicity!)).symm
  simp only [map_sub, map_pow, aeval_X, map_one]
  linear_combination hr

/-- The minimal polynomial of any real root of the quartic is `X⁴ − X − 1`. -/
theorem quartic_minpoly {QQ : ℝ} (hq : QQ ^ 4 = QQ + 1) :
    minpoly ℚ QQ = X ^ 4 - X - 1 := by
  refine (minpoly.eq_of_irreducible_of_monic PDT.quarticQ_irreducible ?_ (by monicity!)).symm
  simp only [map_sub, map_pow, aeval_X, map_one]
  linear_combination hq

/-- `ℚ(ρ)` has degree 3 over `ℚ`. -/
theorem cubic_finrank {rho : ℝ} (hr : rho ^ 3 = rho + 1) :
    Module.finrank ℚ ℚ⟮rho⟯ = 3 := by
  have hInt : IsIntegral ℚ rho := by
    refine ⟨X ^ 3 - X - 1, by monicity!, ?_⟩
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]
    linear_combination hr
  rw [IntermediateField.adjoin.finrank hInt, cubic_minpoly hr]
  compute_degree!

/-- `ℚ(Q)` has degree 4 over `ℚ`. -/
theorem quartic_finrank {QQ : ℝ} (hq : QQ ^ 4 = QQ + 1) :
    Module.finrank ℚ ℚ⟮QQ⟯ = 4 := by
  have hInt : IsIntegral ℚ QQ := by
    refine ⟨X ^ 4 - X - 1, by monicity!, ?_⟩
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]
    linear_combination hq
  rw [IntermediateField.adjoin.finrank hInt, quartic_minpoly hq]
  compute_degree!

/-- **Degree multiplicativity at the ruler product.**  The degree of the minimal
polynomial of `ρQ` is the PRODUCT of the degrees of the minimal polynomials of
`ρ` and `Q` — `12 = 3 · 4`.  Unlike the coprime-degree SUM case, no general
theorem forces this for products (`ζ₃·∛2` has degree 3, not 6), so the equality
is content certified here by the elimination, not bookkeeping. -/
theorem ruler_degree_multiplicative {rho QQ : ℝ} (hr : rho ^ 3 = rho + 1)
    (hq : QQ ^ 4 = QQ + 1) :
    (minpoly ℚ (rho * QQ)).natDegree
      = (minpoly ℚ rho).natDegree * (minpoly ℚ QQ).natDegree := by
  have h3 : (X ^ 3 - X - 1 : ℚ[X]).natDegree = 3 := by compute_degree!
  have h4 : (X ^ 4 - X - 1 : ℚ[X]).natDegree = 4 := by compute_degree!
  rw [ruler_minpoly hr hq, rulerPoly_natDegree, cubic_minpoly hr, quartic_minpoly hq, h3, h4]

/-! ### The compositum in sup form, and linear disjointness -/

/-- **The compositum, in sup form.**  `ℚ(ρ) ⊔ ℚ(Q) = ℚ(ρQ)`: the ruler product
is a primitive element of the compositum of the two simple extensions.  This is
`ruler_adjoin_eq` repackaged into the lattice vocabulary. -/
theorem ruler_compositum_sup {rho QQ : ℝ} (hr : rho ^ 3 = rho + 1)
    (hq : QQ ^ 4 = QQ + 1) :
    ℚ⟮rho⟯ ⊔ ℚ⟮QQ⟯ = ℚ⟮rho * QQ⟯ := by
  rw [ruler_adjoin_eq hr hq, ← IntermediateField.adjoin_union, Set.singleton_union]

/-- **The compositum has degree 12 over `ℚ`**, in sup form. -/
theorem ruler_compositum_finrank {rho QQ : ℝ} (hr : rho ^ 3 = rho + 1)
    (hq : QQ ^ 4 = QQ + 1) :
    Module.finrank ℚ ↥(ℚ⟮rho⟯ ⊔ ℚ⟮QQ⟯) = 12 := by
  rw [ruler_compositum_sup hr hq, ruler_adjoin_eq hr hq]
  exact ruler_finrank hr hq

/-- **`ℚ(ρ)` and `ℚ(Q)` are linearly disjoint over `ℚ`.**  DISCLOSURE: given the
kernel-held degrees 3 and 4, this is near-automatic from Mathlib's
`IntermediateField.LinearDisjoint.of_finrank_coprime` — coprime finite degrees
force linear disjointness.  No new general theorem is claimed here; the
substantive content is the sup-equality `ruler_compositum_sup` above. -/
theorem ruler_linearDisjoint {rho QQ : ℝ} (hr : rho ^ 3 = rho + 1)
    (hq : QQ ^ 4 = QQ + 1) :
    ℚ⟮rho⟯.LinearDisjoint ℚ⟮QQ⟯ := by
  apply IntermediateField.LinearDisjoint.of_finrank_coprime
  rw [cubic_finrank hr, quartic_finrank hq]
  decide

end RulerMinpoly
end PDT

/-! ### Axiom audit -/

#print axioms PDT.RulerMinpoly.rulerPoly_monic
#print axioms PDT.RulerMinpoly.rulerPoly_natDegree
#print axioms PDT.RulerMinpoly.rulerPoly_ne_zero
#print axioms PDT.RulerMinpoly.ruler_root
#print axioms PDT.RulerMinpoly.aeval_rulerPoly
#print axioms PDT.RulerMinpoly.ruler_generates
#print axioms PDT.RulerMinpoly.rho_mem_adjoin
#print axioms PDT.RulerMinpoly.Q_mem_adjoin
#print axioms PDT.RulerMinpoly.ruler_minpoly
#print axioms PDT.RulerMinpoly.exists_cubic_root
#print axioms PDT.RulerMinpoly.exists_quartic_root
#print axioms PDT.RulerMinpoly.rulerPoly_irreducible
#print axioms PDT.RulerMinpoly.ruler_adjoin_eq
#print axioms PDT.RulerMinpoly.ruler_finrank
#print axioms PDT.RulerMinpoly.embedding_product_is_conjugate
#print axioms PDT.RulerMinpoly.ruler_two_conjugates_outside
#print axioms PDT.RulerMinpoly.cubic_of_quadratic
#print axioms PDT.RulerMinpoly.ruler_factorization
#print axioms PDT.RulerMinpoly.exists_cubic_root_mem
#print axioms PDT.RulerMinpoly.exists_cubic_pair
#print axioms PDT.RulerMinpoly.root_is_embedding_product
#print axioms PDT.RulerMinpoly.aeval_rulerPoly_eq
#print axioms PDT.RulerMinpoly.conjugates_eq_embedding_products
#print axioms PDT.RulerMinpoly.ruler_conjugates_card
#print axioms PDT.RulerMinpoly.mem_ruler_rootSet
#print axioms PDT.RulerMinpoly.ruler_unit
#print axioms PDT.RulerMinpoly.rulerPoly_coeff_nine
#print axioms PDT.RulerMinpoly.rulerPoly_coeff_three
#print axioms PDT.RulerMinpoly.rulerPoly_nonreciprocal
#print axioms PDT.RulerMinpoly.cubic_minpoly
#print axioms PDT.RulerMinpoly.quartic_minpoly
#print axioms PDT.RulerMinpoly.cubic_finrank
#print axioms PDT.RulerMinpoly.quartic_finrank
#print axioms PDT.RulerMinpoly.ruler_degree_multiplicative
#print axioms PDT.RulerMinpoly.ruler_compositum_sup
#print axioms PDT.RulerMinpoly.ruler_compositum_finrank
#print axioms PDT.RulerMinpoly.ruler_linearDisjoint
