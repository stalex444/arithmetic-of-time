import Mathlib
import ConstantChain
import FieldNorm
import Irreducibility

/-!
# AlgebraicIntegers — no monomial `ρᵃQᵇ` equals a threshold constant

Consider monomials `ρᵃQᵇ`, where `ρ` is the real root of `x³ − x − 1` and `Q`
the positive real root of `x⁴ − x − 1`. Both defining polynomials are **monic
with integer coefficients**, so `ρ` and `Q` are **algebraic integers**; hence so
is every product `ρᵃQᵇ` (`a, b ≥ 0`), because the algebraic integers form a ring
closed under products and powers.

The threshold constant `r_in = √3/2` (the Voronoi in-radius of the unit,
`Time.rin` from `ConstantChain`) is **not** an algebraic integer: its square
is the rational `3/4`, and `ℤ` is integrally closed in `ℚ`, so a rational
algebraic integer must be an actual integer — but `3/4 ∉ ℤ`.

Consequently **no monomial `ρᵃQᵇ` can EQUAL the threshold**:
`r_in ≠ ρᵃQᵇ` for every `a, b : ℕ`. Hence the strict chain
`κ < r_in < χ < A*` (proved in `ConstantChain`) can never collapse into an
algebraic coincidence — the separation is rigid, because one side lives in the
ring of algebraic integers and the other provably does not.

## Theorems

* **T-INTEGRAL** (`rho_isIntegral`, `Q_isIntegral`): any real `r` with
  `r³ = r + 1`, and any real `q` with `q⁴ = q + 1`, is an algebraic integer
  over `ℤ`, witnessed by the monic integer polynomials `X³ − X − 1` and
  `X⁴ − X − 1`. (Quantifies over ALL such reals — strictly stronger than
  fixing the particular roots ρ, Q, each of which is the unique such positive
  real; matches the `ConstantChain` house style.)
* **T-NOT-INTEGRAL** (`rin_not_isIntegral`): `r_in = √3/2` is NOT an algebraic
  integer over `ℤ`. Route: `(√3/2)² = 3/4`; if `r_in` were integral so would
  `3/4` be; reflect `ℤ → ℚ → ℝ` with `IsIntegral.tower_bot_of_field`; then
  `IsIntegrallyClosed.isIntegral_iff` (`ℤ` integrally closed in its fraction
  field `ℚ`) forces `3/4 = ↑n` for some `n : ℤ`, impossible.
* **T-PRODUCT** (`pow_mul_isIntegral`): every coupling monomial `rᵃqᵇ`
  (`a, b : ℕ`) is an algebraic integer — `IsIntegral.pow` + `IsIntegral.mul`.
* **T-NO-IDENTITY** (`rin_ne_coupling_monomial`): the payload —
  `r_in ≠ rᵃqᵇ` for all `a, b : ℕ`. An algebraic integer can never equal a
  non-algebraic-integer.
* **T-INVERSE-INTEGRAL** (`rho_inv_isIntegral`, `Q_inv_isIntegral`,
  `zpow_zmul_isIntegral`): `ρ⁻¹ = ρ² − 1` and `Q⁻¹ = Q³ − 1` are polynomials
  in ρ, Q hence also algebraic integers, so `rᵃqᵇ` is an algebraic integer for
  ALL integer exponents `a, b : ℤ` — the no-identity conclusion extends to the
  full multiplicative group of coupling monomials (`rin_ne_coupling_zmonomial`).
* **T-ASTAR-NOT-INTEGRAL** (`sqrt_two_mul_isIntegral`, `radicand_not_isIntegral`,
  `Astar_not_isIntegral`, `Astar_ne_coupling_monomial`,
  `Astar_ne_coupling_zmonomial`): the UPPER threshold
  `A* = √(2ρ) − √(3/4 − ρ⁻²)` is also NOT an algebraic integer, so `A* ≠ ρᵃQᵇ`
  for all integer exponents. Route with NO Galois machinery: `√(2ρ)` is an
  algebraic integer (root of `X⁶ − 4X² − 8`); if `A*` were integral then
  `√(3/4 − ρ⁻²) = √(2ρ) − A*` and hence `3/4 − ρ⁻² = ρ² − ρ − 1/4` would be
  integral — but the latter lives in the cubic field `ℚ(ρ)` with minimal
  polynomial `X³ − (5/4)X² + (35/16)X − 23/64` (`X²`-coefficient `−5/4 ∉ ℤ`),
  and `ℤ` integrally closed forbids that. Degree `3` is pinned by
  `ℚ⟮v⟯ = ℚ⟮ρ⟯` (`v = ρ²−ρ−1/4`, `ρ = (3−4v)/(4v+1)`). This completes the
  untunable chain: NO coupling monomial meets EITHER trace-geometry threshold.
* **T-UNIT** (`rho_norm_one`, `Q_norm_neg_one`): the two-sided companion —
  `N(ρ) = 1` and `N(Q) = −1` (re-exported from `FieldNorm`), so ρ, Q are
  algebraic UNITS while r_in is not even an algebraic integer. "Coupling
  monomials are units; the threshold is not even an integer."

## Faithfulness notes (reformulations, none weakening)

* Every statement quantifies over ALL real roots of the defining equations,
  not a chosen embedding — this is *stronger* than a statement about fixed ρ, Q.
* `rin` is imported verbatim from `ConstantChain` (`√3/2`), so
  `rin_ne_coupling_monomial` is literally about the chain's certification
  radius.
* "algebraic integer" is Mathlib's `IsIntegral ℤ`; "unit" is captured through
  `Algebra.norm ℚ = ±1` (re-exported `FieldNorm.norm_ρ`, `FieldNorm.norm_Q`).
* The integer-exponent extension (`ℤ` exponents) uses the exact banked
  identities `ρ⁻¹ = ρ² − 1`, `Q⁻¹ = Q³ − 1` (algebraic consequences of the
  defining equations), so nothing new is posited.

## Both thresholds now closed (no remaining seam)

Both the LOWER threshold `r_in = √3/2` and the UPPER threshold
`A* = √(2ρ) − √(3/4 − ρ⁻²)` are proved NON-integral (`rin_not_isIntegral`,
`Astar_not_isIntegral`), so the full strict chain `κ < r_in < χ < A*` from
`ConstantChain` can never collapse into an algebraic identity with a
coupling monomial `ρᵃQᵇ` at ANY of its rungs — untunable forever, both ends,
at all integer exponents. The `A*` argument avoids the Galois tower originally
anticipated: reducing `A*`'s non-integrality to the single cubic-field fact
`ρ² − ρ − 1/4 ∉ 𝒪_{ℚ(ρ)}` via the concrete algebraic integer `√(2ρ)`.
-/

open Polynomial

namespace Time

noncomputable section

/-! ## T-INTEGRAL — ρ and Q are algebraic integers -/

/-- The monic integer cubic `X³ − X − 1` witnessing that ρ is integral. -/
def pRho : ℤ[X] := X ^ 3 - X - 1

/-- The monic integer quartic `X⁴ − X − 1` witnessing that Q is integral. -/
def pQ : ℤ[X] := X ^ 4 - X - 1

theorem monic_pRho : pRho.Monic := by unfold pRho; monicity!
theorem monic_pQ : pQ.Monic := by unfold pQ; monicity!

/-- **T-INTEGRAL (ρ).** Any real `r` with `r³ = r + 1` is an algebraic integer
over `ℤ`, witnessed by the monic integer polynomial `X³ − X − 1`. -/
theorem rho_isIntegral {r : ℝ} (hr : r ^ 3 = r + 1) : IsIntegral ℤ r :=
  ⟨pRho, monic_pRho, by
    unfold pRho
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]
    linear_combination hr⟩

/-- **T-INTEGRAL (Q).** Any real `q` with `q⁴ = q + 1` is an algebraic integer
over `ℤ`, witnessed by the monic integer polynomial `X⁴ − X − 1`. -/
theorem Q_isIntegral {q : ℝ} (hq : q ^ 4 = q + 1) : IsIntegral ℤ q :=
  ⟨pQ, monic_pQ, by
    unfold pQ
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]
    linear_combination hq⟩

/-! ## T-NOT-INTEGRAL — r_in = √3/2 is not an algebraic integer -/

/-- `3/4 : ℚ` is not an algebraic integer over `ℤ`: `ℤ` is integrally closed
in its fraction field `ℚ`, so a rational algebraic integer is an integer, and
`3/4 ∉ ℤ`. -/
theorem not_isIntegral_three_quarters : ¬ IsIntegral ℤ ((3 : ℚ) / 4) := by
  intro h
  rw [IsIntegrallyClosed.isIntegral_iff] at h
  obtain ⟨y, hy⟩ := h
  rw [eq_intCast] at hy
  -- hy : (y : ℚ) = 3 / 4  ⟹  4 * y = 3 in ℤ, impossible
  have h4 : (4 : ℚ) * (y : ℚ) = 3 := by rw [hy]; norm_num
  have : (4 * y : ℤ) = 3 := by exact_mod_cast h4
  omega

/-- **T-NOT-INTEGRAL.** `r_in = √3/2` is NOT an algebraic integer over `ℤ`.
If it were, its square `3/4` would be too; reflecting `ℤ ⊂ ℚ ⊂ ℝ` and using
that `ℤ` is integrally closed in `ℚ` forces `3/4 ∈ ℤ`, a contradiction. -/
theorem rin_not_isIntegral : ¬ IsIntegral ℤ rin := by
  intro h
  -- square is integral
  have hsq : IsIntegral ℤ (rin ^ 2) := h.pow 2
  -- rin² = 3/4
  have heq : rin ^ 2 = 3 / 4 := by
    rw [rin, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [heq] at hsq
  -- (3:ℝ)/4 is the image of (3:ℚ)/4 under ℚ → ℝ
  have hmap : (3 : ℝ) / 4 = algebraMap ℚ ℝ ((3 : ℚ) / 4) := by
    rw [map_div₀]; norm_num
  rw [hmap] at hsq
  exact not_isIntegral_three_quarters (hsq.tower_bot_of_field)

/-! ## T-PRODUCT and T-NO-IDENTITY -/

/-- **T-PRODUCT.** Every coupling monomial `rᵃqᵇ` (`a, b : ℕ`) is an algebraic
integer: products and powers of algebraic integers are algebraic integers. -/
theorem pow_mul_isIntegral {r q : ℝ} (hr : r ^ 3 = r + 1) (hq : q ^ 4 = q + 1)
    (a b : ℕ) : IsIntegral ℤ (r ^ a * q ^ b) :=
  ((rho_isIntegral hr).pow a).mul ((Q_isIntegral hq).pow b)

/-- **T-NO-IDENTITY (payload).** The trace-geometry threshold `r_in = √3/2`
is never equal to a coupling monomial `rᵃqᵇ` (`a, b : ℕ`): the left side is
not an algebraic integer, the right side always is. The strict chain
`κ < r_in < χ < A*` (`ConstantChain.chain_strict`) can therefore never
collapse into an algebraic identity — untunable forever. -/
theorem rin_ne_coupling_monomial {r q : ℝ} (hr : r ^ 3 = r + 1)
    (hq : q ^ 4 = q + 1) (a b : ℕ) : rin ≠ r ^ a * q ^ b := by
  intro heq
  apply rin_not_isIntegral
  rw [heq]
  exact pow_mul_isIntegral hr hq a b

/-! ## T-INVERSE-INTEGRAL — extension to all integer exponents -/

/-- `ρ⁻¹ = ρ² − 1` (banked exact identity, from `r³ = r + 1`, `r ≠ 0`). -/
theorem rho_inv_eq {r : ℝ} (hr : r ^ 3 = r + 1) : r⁻¹ = r ^ 2 - 1 := by
  have hrne : r ≠ 0 := by
    rintro rfl; norm_num at hr
  field_simp
  linear_combination -hr

/-- `Q⁻¹ = Q³ − 1` (banked exact identity, from `q⁴ = q + 1`, `q ≠ 0`). -/
theorem Q_inv_eq {q : ℝ} (hq : q ^ 4 = q + 1) : q⁻¹ = q ^ 3 - 1 := by
  have hqne : q ≠ 0 := by
    rintro rfl; norm_num at hq
  field_simp
  linear_combination -hq

/-- **T-INVERSE-INTEGRAL (ρ).** `ρ⁻¹` is an algebraic integer, because it
equals the polynomial `ρ² − 1` in the algebraic integer ρ. -/
theorem rho_inv_isIntegral {r : ℝ} (hr : r ^ 3 = r + 1) : IsIntegral ℤ r⁻¹ := by
  rw [rho_inv_eq hr]
  exact ((rho_isIntegral hr).pow 2).sub isIntegral_one

/-- **T-INVERSE-INTEGRAL (Q).** `Q⁻¹` is an algebraic integer, because it
equals the polynomial `Q³ − 1` in the algebraic integer Q. -/
theorem Q_inv_isIntegral {q : ℝ} (hq : q ^ 4 = q + 1) : IsIntegral ℤ q⁻¹ := by
  rw [Q_inv_eq hq]
  exact ((Q_isIntegral hq).pow 3).sub isIntegral_one

/-- Integer power of an algebraic integer whose inverse is also integral is
integral. -/
theorem isIntegral_zpow {x : ℝ} (hx : IsIntegral ℤ x) (hxi : IsIntegral ℤ x⁻¹)
    (n : ℤ) : IsIntegral ℤ (x ^ n) := by
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast]; exact hx.pow m
  · rw [zpow_negSucc, ← inv_pow]; exact hxi.pow (m + 1)

/-- **T-PRODUCT (integer exponents).** Every coupling monomial `rᵃqᵇ` with
`a, b : ℤ` is an algebraic integer — ρ, Q are units so negative exponents stay
integral (`ρ⁻¹ = ρ²−1`, `Q⁻¹ = Q³−1`). -/
theorem zpow_zmul_isIntegral {r q : ℝ} (hr : r ^ 3 = r + 1) (hq : q ^ 4 = q + 1)
    (a b : ℤ) : IsIntegral ℤ (r ^ a * q ^ b) :=
  (isIntegral_zpow (rho_isIntegral hr) (rho_inv_isIntegral hr) a).mul
    (isIntegral_zpow (Q_isIntegral hq) (Q_inv_isIntegral hq) b)

/-- **T-NO-IDENTITY (integer exponents).** `r_in ≠ rᵃqᵇ` for ALL `a, b : ℤ` —
the no-identity separation holds across the full multiplicative group of
coupling monomials, not just the non-negative cone. -/
theorem rin_ne_coupling_zmonomial {r q : ℝ} (hr : r ^ 3 = r + 1)
    (hq : q ^ 4 = q + 1) (a b : ℤ) : rin ≠ r ^ a * q ^ b := by
  intro heq
  apply rin_not_isIntegral
  rw [heq]
  exact zpow_zmul_isIntegral hr hq a b

/-! ## T-ASTAR-NOT-INTEGRAL — the ambiguity threshold `A*` is not an algebraic integer -/

/-- **√(2ρ) is an algebraic integer.** `s = √(2ρ)` satisfies the monic integer
sextic `X⁶ − 4X² − 8` (`s⁶ = (2ρ)³ = 8ρ³ = 8ρ + 8 = 4s² + 8`), so it is integral
over `ℤ`. Cleanly: `s² = 2ρ` is integral (`2·ρ`), and `x²` integral forces `x`
integral (`IsIntegral.of_pow`). -/
theorem sqrt_two_mul_isIntegral {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) (hρ0 : 0 ≤ ρ) :
    IsIntegral ℤ (Real.sqrt (2 * ρ)) := by
  have h2r : IsIntegral ℤ (2 * ρ) := by
    have h := (rho_isIntegral hρ).add (rho_isIntegral hρ)
    simpa [two_mul] using h
  have hsq : Real.sqrt (2 * ρ) ^ 2 = 2 * ρ := Real.sq_sqrt (by positivity)
  have : IsIntegral ℤ (Real.sqrt (2 * ρ) ^ 2) := by rw [hsq]; exact h2r
  exact this.of_pow (by norm_num)

open IntermediateField in
/-- **The radicand difference `v = ρ² − ρ − 1/4` is NOT an algebraic integer.**
(`v = 3/4 − ρ⁻²`, the inner radicand of `A*` rewritten via `ρ⁻² = −ρ² + ρ + 1`.)
`v` lives in the cubic field `ℚ(ρ)`; its minimal polynomial over `ℚ` is
`X³ − (5/4)X² + (35/16)X − 23/64`, whose `X²`-coefficient `−5/4 ∉ ℤ`. Since `ℤ`
is integrally closed, the minimal polynomial of an integral element has integer
coefficients — contradiction. Degree `3` is pinned by `ℚ⟮v⟯ = ℚ⟮ρ⟯`: each field
contains the other's generator (`v = ρ²−ρ−1/4`, and `ρ = (3−4v)/(4v+1)`). -/
theorem radicand_not_isIntegral {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    ¬ IsIntegral ℤ (ρ ^ 2 - ρ - 1 / 4) := by
  intro hint
  have hρ0 : ρ ≠ 0 := by rintro rfl; norm_num at hρ
  have hρ1 : ρ ≠ 1 := by rintro rfl; norm_num at hρ
  set w : ℝ := ρ ^ 2 - ρ - 1 / 4 with hwdef
  -- the candidate minimal polynomial of `w` over `ℚ`
  set q : ℚ[X] := X ^ 3 - C (5 / 4) * X ^ 2 + C (35 / 16) * X - C (23 / 64) with hqdef
  have hqmonic : q.Monic := by rw [hqdef]; monicity!
  have hqdeg : q.natDegree = 3 := by rw [hqdef]; compute_degree!
  -- `w` is a root of `q`
  have hqroot : (Polynomial.aeval w) q = 0 := by
    rw [hqdef, hwdef]
    simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, map_div₀, map_ofNat]
    linear_combination (ρ ^ 3 - 3 * ρ ^ 2 + 2 * ρ + 1) * hρ
  -- `w` and `ρ` are algebraic over `ℚ`
  have hwalg : IsIntegral ℚ w := hint.tower_top
  have hρalg : IsIntegral ℚ ρ := (rho_isIntegral hρ).tower_top
  -- `minpoly ℚ ρ = X³ − X − 1`, so `[ℚ(ρ):ℚ] = 3`
  have hminρ : (X ^ 3 - X - 1 : ℚ[X]) = minpoly ℚ ρ :=
    minpoly.eq_of_irreducible_of_monic cubicQ_irreducible
      (by simp only [map_sub, map_pow, map_one, aeval_X]; linear_combination hρ)
      (by monicity!)
  have hfrρ : Module.finrank ℚ ℚ⟮ρ⟯ = 3 := by
    rw [adjoin.finrank hρalg, ← hminρ]; compute_degree!
  -- `ℚ⟮w⟯ = ℚ⟮ρ⟯`
  have hw_mem : w ∈ ℚ⟮ρ⟯ := by
    have hρmem : ρ ∈ ℚ⟮ρ⟯ := mem_adjoin_simple_self ℚ ρ
    have h14 : (1 / 4 : ℝ) ∈ ℚ⟮ρ⟯ := by
      simpa only [map_div₀, map_one, map_ofNat] using
        IntermediateField.algebraMap_mem ℚ⟮ρ⟯ (1 / 4 : ℚ)
    rw [hwdef]
    exact sub_mem (sub_mem (pow_mem hρmem 2) hρmem) h14
  have hρ_mem : ρ ∈ ℚ⟮w⟯ := by
    have hwmem : w ∈ ℚ⟮w⟯ := mem_adjoin_simple_self ℚ w
    have h3 : (3 : ℝ) ∈ ℚ⟮w⟯ := by
      simpa only [map_ofNat] using IntermediateField.algebraMap_mem ℚ⟮w⟯ (3 : ℚ)
    have h4 : (4 : ℝ) ∈ ℚ⟮w⟯ := by
      simpa only [map_ofNat] using IntermediateField.algebraMap_mem ℚ⟮w⟯ (4 : ℚ)
    have hden : (4 * w + 1 : ℝ) ≠ 0 := by
      rw [hwdef]
      have hfac : 4 * (ρ ^ 2 - ρ - 1 / 4) + 1 = (4 * ρ) * (ρ - 1) := by ring
      rw [hfac]
      exact mul_ne_zero (mul_ne_zero (by norm_num) hρ0) (sub_ne_zero.mpr hρ1)
    have heq : ρ = (3 - 4 * w) / (4 * w + 1) := by
      rw [eq_div_iff hden, hwdef]; linear_combination 4 * hρ
    rw [heq]
    exact div_mem (sub_mem h3 (mul_mem h4 hwmem)) (add_mem (mul_mem h4 hwmem) (one_mem _))
  have hfe : ℚ⟮w⟯ = ℚ⟮ρ⟯ :=
    le_antisymm (by rw [adjoin_simple_le_iff]; exact hw_mem)
      (by rw [adjoin_simple_le_iff]; exact hρ_mem)
  have hminwdeg : (minpoly ℚ w).natDegree = 3 := by
    have h := adjoin.finrank hwalg
    rw [hfe, hfrρ] at h
    exact h.symm
  -- hence `q = minpoly ℚ w`
  have hdvd : minpoly ℚ w ∣ q := minpoly.dvd ℚ w hqroot
  have hmin_eq : q = minpoly ℚ w :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hwalg) hqmonic hdvd
      (Nat.le_of_eq (hqdeg.trans hminwdeg.symm))
  -- but integrality over `ℤ` forces `minpoly ℚ w` to have integer coefficients
  have hmap := minpoly.isIntegrallyClosed_eq_field_fractions' (R := ℤ) ℚ hint
  have hq2 : q.coeff 2 = -(5 / 4) := by
    rw [hqdef]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    norm_num
  have key : (-(5 / 4) : ℚ) = algebraMap ℤ ℚ ((minpoly ℤ w).coeff 2) := by
    rw [← hq2, hmin_eq, hmap, coeff_map]
  rw [eq_intCast (algebraMap ℤ ℚ)] at key
  have h4n : (4 * (minpoly ℤ w).coeff 2 : ℤ) = -5 := by
    have hcast : (4 : ℚ) * ((minpoly ℤ w).coeff 2 : ℚ) = -5 := by rw [← key]; norm_num
    exact_mod_cast hcast
  omega

/-- **T-ASTAR-NOT-INTEGRAL.** The ambiguity threshold
`A* = √(2ρ) − √(3/4 − ρ⁻²)` is NOT an algebraic integer over `ℤ`.
Route (no Galois machinery): `√(2ρ)` IS an algebraic integer
(`sqrt_two_mul_isIntegral`); if `A*` were integral, then
`√(3/4 − ρ⁻²) = √(2ρ) − A*` would be too, hence its square
`3/4 − ρ⁻² = ρ² − ρ − 1/4` would be an algebraic integer — contradicting
`radicand_not_isIntegral`. -/
theorem Astar_not_isIntegral {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) (hρ0 : 0 < ρ) :
    ¬ IsIntegral ℤ (Astar ρ) := by
  intro hint
  have hs : IsIntegral ℤ (Real.sqrt (2 * ρ)) := sqrt_two_mul_isIntegral hρ hρ0.le
  -- √(3/4 − ρ⁻²) = √(2ρ) − A*, so it is integral
  have htdef : Real.sqrt (3 / 4 - (ρ ^ 2)⁻¹) = Real.sqrt (2 * ρ) - Astar ρ := by
    rw [Astar]; ring
  have ht : IsIntegral ℤ (Real.sqrt (3 / 4 - (ρ ^ 2)⁻¹)) := by
    rw [htdef]; exact hs.sub hint
  -- its square `3/4 − ρ⁻²` is integral
  have htsq : Real.sqrt (3 / 4 - (ρ ^ 2)⁻¹) ^ 2 = 3 / 4 - (ρ ^ 2)⁻¹ :=
    Real.sq_sqrt (radicand_pos hρ hρ0).le
  have hval : IsIntegral ℤ (3 / 4 - (ρ ^ 2)⁻¹) := by rw [← htsq]; exact ht.pow 2
  -- `3/4 − ρ⁻² = ρ² − ρ − 1/4`
  have hident : (3 / 4 - (ρ ^ 2)⁻¹) = ρ ^ 2 - ρ - 1 / 4 := by
    have hinv2 : (ρ ^ 2)⁻¹ = -ρ ^ 2 + ρ + 1 :=
      inv_eq_of_mul_eq_one_left (by linear_combination (1 - ρ) * hρ)
    rw [hinv2]; ring
  rw [hident] at hval
  exact radicand_not_isIntegral hρ hval

/-- **T-NO-IDENTITY (A\*).** The ambiguity threshold `A*` is never equal to a
coupling monomial `rᵃqᵇ` (`a, b : ℕ`): the left side is not an algebraic integer,
the right side always is. Together with `rin_ne_coupling_monomial`, this completes
the untunable chain `κ < r_in < χ < A*` — no coupling monomial `ρᵃQᵇ` can meet
*either* trace-geometry threshold, at any integer exponents. -/
theorem Astar_ne_coupling_monomial {r q : ℝ} (hr : r ^ 3 = r + 1) (hr0 : 0 < r)
    (hq : q ^ 4 = q + 1) (a b : ℕ) : Astar r ≠ r ^ a * q ^ b := by
  intro heq
  apply Astar_not_isIntegral hr hr0
  rw [heq]
  exact pow_mul_isIntegral hr hq a b

/-- **T-NO-IDENTITY (A\*, integer exponents).** `A* ≠ rᵃqᵇ` for ALL `a, b : ℤ`. -/
theorem Astar_ne_coupling_zmonomial {r q : ℝ} (hr : r ^ 3 = r + 1) (hr0 : 0 < r)
    (hq : q ^ 4 = q + 1) (a b : ℤ) : Astar r ≠ r ^ a * q ^ b := by
  intro heq
  apply Astar_not_isIntegral hr hr0
  rw [heq]
  exact zpow_zmul_isIntegral hr hq a b

/-! ## T-UNIT — the two-sided companion (re-exported norms) -/

/-- **T-UNIT (ρ).** `N(ρ) = 1`: ρ is an algebraic unit (re-exported from
`FieldNorm`, here as `Algebra.norm ℚ (AdjoinRoot.root (X⁴ … ))`). -/
theorem rho_norm_one : Algebra.norm ℚ (AdjoinRoot.root Time.fρ) = 1 := Time.norm_ρ

/-- **T-UNIT (Q).** `N(Q) = −1`: Q is an algebraic unit. -/
theorem Q_norm_neg_one : Algebra.norm ℚ (AdjoinRoot.root Time.fQ) = -1 := Time.norm_Q

end

end Time
