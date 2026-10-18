module
public import Mathlib
public import Irreducibility
public import Settling
public import PisotBoundary

@[expose] public section

/-!
# BetaIrrational — the distinguished slope is irrational

Let `ρ` be the real root of `x³ − x − 1` and `w` a non-real root of
`x⁴ − x − 1`. The slope distinguished by the paper is
`β = log ‖w‖ / (½ log ρ)`. This module proves that `β` is irrational
(`Time.beta_irrational`), in the multiplicative form
`(normSq w)^n ≠ ρ^k` for all natural `k` and all `n ≥ 1`
(`Time.normSq_pow_ne_rho_pow`).

## The argument

Suppose `(normSq w)^n = ρ^k` with `n ≥ 1`. Let `σ` be a non-real root of the
cubic, so `ρ · normSq σ = 1` (`Time.tick_contraction`). The cubic is the
minimal polynomial of `ρ` over `ℚ` (`Time.cubicQ_irreducible`), so there is a
`ℚ`-embedding `φ` of the field `ℚ(ρ, w, w̄) ⊂ ℂ` into `ℂ` with `φ ρ = σ`.
Applying `φ` to `(w · w̄)^n = ρ^k` and taking `normSq`, the two roots
`a = φ w`, `b = φ w̄` of the quartic satisfy
`normSq a · normSq b · normSq w = 1`.

The quartic factors over `ℝ` as `(x − Q)(x − Q')(x² + s x + t)` with
`Q ∈ [6/5, 5/4]`, `Q' ∈ [−3/4, −7/10]` its two real roots, `s = Q + Q'`,
`t = Q² + Q Q' + Q'²`, and `Q Q' t = −1`; the quadratic factor has no real
root, and each of its roots has `normSq = t`. So every complex root `z` of
the quartic has `normSq z ∈ {Q², Q'², t}`, and `normSq w = t`. A check of
the six products `x · y · t` with `x, y ∈ {Q², Q'², t}` against the bounds
shows that none equals `1`. This contradiction proves the claim.

No Galois group is computed, and no transcendence theory (Baker,
Gelfond–Schneider) is used.

## Scope

* This module proves only the irrationality of `β`. It does not prove that
  `0 < β < 1`.
* It does not connect `β` to any physical reading.
-/

namespace Time

open Polynomial Complex

/-! ### The quartic: two real roots and one conjugate pair -/

/-- The quartic `x⁴ − x − 1` has a real root in `[6/5, 5/4]` and a real root in
`[−3/4, −7/10]`. -/
lemma quartic_two_real_roots : ∃ Q Q' : ℝ, Q ^ 4 = Q + 1 ∧ Q' ^ 4 = Q' + 1 ∧
    6 / 5 ≤ Q ∧ Q ≤ 5 / 4 ∧ -3 / 4 ≤ Q' ∧ Q' ≤ -7 / 10 := by
  have hc : Continuous (fun y : ℝ => y ^ 4 - y - 1) := by fun_prop
  obtain ⟨Q, ⟨hQ1, hQ2⟩, hQ⟩ :=
    intermediate_value_Icc (by norm_num : (6 / 5 : ℝ) ≤ 5 / 4) hc.continuousOn
      (show (0 : ℝ) ∈ Set.Icc ((6 / 5 : ℝ) ^ 4 - 6 / 5 - 1) ((5 / 4 : ℝ) ^ 4 - 5 / 4 - 1) by
        norm_num)
  obtain ⟨Q', ⟨hQ'1, hQ'2⟩, hQ'⟩ :=
    intermediate_value_Icc' (by norm_num : (-3 / 4 : ℝ) ≤ -7 / 10) hc.continuousOn
      (show (0 : ℝ) ∈ Set.Icc ((-7 / 10 : ℝ) ^ 4 - (-7 / 10) - 1)
          ((-3 / 4 : ℝ) ^ 4 - (-3 / 4) - 1) by norm_num)
  simp only at hQ hQ'
  exact ⟨Q, Q', by linarith, by linarith, hQ1, hQ2, hQ'1, hQ'2⟩

/-- The cofactor relation: for two distinct real roots `Q ≠ Q'` of the quartic,
`Q³ + Q²Q' + QQ'² + Q'³ = 1`. -/
lemma quartic_pair_relation {Q Q' : ℝ} (hQ : Q ^ 4 = Q + 1) (hQ' : Q' ^ 4 = Q' + 1)
    (hne : Q ≠ Q') : Q ^ 3 + Q ^ 2 * Q' + Q * Q' ^ 2 + Q' ^ 3 = 1 := by
  have h : (Q - Q') * (Q ^ 3 + Q ^ 2 * Q' + Q * Q' ^ 2 + Q' ^ 3 - 1) = 0 := by
    linear_combination hQ - hQ'
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · linarith

/-- The quartic factors over `ℂ` through its two real roots. -/
lemma quartic_factor {Q Q' : ℝ} (hQ : Q ^ 4 = Q + 1) (hQ' : Q' ^ 4 = Q' + 1)
    (hne : Q ≠ Q') (z : ℂ) :
    z ^ 4 - z - 1 = (z - Q) * (z - Q') *
      (z ^ 2 + ((Q + Q' : ℝ) : ℂ) * z + ((Q ^ 2 + Q * Q' + Q' ^ 2 : ℝ) : ℂ)) := by
  have e1 := quartic_pair_relation hQ hQ' hne
  have e1C : (Q : ℂ) ^ 3 + (Q : ℂ) ^ 2 * Q' + Q * (Q' : ℂ) ^ 2 + (Q' : ℂ) ^ 3 = 1 := by
    exact_mod_cast e1
  have hQC : (Q : ℂ) ^ 4 = Q + 1 := by exact_mod_cast hQ
  push_cast
  linear_combination (z - Q) * e1C + hQC

/-- The constant term: `Q Q' t = −1`, with `t = Q² + QQ' + Q'²`. -/
lemma quartic_const {Q Q' : ℝ} (hQ : Q ^ 4 = Q + 1) (hQ' : Q' ^ 4 = Q' + 1)
    (hne : Q ≠ Q') : Q * Q' * (Q ^ 2 + Q * Q' + Q' ^ 2) = -1 := by
  have e1 := quartic_pair_relation hQ hQ' hne
  linear_combination Q * e1 - hQ

/-- A root of a real quadratic `z² + s z + t` with negative discriminant is
non-real and has `normSq z = t`. -/
lemma quad_root_normSq {s t : ℝ} (hd : s ^ 2 < 4 * t) {z : ℂ}
    (hz : z ^ 2 + (s : ℂ) * z + (t : ℂ) = 0) : normSq z = t ∧ z.im ≠ 0 := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp [pow_two] at hre him
  have hy : z.im ≠ 0 := by
    intro hy
    rw [hy] at hre
    nlinarith [sq_nonneg (2 * z.re + s)]
  have hx : 2 * z.re + s = 0 := by
    have h : z.im * (2 * z.re + s) = 0 := by linear_combination him
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hy
    · exact h
  refine ⟨?_, hy⟩
  rw [Complex.normSq_apply]
  linear_combination (-1 : ℝ) * hre + z.re * hx

/-- Every complex root of the quartic has `normSq` equal to `Q²`, `Q'²` or `t`,
and a non-real root has `normSq` equal to `t`. -/
lemma quartic_root_normSq {Q Q' : ℝ} (hQ : Q ^ 4 = Q + 1) (hQ' : Q' ^ 4 = Q' + 1)
    (hne : Q ≠ Q') (hQpos : 0 < Q) {z : ℂ} (hz : z ^ 4 = z + 1) :
    (normSq z = Q ^ 2 ∨ normSq z = Q' ^ 2 ∨ normSq z = Q ^ 2 + Q * Q' + Q' ^ 2) ∧
      (z.im ≠ 0 → normSq z = Q ^ 2 + Q * Q' + Q' ^ 2) := by
  have h := quartic_factor hQ hQ' hne z
  rw [show z ^ 4 - z - 1 = 0 by rw [hz]; ring] at h
  rcases mul_eq_zero.mp h.symm with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · have hzQ : z = Q := sub_eq_zero.mp h2
      subst hzQ
      refine ⟨Or.inl (by rw [Complex.normSq_ofReal]; ring), fun him => ?_⟩
      simp at him
    · have hzQ : z = Q' := sub_eq_zero.mp h2
      subst hzQ
      refine ⟨Or.inr (Or.inl (by rw [Complex.normSq_ofReal]; ring)), fun him => ?_⟩
      simp at him
  · have hd : (Q + Q') ^ 2 < 4 * (Q ^ 2 + Q * Q' + Q' ^ 2) := by
      nlinarith [sq_nonneg (Q + Q'), mul_pos hQpos hQpos, sq_nonneg Q']
    have hq := quad_root_normSq hd h1
    exact ⟨Or.inr (Or.inr hq.1), fun _ => hq.1⟩

/-- **The norm products.** With the root bounds, no product `x · y · t` with
`x, y ∈ {Q², Q'², t}` equals `1`. -/
lemma norm_products_ne_one {Q Q' x y : ℝ} (hQa : 6 / 5 ≤ Q) (hQb : Q ≤ 5 / 4)
    (hQ'a : -3 / 4 ≤ Q') (hQ'b : Q' ≤ -7 / 10)
    (hPt : Q * Q' * (Q ^ 2 + Q * Q' + Q' ^ 2) = -1)
    (hx : x = Q ^ 2 ∨ x = Q' ^ 2 ∨ x = Q ^ 2 + Q * Q' + Q' ^ 2)
    (hy : y = Q ^ 2 ∨ y = Q' ^ 2 ∨ y = Q ^ 2 + Q * Q' + Q' ^ 2) :
    x * y * (Q ^ 2 + Q * Q' + Q' ^ 2) ≠ 1 := by
  set t := Q ^ 2 + Q * Q' + Q' ^ 2 with ht
  -- `m = −Q Q'` lies in `[21/25, 15/16]` and `m · t = 1`.
  have hm1 : 21 / 25 ≤ -(Q * Q') := by nlinarith
  have hm2 : -(Q * Q') ≤ 15 / 16 := by nlinarith
  have hmt : -(Q * Q') * t = 1 := by linear_combination -hPt
  have htpos : 0 < t := by nlinarith
  have ht1 : 1 < t := by nlinarith
  have ht2 : t ≤ 25 / 21 := by nlinarith
  -- `Q' t = −1/Q`, so `|Q' t| < 1`.
  have hQ't : Q * (Q' * t) = -1 := by linear_combination hPt
  have hQ't1 : -1 < Q' * t := by nlinarith
  have hQ't2 : Q' * t < 0 := by nlinarith
  have hQ2 : 36 / 25 ≤ Q ^ 2 := by nlinarith
  have hQ'2 : Q' ^ 2 ≤ 9 / 16 := by nlinarith
  have hQ'2' : 0 ≤ Q' ^ 2 := sq_nonneg _
  intro h
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · -- Q² · Q² · t > 1
    nlinarith [mul_le_mul hQ2 hQ2 (by norm_num) (by positivity)]
  · -- Q² · Q'² · t = −Q Q' < 1
    have : Q ^ 2 * Q' ^ 2 * t = -(Q * Q') := by linear_combination (-(Q * Q')) * hmt
    linarith
  · -- Q² · t · t = (Q t)² > 1
    nlinarith [mul_le_mul hQ2 ht1.le (by norm_num) (by positivity)]
  · have : Q' ^ 2 * Q ^ 2 * t = -(Q * Q') := by linear_combination (-(Q * Q')) * hmt
    linarith
  · -- Q'⁴ t < 1
    nlinarith [mul_le_mul hQ'2 hQ'2 hQ'2' (by norm_num)]
  · -- Q'² t² = (Q' t)² < 1
    nlinarith
  · nlinarith [mul_le_mul hQ2 ht1.le (by norm_num) (by positivity)]
  · nlinarith
  · -- t³ > 1
    nlinarith [mul_lt_mul ht1 ht1.le one_pos htpos.le]

/-! ### A non-real root of the cubic -/

/-- The cubic `x³ − x − 1` has a root `σ` with `ρ · normSq σ = 1`. -/
lemma exists_cubic_conj_root {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    ∃ σ : ℂ, σ ^ 3 = σ + 1 ∧ ρ * normSq σ = 1 := by
  have hρ1 : 1 < ρ := one_lt_root hρ
  have hd : 0 ≤ 3 * ρ ^ 2 - 4 := by nlinarith
  set h : ℝ := Real.sqrt (3 * ρ ^ 2 - 4) / 2 with hh
  have hh2 : h ^ 2 = (3 * ρ ^ 2 - 4) / 4 := by
    rw [hh, div_pow, Real.sq_sqrt hd]; norm_num
  let σ : ℂ := ⟨-ρ / 2, h⟩
  have hquad : σ ^ 2 + (ρ : ℂ) * σ + ((ρ : ℂ) ^ 2 - 1) = 0 := by
    apply Complex.ext
    · simp [σ, pow_two]
      nlinarith [hh2]
    · simp [σ, pow_two]
      ring
  refine ⟨σ, ?_, ?_⟩
  · have hρC : (ρ : ℂ) ^ 3 = ρ + 1 := by exact_mod_cast hρ
    linear_combination (σ - ρ) * hquad + hρC
  · rw [Complex.normSq_apply]
    simp only [σ]
    nlinarith [hh2]

/-! ### The main theorem -/

/-- **Multiplicative independence.** For the real root `ρ` of `x³ − x − 1` and
a non-real root `w` of `x⁴ − x − 1`, no positive power of `normSq w = ‖w‖²`
equals a power of `ρ`. -/
theorem normSq_pow_ne_rho_pow {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) {w : ℂ}
    (hw : w ^ 4 = w + 1) (hwim : w.im ≠ 0) (k n : ℕ) (hn : n ≠ 0) :
    normSq w ^ n ≠ ρ ^ k := by
  intro hEq
  -- the quartic's root structure
  obtain ⟨Q, Q', hQ, hQ', hQa, hQb, hQ'a, hQ'b⟩ := quartic_two_real_roots
  have hne : Q ≠ Q' := by intro h; linarith
  have hQpos : 0 < Q := by linarith
  have hPt := quartic_const hQ hQ' hne
  have hwt : normSq w = Q ^ 2 + Q * Q' + Q' ^ 2 :=
    (quartic_root_normSq hQ hQ' hne hQpos hw).2 hwim
  -- the conjugate root of the cubic
  obtain ⟨σ, hσ, hσn⟩ := exists_cubic_conj_root hρ
  -- the field `ℚ(ρ, w, w̄)` and an embedding sending `ρ` to `σ`
  have hwc : (starRingEnd ℂ) w ^ 4 = (starRingEnd ℂ) w + 1 := by
    have h := congrArg (starRingEnd ℂ) hw
    simpa [map_add, map_pow, map_one] using h
  have hρC : (ρ : ℂ) ^ 3 = ρ + 1 := by exact_mod_cast hρ
  let S : Set ℂ := {(ρ : ℂ), w, (starRingEnd ℂ) w}
  have hint3 : ∀ x : ℂ, x ^ 3 = x + 1 → IsIntegral ℚ x := fun x hx =>
    ⟨X ^ 3 - X - 1, by monicity!, by
      simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]
      linear_combination hx⟩
  have hint4 : ∀ x : ℂ, x ^ 4 = x + 1 → IsIntegral ℚ x := fun x hx =>
    ⟨X ^ 4 - X - 1, by monicity!, by
      simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]
      linear_combination hx⟩
  have hK : ∀ s ∈ S, IsIntegral ℚ s ∧ ((minpoly ℚ s).map (algebraMap ℚ ℂ)).Splits := by
    intro s hs
    refine ⟨?_, IsAlgClosed.splits _⟩
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact hint3 _ hρC
    · exact hint4 _ hw
    · exact hint4 _ hwc
  have hmin : minpoly ℚ (ρ : ℂ) = X ^ 3 - X - 1 := by
    refine (minpoly.eq_of_irreducible_of_monic cubicQ_irreducible ?_ (by monicity!)).symm
    simp only [map_sub, map_pow, aeval_X, map_one]
    linear_combination hρC
  have hy : aeval σ (minpoly ℚ (ρ : ℂ)) = 0 := by
    rw [hmin]
    simp only [map_sub, map_pow, aeval_X, map_one]
    linear_combination hσ
  have hxρ : (ρ : ℂ) ∈ IntermediateField.adjoin ℚ S :=
    IntermediateField.subset_adjoin ℚ S (by simp [S])
  have hxw : w ∈ IntermediateField.adjoin ℚ S :=
    IntermediateField.subset_adjoin ℚ S (by simp [S])
  have hxw' : (starRingEnd ℂ) w ∈ IntermediateField.adjoin ℚ S :=
    IntermediateField.subset_adjoin ℚ S (by simp [S])
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_adjoin_of_splits_of_aeval hK hxρ hy
  let R : IntermediateField.adjoin ℚ S := ⟨(ρ : ℂ), hxρ⟩
  let W : IntermediateField.adjoin ℚ S := ⟨w, hxw⟩
  let W' : IntermediateField.adjoin ℚ S := ⟨(starRingEnd ℂ) w, hxw'⟩
  -- the relation inside `ℚ(ρ, w, w̄)`
  have hEqC : (w * (starRingEnd ℂ) w) ^ n = (ρ : ℂ) ^ k := by
    rw [Complex.mul_conj]
    exact_mod_cast hEq
  have hEqE : (W * W') ^ n = R ^ k := by
    apply Subtype.ext
    simpa [W, W', R] using hEqC
  have hWE : W ^ 4 = W + 1 := by
    apply Subtype.ext
    simpa [W] using hw
  have hW'E : W' ^ 4 = W' + 1 := by
    apply Subtype.ext
    simpa [W'] using hwc
  -- apply the embedding
  have hφEq : (φ W * φ W') ^ n = σ ^ k := by
    have hR : φ R = σ := hφ
    have h := congrArg φ hEqE
    rw [map_pow, map_mul, map_pow, hR] at h
    exact h
  have ha : (φ W) ^ 4 = φ W + 1 := by
    have h := congrArg φ hWE
    simpa [map_pow, map_add, map_one] using h
  have hb : (φ W') ^ 4 = φ W' + 1 := by
    have h := congrArg φ hW'E
    simpa [map_pow, map_add, map_one] using h
  -- take `normSq`
  have hnorm : (normSq (φ W) * normSq (φ W') * normSq w) ^ n = 1 := by
    have h1 := congrArg normSq hφEq
    simp only [map_pow, map_mul] at h1
    rw [mul_pow, h1, hEq, ← mul_pow, mul_comm, hσn, one_pow]
  have hnorm1 : normSq (φ W) * normSq (φ W') * normSq w = 1 :=
    (pow_eq_one_iff_of_nonneg
      (mul_nonneg (mul_nonneg (normSq_nonneg _) (normSq_nonneg _)) (normSq_nonneg _)) hn).mp hnorm
  rw [hwt] at hnorm1
  exact norm_products_ne_one hQa hQb hQ'a hQ'b hPt
    (quartic_root_normSq hQ hQ' hne hQpos ha).1
    (quartic_root_normSq hQ hQ' hne hQpos hb).1 hnorm1

/-- **The distinguished slope is irrational.** For the real root `ρ` of
`x³ − x − 1` and a non-real root `w` of `x⁴ − x − 1`, the slope
`β = log ‖w‖ / (½ log ρ)` is irrational. -/
theorem beta_irrational {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) {w : ℂ} (hw : w ^ 4 = w + 1)
    (hwim : w.im ≠ 0) : Irrational (Real.log ‖w‖ / ((1 / 2) * Real.log ρ)) := by
  have hρ1 : 1 < ρ := one_lt_root hρ
  have hρ0 : 0 < ρ := by linarith
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ1
  have hw1 : 1 < ‖w‖ := quartic_conj_norm_gt_one w hw hwim
  have hw0 : 0 < ‖w‖ := by linarith
  rintro ⟨r, hr⟩
  have hden : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  -- `2 · den · log ‖w‖ = num · log ρ`
  have h1 : Real.log ‖w‖ = (r : ℝ) * ((1 / 2) * Real.log ρ) := by
    rw [hr]; field_simp
  have h2 : (2 * r.den : ℝ) * Real.log ‖w‖ = r.num * Real.log ρ := by
    rw [h1, Rat.cast_def]
    field_simp
  -- exponentiate: `‖w‖ ^ (2 · den) = ρ ^ num`
  have h3 : ‖w‖ ^ (2 * r.den) = ρ ^ r.num := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity))
      (Set.mem_Ioi.mpr (zpow_pos hρ0 _))
    rw [Real.log_pow, Real.log_zpow]
    push_cast
    linarith [h2]
  -- the exponent `num` is positive
  have hnum : 0 < r.num := by
    by_contra hle
    push Not at hle
    have hle1 : ρ ^ r.num ≤ 1 := zpow_le_one_of_nonpos₀ hρ1.le hle
    have hgt : 1 < ‖w‖ ^ (2 * r.den) := one_lt_pow₀ hw1 (by positivity)
    linarith
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hnum.le
  rw [hk, zpow_natCast, pow_mul, ← Complex.normSq_eq_norm_sq] at h3
  exact normSq_pow_ne_rho_pow hρ hw hwim k r.den r.den_nz h3

end Time

/-! ### Axiom audit -/

#print axioms Time.normSq_pow_ne_rho_pow
#print axioms Time.beta_irrational
