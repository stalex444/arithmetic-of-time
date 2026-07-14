import Mathlib

namespace Time

open Polynomial

/-- The cubic x³ - x - 1 over ℤ. -/
noncomputable def cubicZ : ℤ[X] := X ^ 3 - X - 1

/-- The quartic x⁴ - x - 1 over ℤ. -/
noncomputable def quarticZ : ℤ[X] := X ^ 4 - X - 1

lemma cubicZ_monic : (cubicZ).Monic := by
  unfold cubicZ
  monicity!

lemma quarticZ_monic : (quarticZ).Monic := by
  unfold quarticZ
  monicity!

/-- The image of cubicZ under ℤ → ZMod 2. -/
lemma cubicZ_map2 : cubicZ.map (Int.castRingHom (ZMod 2)) = X ^ 3 + X + 1 := by
  unfold cubicZ
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  have h2 : (2 : (ZMod 2)[X]) = 0 := by
    have e : (2 : ZMod 2) = 0 := by decide
    calc (2 : (ZMod 2)[X]) = C (2 : ZMod 2) := (C_ofNat 2).symm
      _ = C (0 : ZMod 2) := by rw [e]
      _ = 0 := by simp
  linear_combination (-(X : (ZMod 2)[X]) - 1) * h2

/-- x³ + x + 1 is irreducible over 𝔽₂ (it has no root in 𝔽₂). -/
lemma cubic_irred_zmod2 : Irreducible (X ^ 3 + X + 1 : (ZMod 2)[X]) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · -- natDegree ∈ [1,3]
    have hd : (X ^ 3 + X + 1 : (ZMod 2)[X]).natDegree = 3 := by compute_degree!
    rw [Finset.mem_Icc, hd]
    omega
  · -- no root
    intro x
    rw [IsRoot.def]
    simp only [eval_add, eval_pow, eval_X, eval_one]
    fin_cases x <;> decide

/-- x³ - x - 1 is irreducible over ℤ. -/
lemma cubicZ_irred : Irreducible cubicZ := by
  apply cubicZ_monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2))
  rw [cubicZ_map2]
  exact cubic_irred_zmod2

/-- x³ - x - 1 is irreducible over ℚ. -/
theorem cubicQ_irreducible :
    Irreducible (X ^ 3 - X - 1 : ℚ[X]) := by
  have h := (cubicZ_monic.irreducible_iff_irreducible_map_fraction_map
    (K := ℚ)).mp cubicZ_irred
  have hmap : cubicZ.map (algebraMap ℤ ℚ) = (X ^ 3 - X - 1 : ℚ[X]) := by
    unfold cubicZ
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  rwa [hmap] at h

/-! ### The quartic x⁴ - x - 1 -/

/-- The image of quarticZ under ℤ → ZMod 2 is x⁴ + x + 1. -/
lemma quarticZ_map2 : quarticZ.map (Int.castRingHom (ZMod 2)) = X ^ 4 + X + 1 := by
  unfold quarticZ
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  have h2 : (2 : (ZMod 2)[X]) = 0 := by
    have e : (2 : ZMod 2) = 0 := by decide
    calc (2 : (ZMod 2)[X]) = C (2 : ZMod 2) := (C_ofNat 2).symm
      _ = C (0 : ZMod 2) := by rw [e]
      _ = 0 := by simp
  linear_combination (-(X : (ZMod 2)[X]) - 1) * h2

/-- x⁴ + x + 1 has no root in 𝔽₂. -/
lemma quartic_no_root_zmod2 (x : ZMod 2) : ¬ (X ^ 4 + X + 1 : (ZMod 2)[X]).IsRoot x := by
  rw [IsRoot.def]
  simp only [eval_add, eval_pow, eval_X, eval_one]
  fin_cases x <;> decide

/-- The unique irreducible quadratic X²+X+1 over 𝔽₂ is irreducible. -/
lemma quad_irred_zmod2 : Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
  have hm : (X ^ 2 + X + 1 : (ZMod 2)[X]).Monic := by monicity!
  have hnd : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
  by_contra h
  rw [hm.not_irreducible_iff_exists_add_mul_eq_coeff hnd] at h
  obtain ⟨c₁, c₂, hmul, hadd⟩ := h
  have hc0 : (X ^ 2 + X + 1 : (ZMod 2)[X]).coeff 0 = 1 := by
    simp [coeff_add, coeff_X_pow, coeff_X, coeff_one]
  have hc1 : (X ^ 2 + X + 1 : (ZMod 2)[X]).coeff 1 = 1 := by
    simp [coeff_add, coeff_X_pow, coeff_X, coeff_one]
  rw [hc0] at hmul
  rw [hc1] at hadd
  revert hmul hadd
  fin_cases c₁ <;> fin_cases c₂ <;> decide

/-- A monic degree-2 polynomial over 𝔽₂ with no root equals X²+X+1. -/
lemma monic_deg2_no_root_eq (q : (ZMod 2)[X]) (hm : q.Monic) (hnd : q.natDegree = 2)
    (hr : ∀ x, ¬ q.IsRoot x) : q = X ^ 2 + X + 1 := by
  have hform : q = C (q.coeff 0) + C (q.coeff 1) * X + C (q.coeff 2) * X ^ 2 := by
    have h3 : q.natDegree < 3 := by omega
    have h := q.as_sum_range_C_mul_X_pow' h3
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at h
    conv_lhs => rw [h]
    ring
  have hc2 : q.coeff 2 = 1 := by
    have := hm.coeff_natDegree
    rwa [hnd] at this
  -- evaluate roots at 0 and 1
  have h0 := hr 0
  have h1 := hr 1
  rw [IsRoot.def, hform] at h0 h1
  simp only [eval_add, eval_mul, eval_C, eval_X, hc2,
    mul_zero, mul_one, pow_two, add_zero] at h0 h1
  -- h0: ¬ (q.coeff 0 = 0); h1: ¬ (q.coeff 0 + q.coeff 1 + 1 = 0)
  have hcoeff0 : q.coeff 0 = 1 := by
    revert h0; generalize q.coeff 0 = a; clear hform; revert a; decide
  have hcoeff1 : q.coeff 1 = 1 := by
    rw [hcoeff0] at h1
    revert h1; generalize q.coeff 1 = b; clear hform; revert b; decide
  rw [hform, hc2, hcoeff0, hcoeff1, C_1]
  ring

/-- x⁴ + x + 1 is irreducible over 𝔽₂. -/
lemma quartic_irred_zmod2 : Irreducible (X ^ 4 + X + 1 : (ZMod 2)[X]) := by
  set p : (ZMod 2)[X] := X ^ 4 + X + 1 with hp
  have hm : p.Monic := by rw [hp]; monicity!
  have hnd : p.natDegree = 4 := by rw [hp]; compute_degree!
  have hp1 : p ≠ 1 := by
    intro h; rw [h, natDegree_one] at hnd; exact absurd hnd (by norm_num)
  rw [hm.irreducible_iff_lt_natDegree_lt hp1]
  -- natDegree p / 2 = 2
  rw [hnd]
  intro q hqm hq hdvd
  rw [Finset.mem_Ioc] at hq
  obtain ⟨hq0, hq2⟩ := hq
  -- Case on natDegree q (1 or 2)
  interval_cases hqd : q.natDegree
  · -- natDegree q = 1
    have heq : q = X + C (q.coeff 0) := hqm.eq_X_add_C hqd
    obtain ⟨r, hr⟩ := hdvd
    set a := q.coeff 0 with ha
    -- p has root -a
    have : p.IsRoot (-a) := by
      rw [IsRoot.def, hr, eval_mul, heq]
      simp only [eval_add, eval_X, eval_C, neg_add_cancel, zero_mul]
    rw [hp] at this
    exact quartic_no_root_zmod2 _ this
  · -- natDegree q = 2
    obtain ⟨r, hr⟩ := hdvd
    have hrm : r.Monic := hqm.of_mul_monic_left (hr ▸ hm)
    have hrnd : r.natDegree = 2 := by
      have hdeg : q.natDegree + r.natDegree = 4 := by
        rw [← hqm.natDegree_mul hrm, ← hr, hnd]
      omega
    -- q has no root (else linear factor of p gives root of p)
    have hqnoroot : ∀ x, ¬ q.IsRoot x := by
      intro x hx
      have : p.IsRoot x := by
        rw [hr, IsRoot.def, eval_mul]
        rw [IsRoot.def] at hx; rw [hx, zero_mul]
      rw [hp] at this; exact quartic_no_root_zmod2 _ this
    have hrnoroot : ∀ x, ¬ r.IsRoot x := by
      intro x hx
      have : p.IsRoot x := by
        rw [hr, IsRoot.def, eval_mul]
        rw [IsRoot.def] at hx; rw [hx, mul_zero]
      rw [hp] at this; exact quartic_no_root_zmod2 _ this
    -- so q = r = X²+X+1, p = (X²+X+1)², contradiction
    have hqeq : q = X ^ 2 + X + 1 := monic_deg2_no_root_eq q hqm hqd hqnoroot
    have hreq : r = X ^ 2 + X + 1 := monic_deg2_no_root_eq r hrm hrnd hrnoroot
    rw [hqeq, hreq, hp] at hr
    -- product over 𝔽₂: (X²+X+1)² = X⁴+X²+1
    have hprod : (X ^ 2 + X + 1 : (ZMod 2)[X]) * (X ^ 2 + X + 1) = X ^ 4 + X ^ 2 + 1 := by
      have h2 : (2 : (ZMod 2)[X]) = 0 := by
        have e : (2 : ZMod 2) = 0 := by decide
        calc (2 : (ZMod 2)[X]) = C (2 : ZMod 2) := (C_ofNat 2).symm
          _ = C (0 : ZMod 2) := by rw [e]
          _ = 0 := by simp
      linear_combination (X ^ 3 + X ^ 2 + X) * h2
    rw [hprod] at hr
    -- compare coeff 1: LHS = 1, RHS = 0
    have hc := congrArg (fun t => Polynomial.coeff t 1) hr
    simp only [coeff_add, coeff_X_pow, coeff_X, coeff_one] at hc
    exact absurd hc (by decide)

/-- x⁴ - x - 1 is irreducible over ℤ. -/
lemma quarticZ_irred : Irreducible quarticZ := by
  apply quarticZ_monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2))
  rw [quarticZ_map2]
  exact quartic_irred_zmod2

/-- x⁴ - x - 1 is irreducible over ℚ. -/
theorem quarticQ_irreducible :
    Irreducible (X ^ 4 - X - 1 : ℚ[X]) := by
  have h := (quarticZ_monic.irreducible_iff_irreducible_map_fraction_map
    (K := ℚ)).mp quarticZ_irred
  have hmap : quarticZ.map (algebraMap ℤ ℚ) = (X ^ 4 - X - 1 : ℚ[X]) := by
    unfold quarticZ
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  rwa [hmap] at h

end Time
