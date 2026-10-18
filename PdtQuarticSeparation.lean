module
public import PdtRecordBoundary

@[expose] public section

/-!
# Quartic records with both real embeddings bounded

The integer resultant supplies a norm obstruction. Bounding both real
embeddings therefore separates the complex records. These are arithmetic
windows; no identification with physical coordinates is assumed.
-/

open Polynomial
namespace PDT.QuarticSeparation
open PDT.RecordBoundary
noncomputable section

/-- Both real places are bounded, while the complex place is observed. -/
def doubleWindow (q s : ℝ) (z : ℂ) (H K : ℝ) : Set ℂ :=
  {w | ∃ p : Quad, |embed4 q p| ≤ H ∧ |embed4 s p| ≤ K ∧ embed4 z p = w}

/-- Irreducibility makes every quartic root embedding faithful on integer coordinates. -/
lemma embed4_ne_zero {K : Type*} [Field K] [Algebra ℚ K] {t : K}
    (ht : t ^ 4 = t + 1) {p : Quad} (hp : p ≠ 0) : embed4 t p ≠ 0 := by
  obtain ⟨a, b, c, d⟩ := p
  have htroot : aeval t (X ^ 4 - X - 1 : ℚ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_one]
    linear_combination ht
  have hmonic : (X ^ 4 - X - 1 : ℚ[X]).Monic := by monicity!
  have hmin : minpoly ℚ t = X ^ 4 - X - 1 :=
    (minpoly.eq_of_irreducible_of_monic PDT.quarticQ_irreducible htroot hmonic).symm
  intro h0
  let f : ℚ[X] := C (a : ℚ) + C (b : ℚ) * X + C (c : ℚ) * X ^ 2 + C (d : ℚ) * X ^ 3
  have hfroot : aeval t f = 0 := by
    simpa [f, embed4] using h0
  have hfne : f ≠ 0 := by
    intro hf
    apply hp
    have ha : a = 0 := by
      have h := congrArg (fun g : ℚ[X] => g.coeff 0) hf
      simp only [f, coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow, coeff_zero] at h
      norm_num at h
      exact h
    have hb : b = 0 := by
      have h := congrArg (fun g : ℚ[X] => g.coeff 1) hf
      simp only [f, coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow, coeff_zero] at h
      norm_num at h
      exact h
    have hc : c = 0 := by
      have h := congrArg (fun g : ℚ[X] => g.coeff 2) hf
      simp only [f, coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow, coeff_zero] at h
      norm_num at h
      exact h
    have hd : d = 0 := by
      have h := congrArg (fun g : ℚ[X] => g.coeff 3) hf
      simp only [f, coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow, coeff_zero] at h
      norm_num at h
      exact h
    subst a b c d
    rfl
  have hle := Polynomial.natDegree_le_natDegree
    (minpoly.degree_le_of_ne_zero ℚ t hfne hfroot)
  have hdeg : (minpoly ℚ t).natDegree = 4 := by rw [hmin]; compute_degree!
  have hfdeg : f.natDegree ≤ 3 := by dsimp [f]; compute_degree!
  omega

lemma embed4_sub {K : Type*} [CommRing K] (t : K) (p p' : Quad) :
    embed4 t (p - p') = embed4 t p - embed4 t p' := by
  simp only [embed4, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
  ring

lemma embed4_conj (z : ℂ) (p : Quad) :
    embed4 (starRingEnd ℂ z) p = starRingEnd ℂ (embed4 z p) := by
  simp [embed4]

lemma embed4_ofReal (t : ℝ) (p : Quad) : embed4 (t : ℂ) p = ((embed4 t p : ℝ) : ℂ) := by
  simp only [embed4, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_intCast]

/-- The four root places, in a fixed order. -/
def rootPlaces (q s : ℝ) (z : ℂ) : Fin 4 → ℂ := ![(q : ℂ), (s : ℂ), z, starRingEnd ℂ z]

lemma rootPlaces_injective {q s : ℝ} {z : ℂ} (hqs : q ≠ s) (him : z.im ≠ 0) :
    Function.Injective (rootPlaces q s z) := by
  have hqz : (q : ℂ) ≠ z := by intro h; apply him; rw [← h]; rfl
  have hsz : (s : ℂ) ≠ z := by intro h; apply him; rw [← h]; rfl
  have hqzc : (q : ℂ) ≠ starRingEnd ℂ z := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.ofReal_im, Complex.conj_im] at hi
    exact him (by linarith)
  have hszc : (s : ℂ) ≠ starRingEnd ℂ z := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.ofReal_im, Complex.conj_im] at hi
    exact him (by linarith)
  have hzc : z ≠ starRingEnd ℂ z := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.conj_im] at hi
    exact him (by linarith)
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [rootPlaces]

lemma quartic_factorization {q s : ℝ} {z : ℂ}
    (hq : q ^ 4 = q + 1) (hs : s ^ 4 = s + 1) (hqs : q ≠ s)
    (hz : z ^ 4 = z + 1) (him : z.im ≠ 0) :
    (X ^ 4 - X - 1 : ℂ[X]) = ∏ i : Fin 4, (X - C (rootPlaces q s z i)) := by
  have hr : ∀ i, (rootPlaces q s z i) ^ 4 = rootPlaces q s z i + 1 := by
    intro i
    fin_cases i
    · simpa [rootPlaces] using (show (q : ℂ) ^ 4 = (q : ℂ) + 1 by exact_mod_cast hq)
    · simpa [rootPlaces] using (show (s : ℂ) ^ 4 = (s : ℂ) + 1 by exact_mod_cast hs)
    · simpa [rootPlaces] using hz
    · simpa [rootPlaces] using congrArg (starRingEnd ℂ) hz
  apply eq_of_monic_of_dvd_of_natDegree_le
    (monic_prod_X_sub_C (rootPlaces q s z) Finset.univ) (by monicity!)
  · apply Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C (rootPlaces_injective hqs him))
    intro i
    apply dvd_iff_isRoot.mpr
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_one]
    linear_combination hr i
  · rw [natDegree_finsetProd_X_sub_C_eq_card]
    norm_num
    compute_degree!

/-- Integer power-basis polynomial. -/
def coordinatePolynomial (p : Quad) : ℤ[X] :=
  C p.1 + C p.2.1 * X + C p.2.2.1 * X ^ 2 + C p.2.2.2 * X ^ 3

/-- An integer norm, defined as the resultant with the monic quartic. -/
def normForm (p : Quad) : ℤ :=
  resultant (X ^ 4 - X - 1) (coordinatePolynomial p) 4 3

lemma coordinatePolynomial_eval (p : Quad) (z : ℂ) :
    ((coordinatePolynomial p).map (Int.castRingHom ℂ)).eval z = embed4 z p := by
  simp [coordinatePolynomial, embed4]

/-- Exact norm factorization through all four embeddings. -/
lemma normForm_factor {q s : ℝ} {z : ℂ}
    (hq : q ^ 4 = q + 1) (hs : s ^ 4 = s + 1) (hqs : q ≠ s)
    (hz : z ^ 4 = z + 1) (him : z.im ≠ 0) (p : Quad) :
    (normForm p : ℂ) = ((embed4 q p : ℝ) : ℂ) * ((embed4 s p : ℝ) : ℂ) *
      embed4 z p * starRingEnd ℂ (embed4 z p) := by
  let g := (coordinatePolynomial p).map (Int.castRingHom ℂ)
  have hg : g.natDegree ≤ 3 := by dsimp [g, coordinatePolynomial]; simp only [Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_pow, map_C, map_X]; compute_degree!
  have hdeg : (∏ i : Fin 4, (X - C (rootPlaces q s z i))).natDegree = 4 := by
    rw [← quartic_factorization hq hs hqs hz him]
    compute_degree!
  have hmap := resultant_map_map (X ^ 4 - X - 1 : ℤ[X]) (coordinatePolynomial p) 4 3
    (Int.castRingHom ℂ)
  have hprod := resultant_prod_left Finset.univ (fun i : Fin 4 => X - C (rootPlaces q s z i))
    g 3 (by simp) hg
  rw [hdeg] at hprod
  simp only [natDegree_X_sub_C, resultant_X_sub_C_left _ _ _ hg] at hprod
  calc
    (normForm p : ℂ) = resultant (X ^ 4 - X - 1) g 4 3 := by
      change (Int.castRingHom ℂ) (resultant (X ^ 4 - X - 1 : ℤ[X]) (coordinatePolynomial p) 4 3) = _
      rw [← hmap]
      congr 1
      simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one]
    _ = ∏ i : Fin 4, g.eval (rootPlaces q s z i) := by
      rw [quartic_factorization hq hs hqs hz him]; exact hprod
    _ = _ := by
      simp only [Fin.prod_univ_four, g, coordinatePolynomial_eval]
      change embed4 (q : ℂ) p * embed4 (s : ℂ) p * embed4 z p *
        embed4 (starRingEnd ℂ z) p = _
      rw [embed4_conj, embed4_ofReal, embed4_ofReal]


lemma normForm_eq_mul_norm_sq {q s : ℝ} {z : ℂ}
    (hq : q ^ 4 = q + 1) (hs : s ^ 4 = s + 1) (hqs : q ≠ s)
    (hz : z ^ 4 = z + 1) (him : z.im ≠ 0) (p : Quad) :
    (normForm p : ℝ) = embed4 q p * embed4 s p * ‖embed4 z p‖ ^ 2 := by
  have h := normForm_factor hq hs hqs hz him p
  rw [mul_assoc, Complex.mul_conj] at h
  norm_cast at h
  simpa [Complex.normSq_eq_norm_sq, mul_assoc] using h

/-- The nonzero integer norm has absolute value at least one. -/
theorem norm_product_ge_one {q s : ℝ} {z : ℂ}
    (hq : q ^ 4 = q + 1) (hs : s ^ 4 = s + 1) (hqs : q ≠ s)
    (hz : z ^ 4 = z + 1) (him : z.im ≠ 0) (p : Quad) (hp : p ≠ 0) :
    1 ≤ |embed4 q p| * |embed4 s p| * ‖embed4 z p‖ ^ 2 := by
  have hfac := normForm_eq_mul_norm_sq hq hs hqs hz him p
  have hN : normForm p ≠ 0 := by
    intro hn
    have hnon := mul_ne_zero (mul_ne_zero (embed4_ne_zero hq hp) (embed4_ne_zero hs hp))
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr (embed4_ne_zero hz hp)))
    apply hnon
    rw [← hfac, hn, Int.cast_zero]
  have hN1 : (1 : ℝ) ≤ |(normForm p : ℝ)| := by
    exact_mod_cast Int.one_le_abs hN
  simpa only [hfac, abs_mul, abs_pow, abs_norm] using hN1

/-- Bounding the two real sizes bounds how close a nonzero complex record can be to zero. -/
theorem bounded_separation {q s : ℝ} {z : ℂ}
    (hq : q ^ 4 = q + 1) (hs : s ^ 4 = s + 1) (hqs : q ≠ s)
    (hz : z ^ 4 = z + 1) (him : z.im ≠ 0)
    {H K : ℝ} (hH : 0 < H) (hK : 0 < K) (p : Quad) (hp : p ≠ 0)
    (hpH : |embed4 q p| ≤ H) (hpK : |embed4 s p| ≤ K) :
    1 / Real.sqrt (H * K) ≤ ‖embed4 z p‖ := by
  have hprod := norm_product_ge_one hq hs hqs hz him p hp
  have hle : |embed4 q p| * |embed4 s p| ≤ H * K :=
    mul_le_mul hpH hpK (abs_nonneg _) hH.le
  have hbound : 1 ≤ (H * K) * ‖embed4 z p‖ ^ 2 :=
    hprod.trans (mul_le_mul_of_nonneg_right hle (sq_nonneg _))
  have hroot : 0 < Real.sqrt (H * K) := Real.sqrt_pos.mpr (mul_pos hH hK)
  have hsquare : 1 ≤ (Real.sqrt (H * K) * ‖embed4 z p‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_pos hH hK).le]
    exact hbound
  apply (div_le_iff₀ hroot).mpr
  nlinarith [mul_nonneg hroot.le (norm_nonneg (embed4 z p))]

/-- The explicit pair gap for a double window. Each difference doubles both bounds. -/
theorem doubleWindow_pair_gap {q s : ℝ} {z : ℂ}
    (hq : q ^ 4 = q + 1) (hs : s ^ 4 = s + 1) (hqs : q ≠ s)
    (hz : z ^ 4 = z + 1) (him : z.im ≠ 0)
    {H K : ℝ} (hH : 0 < H) (hK : 0 < K)
    {x y : ℂ} (hx : x ∈ doubleWindow q s z H K) (hy : y ∈ doubleWindow q s z H K)
    (hne : x ≠ y) : 1 / (2 * Real.sqrt (H * K)) ≤ ‖x - y‖ := by
  obtain ⟨p, hpH, hpK, rfl⟩ := hx
  obtain ⟨p', hpH', hpK', rfl⟩ := hy
  have hp : p - p' ≠ 0 := by
    intro he
    exact hne (congrArg (embed4 z) (sub_eq_zero.mp he))
  have hdH : |embed4 q (p - p')| ≤ 2 * H := by
    rw [embed4_sub]
    exact (abs_sub _ _).trans (by linarith)
  have hdK : |embed4 s (p - p')| ≤ 2 * K := by
    rw [embed4_sub]
    exact (abs_sub _ _).trans (by linarith)
  have h := bounded_separation hq hs hqs hz him (by positivity : 0 < 2 * H)
    (by positivity : 0 < 2 * K) (p - p') hp hdH hdK
  rw [embed4_sub, show (2 * H) * (2 * K) = 4 * (H * K) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at h
  norm_num at h
  convert h using 1
  ring

/-- The double window is uniformly discrete in its complex projection. -/
theorem doubleWindow_uniform_gap {q s : ℝ} {z : ℂ}
    (hq : q ^ 4 = q + 1) (hs : s ^ 4 = s + 1) (hqs : q ≠ s)
    (hz : z ^ 4 = z + 1) (him : z.im ≠ 0)
    {H K : ℝ} (hH : 0 < H) (hK : 0 < K) :
    HasUniformGap (doubleWindow q s z H K) := by
  refine ⟨1 / (2 * Real.sqrt (H * K)), by positivity, ?_⟩
  intro x hx y hy hne
  exact doubleWindow_pair_gap hq hs hqs hz him hH hK hx hy hne

/-- Taking differences doubles both real windows. -/
lemma sub_mem_doubleWindow {q s : ℝ} {z : ℂ} {H K : ℝ} {x y : ℂ}
    (hx : x ∈ doubleWindow q s z H K) (hy : y ∈ doubleWindow q s z H K) :
    x - y ∈ doubleWindow q s z (2 * H) (2 * K) := by
  obtain ⟨p, hpH, hpK, rfl⟩ := hx
  obtain ⟨p', hpH', hpK', rfl⟩ := hy
  refine ⟨p - p', ?_, ?_, embed4_sub z p p'⟩
  · rw [embed4_sub]; exact (abs_sub _ _).trans (by linarith)
  · rw [embed4_sub]; exact (abs_sub _ _).trans (by linarith)

/-- The difference set also has an explicit uniform gap. -/
theorem doubleWindow_difference_pair_gap {q s : ℝ} {z : ℂ}
    (hq : q ^ 4 = q + 1) (hs : s ^ 4 = s + 1) (hqs : q ≠ s)
    (hz : z ^ 4 = z + 1) (him : z.im ≠ 0)
    {H K : ℝ} (hH : 0 < H) (hK : 0 < K)
    {x y u v : ℂ} (hx : x ∈ doubleWindow q s z H K) (hy : y ∈ doubleWindow q s z H K)
    (hu : u ∈ doubleWindow q s z H K) (hv : v ∈ doubleWindow q s z H K)
    (hne : x - y ≠ u - v) : 1 / (4 * Real.sqrt (H * K)) ≤ ‖(x - y) - (u - v)‖ := by
  have h := doubleWindow_pair_gap hq hs hqs hz him (by positivity : 0 < 2 * H)
    (by positivity : 0 < 2 * K) (sub_mem_doubleWindow hx hy) (sub_mem_doubleWindow hu hv) hne
  rw [show (2 * H) * (2 * K) = 4 * (H * K) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at h
  norm_num at h
  convert h using 1
  ring

/-- The hypotheses of the quartic separation theorems are simultaneously realized. -/
theorem exists_root_places : ∃ q s : ℝ, ∃ z : ℂ,
    q ^ 4 = q + 1 ∧ 1 < q ∧ s ^ 4 = s + 1 ∧ -1 < s ∧ s < 0 ∧
      q ≠ s ∧ z ^ 4 = z + 1 ∧ z.im ≠ 0 := by
  have hqex : ∃ q : ℝ, q ^ 4 = q + 1 ∧ 1 < q := by
    have hc : ContinuousOn (fun y : ℝ => y ^ 4 - y - 1) (Set.Icc (6 / 5) (13 / 10)) := by
      fun_prop
    obtain ⟨q, hmem, he⟩ := intermediate_value_Icc (by norm_num : (6 / 5 : ℝ) ≤ 13 / 10) hc
      (show (0 : ℝ) ∈ Set.Icc ((6 / 5 : ℝ) ^ 4 - 6 / 5 - 1)
        ((13 / 10 : ℝ) ^ 4 - 13 / 10 - 1) by norm_num)
    exact ⟨q, by simp only at he; linarith, by linarith [hmem.1]⟩
  have hrex : ∃ r : ℝ, r ^ 3 = r + 1 := by
    have hc : ContinuousOn (fun y : ℝ => y ^ 3 - y - 1) (Set.Icc 1 2) := by fun_prop
    obtain ⟨r, _, he⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hc
      (show (0 : ℝ) ∈ Set.Icc ((1 : ℝ) ^ 3 - 1 - 1) ((2 : ℝ) ^ 3 - 2 - 1) by norm_num)
    exact ⟨r, by simp only at he; linarith⟩
  obtain ⟨q, hq, hq1⟩ := hqex
  obtain ⟨r, hr⟩ := hrex
  obtain ⟨s, hs, hslo, hshi⟩ := PDT.SalemFamily.exists_r2
  obtain ⟨z, hz, him, _, _⟩ := PDT.SalemFamily.ruler_second_conjugate hq hq1 hr
  exact ⟨q, s, z, hq, hq1, hs, by linarith, by linarith, by linarith, hz, him⟩

end
end PDT.QuarticSeparation

#print axioms PDT.QuarticSeparation.doubleWindow
#print axioms PDT.QuarticSeparation.embed4_ne_zero
#print axioms PDT.QuarticSeparation.embed4_sub
#print axioms PDT.QuarticSeparation.embed4_conj
#print axioms PDT.QuarticSeparation.rootPlaces
#print axioms PDT.QuarticSeparation.rootPlaces_injective
#print axioms PDT.QuarticSeparation.quartic_factorization
#print axioms PDT.QuarticSeparation.coordinatePolynomial
#print axioms PDT.QuarticSeparation.normForm
#print axioms PDT.QuarticSeparation.coordinatePolynomial_eval
#print axioms PDT.QuarticSeparation.normForm_factor
#print axioms PDT.QuarticSeparation.normForm_eq_mul_norm_sq

#print axioms PDT.QuarticSeparation.embed4_ofReal

#print axioms PDT.QuarticSeparation.norm_product_ge_one
#print axioms PDT.QuarticSeparation.bounded_separation
#print axioms PDT.QuarticSeparation.doubleWindow_pair_gap
#print axioms PDT.QuarticSeparation.doubleWindow_uniform_gap
#print axioms PDT.QuarticSeparation.sub_mem_doubleWindow
#print axioms PDT.QuarticSeparation.doubleWindow_difference_pair_gap
#print axioms PDT.QuarticSeparation.exists_root_places
