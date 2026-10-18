/-
PdtMahlerTheta — the exact constant: the degree-4 Mahler minimum IS the
second-smallest Pisot number.

  `mahler_fam_pisot` : M := M(x⁴−x−1) satisfies M⁴ = M³ + 1 and 1 < M —
  i.e. the minimal quartic Mahler measure is the root > 1 of x⁴−x³−1
  (θ₄, Siegel's second-smallest Pisot number).

Route: M(x⁴−x−1) = M(x⁴−x³−1) by reversal invariance (tie_revneg_eq);
x⁴−x³−1 is Pisot-shaped — its non-real roots lie strictly inside the
unit circle (the PdtPisotBoundary (σ,s)-reduction, flipped inequality),
its real roots lie in (−1,0) ∪ (69/50, 2) with the outside one unique —
so the measure equals that single outside root. Multiplicity is excluded
by the kernel-certified bracket 11/10 < M ≤ 139/100. No calculus, no
discriminants, no irreducibility.
-/
module
public import PdtMahlerMain

@[expose] public section

namespace PDT
namespace Mahler
open Polynomial Complex

noncomputable section

/-- **The conjugate pair of `x⁴−x³−1` contracts.** Every non-real root has
norm < 1 (the `PdtPisotBoundary` reduction: two real identities in
`σ = 2 Re w`, `s = ‖w‖²`, then case analysis). -/
theorem theta_conj_norm_lt_one (w : ℂ) (hw : w ^ 4 = w ^ 3 + 1)
    (him : w.im ≠ 0) : ‖w‖ < 1 := by
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; norm_num at hw
  set σ : ℝ := 2 * w.re with hσdef
  set s : ℝ := normSq w with hsdef
  have hspos : 0 < s := by rw [hsdef]; exact normSq_pos.mpr hw0
  have hsum : w + (starRingEnd ℂ) w = (σ : ℂ) := by rw [add_conj, hσdef]
  have hprod : w * (starRingEnd ℂ) w = (s : ℂ) := by rw [mul_conj, hsdef]
  have hquad : w ^ 2 = (σ : ℂ) * w - (s : ℂ) := by rw [← hsum, ← hprod]; ring
  have hred3 : w ^ 3 = ((σ:ℂ)^2 - (s:ℂ)) * w - (σ:ℂ)*(s:ℂ) := by
    calc w ^ 3 = w * w ^ 2 := by ring
      _ = w * ((σ:ℂ) * w - (s:ℂ)) := by rw [hquad]
      _ = (σ:ℂ) * w ^ 2 - (s:ℂ) * w := by ring
      _ = (σ:ℂ) * ((σ:ℂ) * w - (s:ℂ)) - (s:ℂ) * w := by rw [hquad]
      _ = ((σ:ℂ)^2 - (s:ℂ)) * w - (σ:ℂ)*(s:ℂ) := by ring
  have hred4 : w ^ 4 = ((σ:ℂ)^3 - 2*(s:ℂ)*(σ:ℂ)) * w
      + ((s:ℂ)^2 - (σ:ℂ)^2*(s:ℂ)) := by
    calc w ^ 4 = (w ^ 2) ^ 2 := by ring
      _ = ((σ:ℂ) * w - (s:ℂ)) ^ 2 := by rw [hquad]
      _ = (σ:ℂ)^2 * w^2 - 2*(σ:ℂ)*(s:ℂ)*w + (s:ℂ)^2 := by ring
      _ = (σ:ℂ)^2 * ((σ:ℂ) * w - (s:ℂ)) - 2*(σ:ℂ)*(s:ℂ)*w + (s:ℂ)^2 := by
          rw [hquad]
      _ = ((σ:ℂ)^3 - 2*(s:ℂ)*(σ:ℂ)) * w + ((s:ℂ)^2 - (σ:ℂ)^2*(s:ℂ)) := by
          ring
  -- w⁴ − w³ − 1 = 0 in the reduced basis {1, w}
  have hAB : (((σ:ℂ)^3 - 2*(s:ℂ)*(σ:ℂ)) - ((σ:ℂ)^2 - (s:ℂ))) * w
      + ((s:ℂ)^2 - (σ:ℂ)^2*(s:ℂ) + (σ:ℂ)*(s:ℂ) - 1) = 0 := by
    linear_combination hw - hred4 + hred3
  have hABc : (((σ:ℂ)^3 - 2*(s:ℂ)*(σ:ℂ)) - ((σ:ℂ)^2 - (s:ℂ)))
      * (starRingEnd ℂ) w
      + ((s:ℂ)^2 - (σ:ℂ)^2*(s:ℂ) + (σ:ℂ)*(s:ℂ) - 1) = 0 := by
    have h := congrArg (starRingEnd ℂ) hAB
    simpa [map_add, map_mul, map_sub, map_pow, map_one, map_ofNat,
      Complex.conj_ofReal] using h
  have hne : w - (starRingEnd ℂ) w ≠ 0 := by
    rw [sub_ne_zero]; intro h; exact him (Complex.conj_eq_iff_im.mp h.symm)
  have hA : ((σ:ℂ)^3 - 2*(s:ℂ)*(σ:ℂ)) - ((σ:ℂ)^2 - (s:ℂ)) = 0 := by
    have hfac : (((σ:ℂ)^3 - 2*(s:ℂ)*(σ:ℂ)) - ((σ:ℂ)^2 - (s:ℂ)))
        * (w - (starRingEnd ℂ) w) = 0 := by
      linear_combination hAB - hABc
    rcases mul_eq_zero.mp hfac with h | h
    · exact h
    · exact absurd h hne
  have hB : (s:ℂ)^2 - (σ:ℂ)^2*(s:ℂ) + (σ:ℂ)*(s:ℂ) - 1 = 0 := by
    linear_combination hAB - w * hA
  have hEqA' : σ^3 - 2*s*σ - (σ^2 - s) = 0 := by exact_mod_cast hA
  have hEqA : σ^3 - 2*s*σ - σ^2 + s = 0 := by linarith
  have hEqB : s^2 - σ^2*s + σ*s - 1 = 0 := by exact_mod_cast hB
  -- the real case analysis: s < 1
  have hs1 : s < 1 := by
    by_contra hs1
    push_neg at hs1
    -- (i) 0 < σ < 1 is impossible: σ(1−σ)s = 1 − s² ≤ 0
    have hσcase : σ ≤ 0 ∨ 1 ≤ σ := by
      by_contra hc
      push_neg at hc
      obtain ⟨h0, h1⟩ := hc
      nlinarith [mul_pos (mul_pos h0 hspos) (sub_pos.2 h1)]
    rcases hσcase with hσ0 | hσ1
    · -- σ ≤ 0: A gives s ≤ σ², B gives s > σ² − σ; hence σ > 0, absurd
      have hA' : s * (1 - 2*σ) = σ^2 * (1 - σ) := by linear_combination hEqA
      have h12 : (0:ℝ) < 1 - 2*σ := by linarith
      have hs_le : s ≤ σ^2 := by nlinarith [hA', h12, hσ0]
      have hs_gt : σ^2 - σ < s := by nlinarith [hEqB, hspos]
      linarith
    · -- 1 ≤ σ: forces σ(σ−1)² < 0, absurd
      have hA'' : s * (2*σ - 1) = σ^2 * (σ - 1) := by linear_combination -hEqA
      have h21 : (0:ℝ) < 2*σ - 1 := by linarith
      have hpos : 0 < s + σ - σ^2 := by
        by_contra hp
        push_neg at hp
        nlinarith [hEqB, mul_nonneg hspos.le (neg_nonneg.2 hp)]
      have hgt : σ^2 - σ < s := by linarith
      have hstep := mul_lt_mul_of_pos_right hgt h21
      rw [hA''] at hstep
      nlinarith [hstep, hσ1, sq_nonneg (σ - 1), hspos, hA'', h21, hs1]
  have hnorm : ‖w‖ ^ 2 = s := by rw [hsdef]; exact (Complex.normSq_eq_norm_sq w).symm
  nlinarith [norm_nonneg w, hs1, hnorm, sq_nonneg (‖w‖ - 1)]

/-- Real roots of `x⁴ = x³ + 1` lie in `(−1, 0) ∪ (69/50, 2)`. -/
lemma theta_real_root_cases (x : ℝ) (hx : x ^ 4 = x ^ 3 + 1) :
    (-1 < x ∧ x < 0) ∨ (69/50 < x ∧ x < 2) := by
  have hne0 : x ≠ 0 := by intro h; rw [h] at hx; norm_num at hx
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · left
    refine ⟨?_, hneg⟩
    by_contra hle
    push_neg at hle
    nlinarith [hx, mul_nonneg (mul_nonneg (mul_self_nonneg x) (neg_nonneg.2 hneg.le)) (neg_nonneg.2 hneg.le)]
  · exact absurd hzero hne0
  · right
    have h1 : 1 < x := by
      by_contra hle
      push_neg at hle
      nlinarith [pow_le_one₀ hpos.le hle (n := 3), hx, pow_pos hpos 3]
    constructor
    · by_contra hle
      push_neg at hle
      have h3 : x^3 ≤ (69/50)^3 := by
        nlinarith [mul_nonneg (sub_nonneg.2 hle)
          (by nlinarith : (0:ℝ) ≤ (69/50)^2 + (69/50)*x + x^2)]
      have hprod : x^3 * (x - 1) ≤ (69/50)^3 * (19/50) :=
        mul_le_mul h3 (by linarith) (by linarith) (by positivity)
      nlinarith [hx, hprod]
    · by_contra hle
      push_neg at hle
      have h8 : (8:ℝ) ≤ x^3 := by
        nlinarith [mul_nonneg (sub_nonneg.2 hle)
          (by nlinarith : (0:ℝ) ≤ x^2 + 2*x + 4)]
      have hprod : (8:ℝ) * 1 ≤ x^3 * (x - 1) :=
        mul_le_mul h8 (by linarith) (by norm_num) (by nlinarith)
      nlinarith [hx, hprod]

/-- Uniqueness of the outside real root. -/
lemma theta_real_root_unique {x y : ℝ} (hx : x ^ 4 = x ^ 3 + 1) (h1x : 1 < x)
    (hy : y ^ 4 = y ^ 3 + 1) (h1y : 1 < y) : x = y := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · nlinarith [hx, hy, mul_pos (sub_pos.2 h)
      (by nlinarith : (0:ℝ) < (y - 1) * (y^2 + y*x + x^2) + x^3)]
  · nlinarith [hx, hy, mul_pos (sub_pos.2 h)
      (by nlinarith : (0:ℝ) < (x - 1) * (x^2 + x*y + y^2) + y^3)]

/-- Kernel bracket, lower side: `11/10 < M(x⁴−x−1)`. -/
lemma fam_lower_11 :
    (11 : ℝ) / 10
      < ((zq4 (0, 0, -1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  have hs := lowerCert_sound (P := 11) (Q := 10) (by norm_num) 9 0 (0, 0, -1, -1)
  simp only [pow_zero, pow_one, Function.iterate_zero_apply] at hs
  have h' : lowerCert 9 ((11 : ℕ) : ℤ) ((10 : ℕ) : ℤ) (0, 0, -1, -1) = true := by
    exact_mod_cast (by decide : lowerCert 9 (11 : ℤ) (10 : ℤ) (0, 0, -1, -1) = true)
  exact_mod_cast hs h'

/-- Products of `max 1 ‖·‖` are at least one. -/
lemma one_le_prod_max (s : Multiset ℂ) :
    1 ≤ (s.map fun r => max 1 ‖r‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      calc (1:ℝ) = 1 * 1 := by norm_num
        _ ≤ max 1 ‖r‖ * (s.map fun r => max 1 ‖r‖).prod :=
            mul_le_mul (le_max_left _ _) ih (by norm_num)
              (le_trans (by norm_num) (le_max_left _ _))

/-- **The exact constant.** The degree-4 Mahler minimum satisfies the Pisot
quartic: `M(x⁴−x−1)⁴ = M(x⁴−x−1)³ + 1` with `M > 1` — the minimal quartic
Mahler measure IS the second-smallest Pisot number θ₄ (root of x⁴−x³−1). -/
theorem mahler_fam_pisot :
    (((zq4 (0, 0, -1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure) ^ 4
        = (((zq4 (0, 0, -1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure) ^ 3 + 1
      ∧ 1 < ((zq4 (0, 0, -1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  -- switch to the reversal partner x⁴−x³−1 = q4 (−1) 0 0 (−1)
  have hswitch : ((zq4 (0, 0, -1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure
      = (q4 (-1) 0 0 (-1)).mahlerMeasure := by
    rw [← tie_revneg_eq, map_zq4]
    push_cast
    norm_num
  set G : ℂ[X] := q4 (-1) 0 0 (-1) with hG
  have hroot_eq : ∀ r ∈ G.roots, r ^ 4 = r ^ 3 + 1 := by
    intro r hr
    have h := isRoot_of_mem_roots hr
    simp only [hG, IsRoot, q4, eval_add, eval_mul, eval_pow, eval_X, eval_C,
      map_neg, map_one, eval_neg, eval_one] at h
    linear_combination h
  -- the measure brackets, transported to G
  have hMup : G.mahlerMeasure ≤ 139/100 := by
    rw [← hswitch]
    have h := fam_upper
    exact_mod_cast h
  have hMlow : 11/10 < G.mahlerMeasure := by
    rw [← hswitch]
    exact_mod_cast fam_lower_11
  have hMform : G.mahlerMeasure = (G.roots.map fun r => max 1 ‖r‖).prod :=
    mahlerMeasure_eq_prod_roots (q4_monic _ _ _ _)
  -- a root of norm > 1 exists
  have hexists : ∃ r ∈ G.roots, 1 < ‖r‖ := by
    by_contra hall
    push_neg at hall
    have hone : ∀ r ∈ G.roots, max 1 ‖r‖ = 1 := fun r hr =>
      max_eq_left (hall r hr)
    rw [hMform, Multiset.map_congr rfl hone] at hMlow
    simp at hMlow
    linarith
  obtain ⟨rstar, hrmem, hrbig⟩ := hexists
  -- it is real, and its real part is the outside root
  have hrim : rstar.im = 0 := by
    by_contra him
    exact absurd (theta_conj_norm_lt_one rstar (hroot_eq rstar hrmem) him)
      (not_lt.mpr hrbig.le)
  have hrre : rstar = ((rstar.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hrim]
  set x : ℝ := rstar.re with hxdef
  have hxroot : x ^ 4 = x ^ 3 + 1 := by
    have h := hroot_eq rstar hrmem
    rw [hrre] at h
    exact_mod_cast h
  have hxnorm : ‖rstar‖ = |x| := by rw [hrre]; exact Complex.norm_real _
  have hxbig : 69/50 < x ∧ x < 2 := by
    rcases theta_real_root_cases x hxroot with ⟨h1, h2⟩ | h
    · exfalso
      rw [hxnorm] at hrbig
      have : |x| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
      linarith
    · exact h
  have hx1 : 1 < x := by linarith [hxbig.1]
  have hxpos : 0 < x := by linarith
  have hnormx : ‖rstar‖ = x := by rw [hxnorm, abs_of_pos hxpos]
  -- multiplicity of rstar is one: a double root would push M past 139/100
  have hcount : Multiset.count rstar G.roots = 1 := by
    have hge : 1 ≤ Multiset.count rstar G.roots :=
      Multiset.one_le_count_iff_mem.mpr hrmem
    by_contra hne
    have h2 : 2 ≤ Multiset.count rstar G.roots := by omega
    have hrep : Multiset.replicate 2 rstar ≤ G.roots :=
      Multiset.le_count_iff_replicate_le.mp h2
    obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp hrep
    have : (G.roots.map fun r => max 1 ‖r‖).prod
        = (max 1 ‖rstar‖) ^ 2 * (u.map fun r => max 1 ‖r‖).prod := by
      rw [hu, Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
        Multiset.prod_replicate]
    rw [this] at hMform
    have hsq : (max 1 ‖rstar‖) ^ 2 = x ^ 2 := by
      rw [hnormx, max_eq_right hx1.le]
    rw [hsq] at hMform
    have hx2 : (69/50 : ℝ)^2 < x ^ 2 := by nlinarith [hxbig.1]
    nlinarith [hMform, hMup, one_le_prod_max u, hx2, sq_nonneg x]
  -- every other root contributes max = 1
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
      have hroot' : r.re ^ 4 = r.re ^ 3 + 1 := by
        have h := hroot_eq r hrmem'
        rw [hre] at h
        exact_mod_cast h
      have hnr : ‖r‖ = |r.re| := by rw [hre]; exact Complex.norm_real _
      rcases theta_real_root_cases r.re hroot' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hnr]
        rw [abs_le]
        constructor <;> linarith
      · exfalso
        apply hrne
        rw [hre, hrre]
        norm_cast
        exact theta_real_root_unique hroot' (by linarith) hxroot hx1
    · exact (theta_conj_norm_lt_one r (hroot_eq r hrmem') him).le
  -- assemble: M = x
  have hMx : G.mahlerMeasure = x := by
    rw [hMform, ← Multiset.prod_map_erase (f := fun r => max 1 ‖r‖) hrmem]
    rw [Multiset.map_congr rfl herase]
    simp [hnormx, max_eq_right hx1.le]
  constructor
  · rw [hswitch, hMx]
    exact hxroot
  · rw [hswitch, hMx]
    exact hx1

end

end Mahler
end PDT
