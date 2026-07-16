import Mathlib

/-!
# The Pisot boundary: the cubic settles, the quartic spirals

For the two polynomials `x³ − x − 1` (root ρ, the plastic number) and
`x⁴ − x − 1` (root Q), this file proves the **dichotomy at the unit circle**
directly from the polynomials, with no free parameters:

* the non-real conjugate pair of the **cubic** `x³ − x − 1` has modulus `< 1`
  (`cubic_conj_norm_lt_one`) — it CONTRACTS, so ρ is a Pisot number and its
  arithmetic SETTLES;
* the non-real conjugate pair of the **quartic** `x⁴ − x − 1` has modulus `> 1`
  (`quartic_conj_norm_gt_one`) — it EXPANDS, so Q is NOT a Pisot number and its
  arithmetic SPIRALS.

Packaged as `pisot_boundary_dichotomy`: the two roots sit on opposite sides of
the unit circle — one settling arithmetic, one spiraling — forced by the degree
alone.

The method is elementary and self-contained. For a non-real root `w` write
`σ = w + conj w` and `s = w · conj w = ‖w‖²`, both real, with `s > 0`. The pair
`{w, conj w}` satisfies the Vieta quadratic `w² = σ·w − s`. Reducing the
defining equation modulo this quadratic and matching the (real) coefficients of
the ℝ-linearly-independent `{1, w}` yields two real identities in `σ, s`; a
short `nlinarith` extracts the modulus bound. No Pisot theory, no root-finding,
no `Polynomial` API.
-/

namespace Time

noncomputable section
open Complex

/-- **The quartic spirals.** Every non-real root `w` of `x⁴ − x − 1` has
`‖w‖ > 1`: the transverse mode of `Q` EXPANDS, so `Q` is not a Pisot number. -/
theorem quartic_conj_norm_gt_one (w : ℂ) (hw : w ^ 4 = w + 1) (him : w.im ≠ 0) :
    1 < ‖w‖ := by
  have hw0 : w ≠ 0 := by intro h; apply him; rw [h]; simp
  have hc : (starRingEnd ℂ) w ^ 4 = (starRingEnd ℂ) w + 1 := by
    have h := congrArg (starRingEnd ℂ) hw
    simpa [map_add, map_pow, map_one] using h
  set σ : ℝ := 2 * w.re with hσ
  set s : ℝ := normSq w with hs
  have hspos : 0 < s := by rw [hs]; exact normSq_pos.mpr hw0
  have hsum : w + (starRingEnd ℂ) w = (σ : ℂ) := by rw [add_conj, hσ]
  have hprod : w * (starRingEnd ℂ) w = (s : ℂ) := by rw [mul_conj, hs]
  have hquad : w ^ 2 = (σ : ℂ) * w - (s : ℂ) := by rw [← hsum, ← hprod]; ring
  -- reduce w⁴ modulo the quadratic (substitution, no guessed multiplier)
  have hred : w ^ 4 = ((σ:ℂ)^3 - 2*(s:ℂ)*(σ:ℂ)) * w + ((s:ℂ)^2 - (σ:ℂ)^2*(s:ℂ)) := by
    calc w ^ 4 = (w ^ 2) ^ 2 := by ring
      _ = ((σ:ℂ) * w - (s:ℂ)) ^ 2 := by rw [hquad]
      _ = (σ:ℂ)^2 * w^2 - 2*(σ:ℂ)*(s:ℂ)*w + (s:ℂ)^2 := by ring
      _ = (σ:ℂ)^2 * ((σ:ℂ) * w - (s:ℂ)) - 2*(σ:ℂ)*(s:ℂ)*w + (s:ℂ)^2 := by rw [hquad]
      _ = ((σ:ℂ)^3 - 2*(s:ℂ)*(σ:ℂ)) * w + ((s:ℂ)^2 - (σ:ℂ)^2*(s:ℂ)) := by ring
  have hAB : ((σ:ℂ)^3 - 2*(s:ℂ)*(σ:ℂ) - 1) * w + ((s:ℂ)^2 - (σ:ℂ)^2*(s:ℂ) - 1) = 0 := by
    linear_combination hw - hred
  have hABc : ((σ:ℂ)^3 - 2*(s:ℂ)*(σ:ℂ) - 1) * (starRingEnd ℂ) w
      + ((s:ℂ)^2 - (σ:ℂ)^2*(s:ℂ) - 1) = 0 := by
    have h := congrArg (starRingEnd ℂ) hAB
    simpa [map_add, map_mul, map_sub, map_pow, map_one, map_ofNat, Complex.conj_ofReal] using h
  have hne : w - (starRingEnd ℂ) w ≠ 0 := by
    rw [sub_ne_zero]; intro h; exact him (Complex.conj_eq_iff_im.mp h.symm)
  have hA : (σ:ℂ)^3 - 2*(s:ℂ)*(σ:ℂ) - 1 = 0 := by
    have hfac : ((σ:ℂ)^3 - 2*(s:ℂ)*(σ:ℂ) - 1) * (w - (starRingEnd ℂ) w) = 0 := by
      linear_combination hAB - hABc
    rcases mul_eq_zero.mp hfac with h | h
    · exact h
    · exact absurd h hne
  have hB : (s:ℂ)^2 - (σ:ℂ)^2*(s:ℂ) - 1 = 0 := by linear_combination hAB - w * hA
  have hEqA : σ^3 - 2*s*σ - 1 = 0 := by exact_mod_cast hA
  have hEqB : s^2 - σ^2*s - 1 = 0 := by exact_mod_cast hB
  have hσne : σ ≠ 0 := by intro h; rw [h] at hEqA; norm_num at hEqA
  have hσ2 : 0 < σ^2 := by positivity
  have hs2 : 1 < s^2 := by nlinarith [mul_pos hσ2 hspos, hEqB]
  have hs1 : 1 < s := by nlinarith [hs2, hspos]
  have hnorm : ‖w‖ ^ 2 = s := by rw [hs]; exact (Complex.normSq_eq_norm_sq w).symm
  nlinarith [norm_nonneg w, hs1, hnorm, sq_nonneg (‖w‖ - 1)]

/-- **The cubic settles.** Every non-real root `z` of `x³ − x − 1` has `‖z‖ < 1`:
the transverse mode of `ρ` CONTRACTS, so `ρ` is a Pisot number. -/
theorem cubic_conj_norm_lt_one (z : ℂ) (hz : z ^ 3 = z + 1) (him : z.im ≠ 0) :
    ‖z‖ < 1 := by
  have hz0 : z ≠ 0 := by intro h; apply him; rw [h]; simp
  have hc : (starRingEnd ℂ) z ^ 3 = (starRingEnd ℂ) z + 1 := by
    have h := congrArg (starRingEnd ℂ) hz
    simpa [map_add, map_pow, map_one] using h
  set σ : ℝ := 2 * z.re with hσ
  set s : ℝ := normSq z with hs
  have hspos : 0 < s := by rw [hs]; exact normSq_pos.mpr hz0
  have hsum : z + (starRingEnd ℂ) z = (σ : ℂ) := by rw [add_conj, hσ]
  have hprod : z * (starRingEnd ℂ) z = (s : ℂ) := by rw [mul_conj, hs]
  have hquad : z ^ 2 = (σ : ℂ) * z - (s : ℂ) := by rw [← hsum, ← hprod]; ring
  have hred : z ^ 3 = ((σ:ℂ)^2 - (s:ℂ)) * z - (σ:ℂ)*(s:ℂ) := by
    calc z ^ 3 = z * z ^ 2 := by ring
      _ = z * ((σ:ℂ) * z - (s:ℂ)) := by rw [hquad]
      _ = (σ:ℂ) * z^2 - (s:ℂ)*z := by ring
      _ = (σ:ℂ) * ((σ:ℂ) * z - (s:ℂ)) - (s:ℂ)*z := by rw [hquad]
      _ = ((σ:ℂ)^2 - (s:ℂ)) * z - (σ:ℂ)*(s:ℂ) := by ring
  have hAB : ((σ:ℂ)^2 - (s:ℂ) - 1) * z + (-(σ:ℂ)*(s:ℂ) - 1) = 0 := by
    linear_combination hz - hred
  have hABc : ((σ:ℂ)^2 - (s:ℂ) - 1) * (starRingEnd ℂ) z + (-(σ:ℂ)*(s:ℂ) - 1) = 0 := by
    have h := congrArg (starRingEnd ℂ) hAB
    simpa [map_add, map_mul, map_sub, map_neg, map_pow, map_one, map_ofNat,
      Complex.conj_ofReal] using h
  have hne : z - (starRingEnd ℂ) z ≠ 0 := by
    rw [sub_ne_zero]; intro h; exact him (Complex.conj_eq_iff_im.mp h.symm)
  have hA : (σ:ℂ)^2 - (s:ℂ) - 1 = 0 := by
    have hfac : ((σ:ℂ)^2 - (s:ℂ) - 1) * (z - (starRingEnd ℂ) z) = 0 := by
      linear_combination hAB - hABc
    rcases mul_eq_zero.mp hfac with h | h
    · exact h
    · exact absurd h hne
  have hB : -(σ:ℂ)*(s:ℂ) - 1 = 0 := by linear_combination hAB - z * hA
  have hEqA : σ^2 - s - 1 = 0 := by exact_mod_cast hA
  have hEqB : -σ*s - 1 = 0 := by exact_mod_cast hB
  have hcubic : s^3 + s^2 - 1 = 0 := by linear_combination (-σ*s + 1) * hEqB - s^2 * hEqA
  have hs2lt : s^2 < 1 := by nlinarith [hcubic, pow_pos hspos 3]
  have hs1 : s < 1 := by nlinarith [hs2lt, hspos]
  have hnorm : ‖z‖ ^ 2 = s := by rw [hs]; exact (Complex.normSq_eq_norm_sq z).symm
  nlinarith [norm_nonneg z, hs1, hnorm, sq_nonneg (‖z‖ - 1)]

/-- **The Pisot-boundary dichotomy — the settle/spiral fork is forced.**
From the two polynomials alone: the cubic's non-real conjugates contract
(`‖z‖ < 1`, ρ settles / is Pisot) and the quartic's expand (`‖w‖ > 1`,
Q spirals / is non-Pisot) — one flipped inequality, driven purely by the
degree. -/
theorem pisot_boundary_dichotomy
    (z : ℂ) (hz : z ^ 3 = z + 1) (hzim : z.im ≠ 0)
    (w : ℂ) (hw : w ^ 4 = w + 1) (hwim : w.im ≠ 0) :
    ‖z‖ < 1 ∧ 1 < ‖w‖ :=
  ⟨cubic_conj_norm_lt_one z hz hzim, quartic_conj_norm_gt_one w hw hwim⟩

end

end Time
