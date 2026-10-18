module
public import Mathlib

@[expose] public section
/-!
# PdtPisotBoundary — the Pisot dichotomy of the two defining polynomials (ρ Pisot, Q non-Pisot)

The two defining polynomials of PDT, `f = x³ − x − 1` (root ρ, the plastic
number) and `g = x⁴ − x − 1` (root Q), sit on
opposite sides of the unit circle `|σ| = 1` — the **Pisot boundary**. This
module kernel-verifies that dichotomy directly from the polynomials, with zero
free parameters:

* **the cubic settles** (`cubic_conj_norm_lt_one`): every non-real root `z` of
  `x³ − x − 1` has `‖z‖ < 1` — the transverse mode CONTRACTS, so ρ is a Pisot
  number and its arithmetic settles onto ℤ[ρ] (`‖z‖ = ρ^(−1/2) ≈ 0.8688`);
* **the quartic spirals** (`quartic_conj_norm_gt_one`): every non-real root `w`
  of `x⁴ − x − 1` has `‖w‖ > 1` — the transverse mode EXPANDS, so Q is NOT a
  Pisot number and its arithmetic spirals (`‖w‖ ≈ 1.0633`);
* **the dichotomy** (`pisot_boundary_dichotomy`): `‖z‖ < 1 ∧ 1 < ‖w‖` — the
  contraction/expansion split that PDT reads as its classical/quantum divide.
  The split itself is the kernel-verified content; the reading is interpretive.

This upgrades the previously-computed value `|σ_Q| = 1.0633` (a numerical fact)
to a kernel theorem. It does NOT prove Siegel minimality (ρ = the *smallest* Pisot),
which requires Pisot theory absent from Mathlib.

## Method (elementary, self-contained)

For a non-real root `w`, write `σ = w + conj w` and `s = w · conj w = ‖w‖²`,
both real, with `s > 0`. The conjugate pair `{w, conj w}` satisfies the Vieta
quadratic `w² = σ·w − s`. Reducing the defining equation modulo this quadratic
and matching the (real) coefficients of the ℝ-linearly-independent `{1, w}`
yields two real identities in `σ, s`:

* quartic: `s² − σ²·s = 1`  ⇒  `s > 1` (since `σ² ≥ 0`, `s > 0`, and `s = 1`
  would force `σ = 0`, contradicting `σ³ − 2sσ = 1`);
* cubic: `s³ + s² = 1`  ⇒  `s < 1`.

One flipped inequality, driven purely by the degree. No Pisot theory, no
root-finding, no `Polynomial` API.
-/

namespace PDT

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

/-- **The Pisot-boundary dichotomy.** From the two zero-parameter defining
polynomials: the cubic's non-real roots contract (`‖z‖ < 1`; ρ is Pisot) and
the quartic's expand (`‖w‖ > 1`; Q is not) — the two polynomials sit on
opposite sides of the unit circle. -/
theorem pisot_boundary_dichotomy
    (z : ℂ) (hz : z ^ 3 = z + 1) (hzim : z.im ≠ 0)
    (w : ℂ) (hw : w ^ 4 = w + 1) (hwim : w.im ≠ 0) :
    ‖z‖ < 1 ∧ 1 < ‖w‖ :=
  ⟨cubic_conj_norm_lt_one z hz hzim, quartic_conj_norm_gt_one w hw hwim⟩

end

end PDT

/-! ### Axiom audit -/

#print axioms PDT.quartic_conj_norm_gt_one
#print axioms PDT.cubic_conj_norm_lt_one
#print axioms PDT.pisot_boundary_dichotomy
