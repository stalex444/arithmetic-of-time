import Mathlib
import Irreducibility

/-!
# SettlingReplica — an independent second formalization of `Settling`

An independent, from-scratch re-derivation of the `Settling` results: the same
statements, but with independently chosen proof routes (e.g. the norm-form
factorization is certified against a triangular Cauchy-module system rather than
by a computer-algebra `linear_combination` multiplier). It lives in its own
namespace `TimeReplica`, so both developments build side by side.

`K = ℚ(ρ)`, ρ the real root of `x³ − x − 1` (the smallest Pisot number, a.k.a.
the plastic number). Signature (1,1): one real embedding σ₁ (ρ ↦ r) and one
conjugate pair σ₂, σ̄₂ (ρ ↦ z, z̄ with z non-real). Model (informal motivation):
a discrete step of dynamics is multiplication by ρ; on the transverse plane σ₂
this is multiplication by z; the "record lattice" is σ₂(ℤ[ρ]), and a state
"settles" onto a lattice point when it enters a ball around it of radius below
half the windowed separation.

## Formalization choices (all faithful, none weakening)

* The roots are hypothetical: any `r : ℝ` with `r³ = r + 1` and any `z : ℂ` with
  `z³ = z + 1`, `z.im ≠ 0`. This is *more* general than fixing numerical roots;
  every theorem holds in particular for the actual `(ρ, σ₂(ρ))`.
* Elements of `ℤ[ρ]` are integer coordinate triples `v : ℤ × ℤ × ℤ` in the power
  basis `(1, ρ, ρ²)`; the embeddings are `emb1 r v = v.1 + v.2.1·r + v.2.2·r²`
  (σ₁) and `emb2 z v = v.1 + v.2.1·z + v.2.2·z²` (σ₂). The coordinates are proven
  faithful, not assumed: `emb1`/`emb2` vanish only at `0` (`emb1_ne_zero`,
  `emb2_ne_zero`), via the irreducibility of `x³ − x − 1` over ℚ (imported from
  `Irreducibility`).
* Multiplication by ρ on coordinates is the explicit integer map
  `tick (a,b,c) = (c, a+c, b)` (from `ρ·(a+bρ+cρ²) = c + (a+c)ρ + bρ²`); its
  σ₂-equivariance `emb2 z (tick v) = z · emb2 z v` is proven (`emb2_tick`), so
  `tick^[n]` *is* multiplication by ρⁿ. `untick` realizes ρ⁻¹ = ρ² − 1 (ρ is a
  unit), giving lattice invariance.
* `H^(−1/2)` is `Real.rpow`; internally it is converted to `(Real.sqrt H)⁻¹`,
  equal for `H > 0` (`rpow_neg_half`).
* T3(c) `certification_soundness` is stated WINDOWED, exactly per the model: the
  permanence of the nearest-point reading is claimed only against competitors ℓ'
  with `|σ₁(ℓ') − σ₁(ρⁿℓ)| ≤ H`. No unwindowed claim is made (the unwindowed
  transverse projection is dense).

## Main results

* `tick_contraction` (T1): `r · ‖z‖² = 1` — each tick contracts the transverse
  plane by exactly ρ^(−1/2).
* `one_lt_root`, `transverse_contraction`: `1 < r` and `‖z‖ < 1`.
* `meyer_separation` / `meyer_separation_rpow` (T2): for `v ≠ 0`,
  `1 ≤ |σ₁ v| · ‖σ₂ v‖²`, i.e. `‖σ₂ v‖ ≥ |σ₁ v|^(−1/2)`.
* `lattice_invariance` (T3a): `z · σ₂(ℤ[ρ]) = σ₂(ℤ[ρ])`.
* `windowed_uniform_discreteness` (T3b): distinct lattice points whose
  σ₁-difference is bounded by `H` have transverse separation `≥ H^(−1/2)`.
* `certification_soundness` (T3c): a reading certified to within
  `(1/2)·H^(−1/2)` never changes: for every `n`, the true image `zⁿ·σ₂(ℓ)` beats
  every windowed competitor strictly.
-/

open Polynomial

namespace TimeReplica

noncomputable section

/-! ## Elementary algebra of the three roots of x³ = x + 1 -/

/-- Two distinct roots of `x³ − x − 1` satisfy the pair relation
    `u² + uv + v² = 1`. -/
lemma root_pair {u v : ℂ} (hu : u ^ 3 = u + 1) (hv : v ^ 3 = v + 1) (huv : u ≠ v) :
    u ^ 2 + u * v + v ^ 2 = 1 := by
  have h : (u - v) * (u ^ 2 + u * v + v ^ 2 - 1) = 0 := by linear_combination hu - hv
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd (sub_eq_zero.mp h') huv
  · linear_combination h'

/-- Three distinct roots of `x³ − x − 1` sum to zero (Vieta, e₁ = 0). -/
lemma roots_sum {u v t : ℂ} (hu : u ^ 3 = u + 1) (hv : v ^ 3 = v + 1)
    (ht : t ^ 3 = t + 1) (huv : u ≠ v) (hut : u ≠ t) (hvt : v ≠ t) :
    u + v + t = 0 := by
  have hab := root_pair hu hv huv
  have hac := root_pair hu ht hut
  have h : (v - t) * (u + v + t) = 0 := by linear_combination hab - hac
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd (sub_eq_zero.mp h') hvt
  · linear_combination h'

/-- Three distinct roots of `x³ − x − 1` have product 1 (Vieta, e₃ = 1). -/
lemma roots_prod {u v t : ℂ} (hu : u ^ 3 = u + 1) (hv : v ^ 3 = v + 1)
    (ht : t ^ 3 = t + 1) (huv : u ≠ v) (hut : u ≠ t) (hvt : v ≠ t) :
    u * v * t = 1 := by
  have hab := root_pair hu hv huv
  have hsum := roots_sum hu hv ht huv hut hvt
  linear_combination (u * v) * hsum - ((u + v) / 2) * hab
    + (1 / 2 : ℂ) * hu + (1 / 2 : ℂ) * hv

/-- The conjugate of a root is a root. -/
lemma conj_root {z : ℂ} (hz : z ^ 3 = z + 1) :
    (starRingEnd ℂ) z ^ 3 = (starRingEnd ℂ) z + 1 := by
  have := congrArg (starRingEnd ℂ) hz
  simpa using this

/-- A real number is not a non-real complex number. -/
lemma real_ne_nonreal {r : ℝ} {z : ℂ} (him : z.im ≠ 0) : (r : ℂ) ≠ z := by
  intro h
  have h' := congrArg Complex.im h
  rw [Complex.ofReal_im] at h'
  exact him h'.symm

/-- A non-real complex number differs from its conjugate. -/
lemma nonreal_ne_conj {z : ℂ} (him : z.im ≠ 0) : z ≠ (starRingEnd ℂ) z := by
  intro h
  have h' := congrArg Complex.im h
  rw [Complex.conj_im] at h'
  exact him (by linarith)

/-- Vieta bundle for the root triple `(r, z, z̄)`: sum zero, the (z, z̄) pair
    relation, and product one. -/
lemma vieta_rzw (r : ℝ) (z : ℂ) (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) :
    (r : ℂ) + z + (starRingEnd ℂ) z = 0 ∧
    z ^ 2 + z * (starRingEnd ℂ) z + ((starRingEnd ℂ) z) ^ 2 = 1 ∧
    (r : ℂ) * z * (starRingEnd ℂ) z = 1 := by
  have hrc : (r : ℂ) ^ 3 = (r : ℂ) + 1 := by exact_mod_cast congrArg Complex.ofReal hr
  have hw : (starRingEnd ℂ) z ^ 3 = (starRingEnd ℂ) z + 1 := conj_root hz
  have hrz : (r : ℂ) ≠ z := real_ne_nonreal him
  have hrw : (r : ℂ) ≠ (starRingEnd ℂ) z := by
    intro h
    have h' := congrArg Complex.im h
    rw [Complex.ofReal_im, Complex.conj_im] at h'
    exact him (by linarith)
  have hzw : z ≠ (starRingEnd ℂ) z := nonreal_ne_conj him
  exact ⟨roots_sum hrc hz hw hrz hrw hzw, root_pair hz hw hzw,
    roots_prod hrc hz hw hrz hrw hzw⟩

/-! ## T1 — exact contraction rate: one tick contracts by exactly ρ^(−1/2) -/

/-- **T1 (exact contraction rate).** If `r` is the real root and `z` a non-real
    root of `x³ − x − 1`, then `r · ‖z‖² = 1`: multiplication by `z` contracts
    the transverse plane by exactly `ρ^(−1/2)` per tick. -/
theorem tick_contraction (r : ℝ) (z : ℂ) (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) : r * ‖z‖ ^ 2 = 1 := by
  obtain ⟨-, -, hprod⟩ := vieta_rzw r z hr hz him
  have hzw : z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [mul_assoc, hzw] at hprod
  exact_mod_cast hprod

/-- Any real root of `x³ − x − 1` exceeds 1 (so ρ is expanding on σ₁). -/
theorem one_lt_root {r : ℝ} (hr : r ^ 3 = r + 1) : 1 < r := by
  by_contra h
  rw [not_lt] at h
  have key : (1 - r) * (r + 1) ^ 2 + r ^ 2 = 0 := by linear_combination -hr
  have h1 : 0 ≤ (1 - r) * (r + 1) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : r ^ 2 = 0 := by linarith [sq_nonneg r]
  have h3 : r = 0 := sq_eq_zero_iff.mp h2
  rw [h3] at hr
  norm_num at hr

/-- The transverse multiplier is a strict contraction: `‖z‖ < 1`. -/
theorem transverse_contraction (r : ℝ) (z : ℂ) (hr : r ^ 3 = r + 1)
    (hz : z ^ 3 = z + 1) (him : z.im ≠ 0) : ‖z‖ < 1 := by
  have h1 := tick_contraction r z hr hz him
  have h2 := one_lt_root hr
  have hr0 : r ≠ 0 := by intro h; rw [h] at h2; norm_num at h2
  have hB2 : ‖z‖ ^ 2 = r⁻¹ := by
    field_simp
    linear_combination h1
  have hB2lt : ‖z‖ ^ 2 < 1 := by
    rw [hB2]
    exact inv_lt_one_of_one_lt₀ h2
  nlinarith [norm_nonneg z, hB2lt, sq_nonneg (‖z‖ - 1)]

/-! ## Coordinates on ℤ[ρ] and the two embeddings -/

/-- σ₁: the real embedding, on integer coordinate triples in the power basis
    `(1, ρ, ρ²)`. -/
def emb1 (r : ℝ) (v : ℤ × ℤ × ℤ) : ℝ := v.1 + v.2.1 * r + v.2.2 * r ^ 2

/-- σ₂: the complex embedding, on integer coordinate triples in the power basis
    `(1, ρ, ρ²)`. -/
def emb2 (z : ℂ) (v : ℤ × ℤ × ℤ) : ℂ := v.1 + v.2.1 * z + v.2.2 * z ^ 2

/-- One tick: multiplication by ρ on ℤ[ρ]-coordinates, `(a,b,c) ↦ (c, a+c, b)`. -/
def tick (v : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (v.2.2, v.1 + v.2.2, v.2.1)

/-- Inverse tick: multiplication by ρ⁻¹ = ρ² − 1 on ℤ[ρ]-coordinates. -/
def untick (v : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (v.2.1 - v.1, v.2.2, v.1)

lemma tick_untick (v : ℤ × ℤ × ℤ) : tick (untick v) = v := by
  obtain ⟨a, b, c⟩ := v
  simp [tick, untick]

lemma emb1_sub (r : ℝ) (u v : ℤ × ℤ × ℤ) :
    emb1 r (u - v) = emb1 r u - emb1 r v := by
  unfold emb1
  simp only [Prod.fst_sub, Prod.snd_sub]
  push_cast
  ring

lemma emb2_sub (z : ℂ) (u v : ℤ × ℤ × ℤ) :
    emb2 z (u - v) = emb2 z u - emb2 z v := by
  unfold emb2
  simp only [Prod.fst_sub, Prod.snd_sub]
  push_cast
  ring

/-- σ₁-equivariance of the tick map: `σ₁(ρ·x) = r·σ₁(x)`. -/
lemma emb1_tick {r : ℝ} (hr : r ^ 3 = r + 1) (v : ℤ × ℤ × ℤ) :
    emb1 r (tick v) = r * emb1 r v := by
  unfold emb1 tick
  push_cast
  linear_combination (-(v.2.2 : ℝ)) * hr

/-- σ₂-equivariance of the tick map: `σ₂(ρ·x) = z·σ₂(x)`. -/
lemma emb2_tick {z : ℂ} (hz : z ^ 3 = z + 1) (v : ℤ × ℤ × ℤ) :
    emb2 z (tick v) = z * emb2 z v := by
  unfold emb2 tick
  push_cast
  linear_combination (-(v.2.2 : ℂ)) * hz

/-- `tick^[n]` is multiplication by ρⁿ on σ₁. -/
lemma emb1_tick_iter {r : ℝ} (hr : r ^ 3 = r + 1) (v : ℤ × ℤ × ℤ) (n : ℕ) :
    emb1 r (tick^[n] v) = r ^ n * emb1 r v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', emb1_tick hr, ih, pow_succ]
    ring

/-- `tick^[n]` is multiplication by ρⁿ on σ₂. -/
lemma emb2_tick_iter {z : ℂ} (hz : z ^ 3 = z + 1) (v : ℤ × ℤ × ℤ) (n : ℕ) :
    emb2 z (tick^[n] v) = z ^ n * emb2 z v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', emb2_tick hz, ih, pow_succ]
    ring

/-! ## Faithfulness of the coordinates (degree-3 linear independence) -/

/-- `{1, α, α²}` is ℚ-linearly independent for any root α of `x³ − x − 1`
    (irreducibility over ℚ, imported from `Irreducibility`). -/
lemma coords_eq_zero {α : ℂ} (hα : α ^ 3 = α + 1) {a b c : ℚ}
    (h : (a : ℂ) + (b : ℂ) * α + (c : ℂ) * α ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hroot : (aeval α) (X ^ 3 - X - 1 : ℚ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_one]
    linear_combination hα
  have hmin : minpoly ℚ α = X ^ 3 - X - 1 :=
    (minpoly.eq_of_irreducible_of_monic Time.cubicQ_irreducible hroot (by monicity!)).symm
  set g : ℚ[X] := C c * X ^ 2 + C b * X + C a with hg
  have hgroot : (aeval α) g = 0 := by
    rw [hg]
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, eq_ratCast]
    linear_combination h
  have hg0 : g = 0 := by
    by_contra hne
    have hdvd : minpoly ℚ α ∣ g := minpoly.dvd ℚ α hgroot
    have hdeg := Polynomial.natDegree_le_of_dvd hdvd hne
    have hd3 : (X ^ 3 - X - 1 : ℚ[X]).natDegree = 3 := by compute_degree!
    rw [hmin, hd3] at hdeg
    have hd2 : g.natDegree ≤ 2 := by rw [hg]; compute_degree
    omega
  rw [hg] at hg0
  have h0 := congrArg (fun p => Polynomial.coeff p 0) hg0
  have h1 := congrArg (fun p => Polynomial.coeff p 1) hg0
  have h2 := congrArg (fun p => Polynomial.coeff p 2) hg0
  simp at h0 h1 h2
  exact ⟨h0, h1, h2⟩

/-- σ₁ is injective on coordinates: `emb1 r v = 0` forces `v = 0`. -/
lemma emb1_ne_zero {r : ℝ} (hr : r ^ 3 = r + 1) {v : ℤ × ℤ × ℤ} (hv : v ≠ 0) :
    emb1 r v ≠ 0 := by
  intro h
  have hrc : (r : ℂ) ^ 3 = (r : ℂ) + 1 := by exact_mod_cast congrArg Complex.ofReal hr
  have hC : ((v.1 : ℚ) : ℂ) + ((v.2.1 : ℚ) : ℂ) * (r : ℂ)
      + ((v.2.2 : ℚ) : ℂ) * (r : ℂ) ^ 2 = 0 := by
    have h' := congrArg Complex.ofReal h
    unfold emb1 at h'
    push_cast at h' ⊢
    linear_combination h'
  obtain ⟨h1, h2, h3⟩ := coords_eq_zero hrc hC
  have e1 : v.1 = 0 := by exact_mod_cast h1
  have e2 : v.2.1 = 0 := by exact_mod_cast h2
  have e3 : v.2.2 = 0 := by exact_mod_cast h3
  apply hv
  simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
  exact ⟨e1, e2, e3⟩

/-- σ₂ is injective on coordinates: `emb2 z v = 0` forces `v = 0`. -/
lemma emb2_ne_zero {z : ℂ} (hz : z ^ 3 = z + 1) {v : ℤ × ℤ × ℤ} (hv : v ≠ 0) :
    emb2 z v ≠ 0 := by
  intro h
  have hC : ((v.1 : ℚ) : ℂ) + ((v.2.1 : ℚ) : ℂ) * z
      + ((v.2.2 : ℚ) : ℂ) * z ^ 2 = 0 := by
    unfold emb2 at h
    push_cast at h ⊢
    linear_combination h
  obtain ⟨h1, h2, h3⟩ := coords_eq_zero hz hC
  have e1 : v.1 = 0 := by exact_mod_cast h1
  have e2 : v.2.1 = 0 := by exact_mod_cast h2
  have e3 : v.2.2 = 0 := by exact_mod_cast h3
  apply hv
  simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
  exact ⟨e1, e2, e3⟩

/-! ## T2 — the Meyer separation inequality -/

/-- The field norm `N(a + bρ + cρ²)` of ℤ[ρ] as an explicit integer form
    (determinant of the multiplication matrix in the power basis). -/
def normForm (v : ℤ × ℤ × ℤ) : ℤ :=
  v.1 ^ 3 + v.2.1 ^ 3 + v.2.2 ^ 3 + 2 * v.1 ^ 2 * v.2.2 + v.1 * v.2.2 ^ 2
    - v.1 * v.2.1 ^ 2 - v.2.1 * v.2.2 ^ 2 - 3 * v.1 * v.2.1 * v.2.2

/-- Product of the quadratic evaluations over a root triple with e₁ = 0, the
    (v,t)-pair relation, and t a root, equals the norm form. Certificate computed
    by Gröbner reduction against the triangular Cauchy-module system
    `{u+v+t, v²+vt+t²−1, t³−t−1}`. -/
lemma prod_root_quadratics (u v t A B C : ℂ) (h1 : u + v + t = 0)
    (h2 : v ^ 2 + v * t + t ^ 2 = 1) (h3 : t ^ 3 = t + 1) :
    (A + B * u + C * u ^ 2) * (A + B * v + C * v ^ 2) * (A + B * t + C * t ^ 2)
      = A ^ 3 + B ^ 3 + C ^ 3 + 2 * A ^ 2 * C + A * C ^ 2 - A * B ^ 2
        - B * C ^ 2 - 3 * A * B * C := by
  linear_combination
    (A^2*B - A^2*C*t + A^2*C*u - A^2*C*v + A*B^2*t + A*B^2*v + A*B*C*t*u
      - 2*A*B*C*t*v + A*B*C*u*v - A*C^2*t^3 + A*C^2*t^2*u - A*C^2*t^2*v
      - A*C^2*t*v^2 + A*C^2*u*v^2 - A*C^2*v^3 + B^3*t*v + B^2*C*t*u*v
      - B*C^2*t^3*v + B*C^2*t^2*u*v - B*C^2*t^2*v^2 + B*C^2*t*u*v^2
      - B*C^2*t*v^3 - C^3*t^3*v^2 + C^3*t^2*u*v^2 - C^3*t^2*v^3) * h1
    + (2*A^2*C - A*B^2 + 3*A*B*C*t + A*C^2*t^2 + A*C^2*t*v + A*C^2*v^2 + A*C^2
      - B^3*t + B*C^2*t^2*v + B*C^2*t*v^2 + B*C^2*t - C^3*t^4 + C^3*t^3*v
      + C^3*t^2*v^2 + C^3*t^2) * h2
    + (-3*A*B*C + B^3 - B*C^2 + C^3*t^3 - C^3*t + C^3) * h3

/-- The arithmetic identity behind T2: `σ₁(x)·‖σ₂(x)‖² = N(x)`, the product of
    `x` over all three embeddings, as real numbers. -/
lemma emb_prod_eq_normForm (r : ℝ) (z : ℂ) (hr : r ^ 3 = r + 1)
    (hz : z ^ 3 = z + 1) (him : z.im ≠ 0) (v : ℤ × ℤ × ℤ) :
    emb1 r v * ‖emb2 z v‖ ^ 2 = (normForm v : ℝ) := by
  obtain ⟨hsum, hpair, -⟩ := vieta_rzw r z hr hz him
  have hw : (starRingEnd ℂ) z ^ 3 = (starRingEnd ℂ) z + 1 := conj_root hz
  have key := prod_root_quadratics (r : ℂ) z ((starRingEnd ℂ) z)
    (v.1 : ℂ) (v.2.1 : ℂ) (v.2.2 : ℂ) hsum hpair hw
  have hfac1 : ((emb1 r v : ℝ) : ℂ)
      = (v.1 : ℂ) + (v.2.1 : ℂ) * (r : ℂ) + (v.2.2 : ℂ) * (r : ℂ) ^ 2 := by
    unfold emb1
    push_cast
    ring
  have hfac2 : emb2 z v = (v.1 : ℂ) + (v.2.1 : ℂ) * z + (v.2.2 : ℂ) * z ^ 2 := rfl
  have hfac3 : (starRingEnd ℂ) (emb2 z v)
      = (v.1 : ℂ) + (v.2.1 : ℂ) * ((starRingEnd ℂ) z)
        + (v.2.2 : ℂ) * ((starRingEnd ℂ) z) ^ 2 := by
    unfold emb2
    simp only [map_add, map_mul, map_pow, map_intCast]
  have hns : emb2 z v * (starRingEnd ℂ) (emb2 z v) = ((‖emb2 z v‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hRHS : ((normForm v : ℤ) : ℂ)
      = (v.1 : ℂ) ^ 3 + (v.2.1 : ℂ) ^ 3 + (v.2.2 : ℂ) ^ 3
        + 2 * (v.1 : ℂ) ^ 2 * (v.2.2 : ℂ) + (v.1 : ℂ) * (v.2.2 : ℂ) ^ 2
        - (v.1 : ℂ) * (v.2.1 : ℂ) ^ 2 - (v.2.1 : ℂ) * (v.2.2 : ℂ) ^ 2
        - 3 * (v.1 : ℂ) * (v.2.1 : ℂ) * (v.2.2 : ℂ) := by
    unfold normForm
    push_cast
    ring
  have hC : ((emb1 r v : ℝ) : ℂ) * ((‖emb2 z v‖ ^ 2 : ℝ) : ℂ)
      = ((normForm v : ℤ) : ℂ) := by
    calc ((emb1 r v : ℝ) : ℂ) * ((‖emb2 z v‖ ^ 2 : ℝ) : ℂ)
        = ((emb1 r v : ℝ) : ℂ) * (emb2 z v * (starRingEnd ℂ) (emb2 z v)) := by
          rw [hns]
      _ = ((v.1 : ℂ) + (v.2.1 : ℂ) * (r : ℂ) + (v.2.2 : ℂ) * (r : ℂ) ^ 2)
            * ((v.1 : ℂ) + (v.2.1 : ℂ) * z + (v.2.2 : ℂ) * z ^ 2)
            * ((v.1 : ℂ) + (v.2.1 : ℂ) * ((starRingEnd ℂ) z)
              + (v.2.2 : ℂ) * ((starRingEnd ℂ) z) ^ 2) := by
          rw [hfac1, hfac3, hfac2]
          ring
      _ = (v.1 : ℂ) ^ 3 + (v.2.1 : ℂ) ^ 3 + (v.2.2 : ℂ) ^ 3
            + 2 * (v.1 : ℂ) ^ 2 * (v.2.2 : ℂ) + (v.1 : ℂ) * (v.2.2 : ℂ) ^ 2
            - (v.1 : ℂ) * (v.2.1 : ℂ) ^ 2 - (v.2.1 : ℂ) * (v.2.2 : ℂ) ^ 2
            - 3 * (v.1 : ℂ) * (v.2.1 : ℂ) * (v.2.2 : ℂ) := key
      _ = ((normForm v : ℤ) : ℂ) := hRHS.symm
  exact_mod_cast hC

/-- **T2 (Meyer separation, product form).** For every nonzero `x ∈ ℤ[ρ]`:
    `1 ≤ |σ₁(x)| · ‖σ₂(x)‖²`. The norm `N(x) = σ₁(x)·‖σ₂(x)‖²` is a nonzero
    rational integer, hence at least 1 in absolute value. -/
theorem meyer_separation (r : ℝ) (z : ℂ) (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) (v : ℤ × ℤ × ℤ) (hv : v ≠ 0) :
    1 ≤ |emb1 r v| * ‖emb2 z v‖ ^ 2 := by
  have hid := emb_prod_eq_normForm r z hr hz him v
  have hnf : normForm v ≠ 0 := by
    intro h0
    rw [h0] at hid
    norm_num at hid
    rcases hid with h | h
    · exact emb1_ne_zero hr hv h
    · exact emb2_ne_zero hz hv h
  have h1 : (1 : ℝ) ≤ |(normForm v : ℝ)| := by
    have := Int.one_le_abs hnf
    exact_mod_cast this
  calc (1 : ℝ) ≤ |(normForm v : ℝ)| := h1
    _ = |emb1 r v * ‖emb2 z v‖ ^ 2| := by rw [hid]
    _ = |emb1 r v| * ‖emb2 z v‖ ^ 2 := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg ‖emb2 z v‖)]

/-- `H^(−1/2)` (rpow) equals `(√H)⁻¹` for `H > 0`. -/
lemma rpow_neg_half {H : ℝ} (hH : 0 < H) :
    H ^ (-(1 / 2) : ℝ) = (Real.sqrt H)⁻¹ := by
  rw [Real.rpow_neg hH.le, ← Real.sqrt_eq_rpow]

/-- **T2 (Meyer separation, exponent form).** For every nonzero `x ∈ ℤ[ρ]`:
    `‖σ₂(x)‖ ≥ |σ₁(x)|^(−1/2)`. -/
theorem meyer_separation_rpow (r : ℝ) (z : ℂ) (hr : r ^ 3 = r + 1)
    (hz : z ^ 3 = z + 1) (him : z.im ≠ 0) (v : ℤ × ℤ × ℤ) (hv : v ≠ 0) :
    |emb1 r v| ^ (-(1 / 2) : ℝ) ≤ ‖emb2 z v‖ := by
  have hpos : 0 < |emb1 r v| := abs_pos.mpr (emb1_ne_zero hr hv)
  rw [rpow_neg_half hpos]
  have hm := meyer_separation r z hr hz him v hv
  have hinv : |emb1 r v|⁻¹ ≤ ‖emb2 z v‖ ^ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    linarith [hm]
  calc (Real.sqrt |emb1 r v|)⁻¹
      = Real.sqrt |emb1 r v|⁻¹ := (Real.sqrt_inv _).symm
    _ ≤ Real.sqrt (‖emb2 z v‖ ^ 2) := Real.sqrt_le_sqrt hinv
    _ = ‖emb2 z v‖ := Real.sqrt_sq (norm_nonneg _)

/-! ## T3 — certification soundness -/

/-- The record lattice `σ₂(ℤ[ρ]) ⊆ ℂ`. -/
def recordLattice (z : ℂ) : Set ℂ := {x | ∃ v : ℤ × ℤ × ℤ, x = emb2 z v}

/-- **T3(a) (lattice invariance).** Multiplication by `z` maps the record
    lattice σ₂(ℤ[ρ]) onto itself (ρ is a unit: ρ⁻¹ = ρ² − 1 ∈ ℤ[ρ]). -/
theorem lattice_invariance {z : ℂ} (hz : z ^ 3 = z + 1) :
    (fun x => z * x) '' recordLattice z = recordLattice z := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨v, rfl⟩ := hy
    exact ⟨tick v, (emb2_tick hz v).symm⟩
  · rintro ⟨v, rfl⟩
    refine ⟨emb2 z (untick v), ⟨untick v, rfl⟩, ?_⟩
    show z * emb2 z (untick v) = emb2 z v
    rw [← emb2_tick hz (untick v), tick_untick]

/-- **T3(b) (windowed uniform discreteness).** Distinct points of ℤ[ρ] whose
    σ₁-images differ by at most `H` have σ₂-images at least `H^(−1/2)` apart.
    Corollary of T2: the certification radius is uniformly positive on any
    window of bounded Perron coordinate. -/
theorem windowed_uniform_discreteness (r : ℝ) (z : ℂ) (hr : r ^ 3 = r + 1)
    (hz : z ^ 3 = z + 1) (him : z.im ≠ 0) (u v : ℤ × ℤ × ℤ) (huv : u ≠ v)
    {H : ℝ} (hH : 0 < H) (hwin : |emb1 r u - emb1 r v| ≤ H) :
    H ^ (-(1 / 2) : ℝ) ≤ ‖emb2 z u - emb2 z v‖ := by
  rw [rpow_neg_half hH]
  have hd : u - v ≠ 0 := sub_ne_zero.mpr huv
  have hm := meyer_separation r z hr hz him (u - v) hd
  rw [emb1_sub, emb2_sub] at hm
  have hB : (0 : ℝ) ≤ ‖emb2 z u - emb2 z v‖ := norm_nonneg _
  have hH2 : H⁻¹ ≤ ‖emb2 z u - emb2 z v‖ ^ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hH]
    have habs : |emb1 r u - emb1 r v| * ‖emb2 z u - emb2 z v‖ ^ 2
        ≤ H * ‖emb2 z u - emb2 z v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hwin (sq_nonneg _)
    linarith [hm, habs]
  calc (Real.sqrt H)⁻¹ = Real.sqrt H⁻¹ := (Real.sqrt_inv _).symm
    _ ≤ Real.sqrt (‖emb2 z u - emb2 z v‖ ^ 2) := Real.sqrt_le_sqrt hH2
    _ = ‖emb2 z u - emb2 z v‖ := Real.sqrt_sq hB

/-- **T3(c) (certification soundness — one tick = one settling).** If a
    transverse reading `w` is certified to a lattice point `ℓ` within radius
    `(1/2)·H^(−1/2)`, then at every later tick `n` the evolved reading `zⁿ·w`
    is strictly closer to the true evolved lattice point `σ₂(ρⁿℓ)` (realized as
    `emb2 z (tick^[n] ℓ)`) than to ANY other lattice point ℓ' in the σ₁-window
    `|σ₁(ℓ') − σ₁(ρⁿℓ)| ≤ H`: the windowed nearest-point reading never changes.
    The window hypothesis is essential and stated explicitly — no unwindowed
    permanence is claimed. -/
theorem certification_soundness (r : ℝ) (z : ℂ) (hr : r ^ 3 = r + 1)
    (hz : z ^ 3 = z + 1) (him : z.im ≠ 0) (w : ℂ) (ℓ : ℤ × ℤ × ℤ) {H : ℝ}
    (hH : 0 < H) (hcert : ‖w - emb2 z ℓ‖ < H ^ (-(1 / 2) : ℝ) / 2)
    (n : ℕ) (ℓ' : ℤ × ℤ × ℤ) (hne : ℓ' ≠ tick^[n] ℓ)
    (hwin : |emb1 r ℓ' - emb1 r (tick^[n] ℓ)| ≤ H) :
    ‖z ^ n * w - emb2 z (tick^[n] ℓ)‖ < ‖z ^ n * w - emb2 z ℓ'‖ := by
  rw [rpow_neg_half hH] at hcert
  have hz1 : ‖z‖ < 1 := transverse_contraction r z hr hz him
  have hzn : ‖z‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg z) hz1.le
  have hequiv : z ^ n * w - emb2 z (tick^[n] ℓ) = z ^ n * (w - emb2 z ℓ) := by
    rw [emb2_tick_iter hz]
    ring
  have htrue : ‖z ^ n * w - emb2 z (tick^[n] ℓ)‖ < (Real.sqrt H)⁻¹ / 2 := by
    rw [hequiv, norm_mul, norm_pow]
    calc ‖z‖ ^ n * ‖w - emb2 z ℓ‖ ≤ 1 * ‖w - emb2 z ℓ‖ :=
          mul_le_mul_of_nonneg_right hzn (norm_nonneg _)
      _ = ‖w - emb2 z ℓ‖ := one_mul _
      _ < (Real.sqrt H)⁻¹ / 2 := hcert
  have hsep : (Real.sqrt H)⁻¹ ≤ ‖emb2 z ℓ' - emb2 z (tick^[n] ℓ)‖ := by
    have h := windowed_uniform_discreteness r z hr hz him ℓ' (tick^[n] ℓ) hne hH hwin
    rwa [rpow_neg_half hH] at h
  have htri : ‖emb2 z ℓ' - emb2 z (tick^[n] ℓ)‖
      ≤ ‖z ^ n * w - emb2 z (tick^[n] ℓ)‖ + ‖z ^ n * w - emb2 z ℓ'‖ := by
    have hrw : emb2 z ℓ' - emb2 z (tick^[n] ℓ)
        = (z ^ n * w - emb2 z (tick^[n] ℓ)) - (z ^ n * w - emb2 z ℓ') := by
      ring
    rw [hrw]
    exact norm_sub_le _ _
  linarith

end

end TimeReplica
