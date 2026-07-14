import Irreducibility

/-!
# Settling — an exact contraction rate and a Meyer separation on ℤ[ρ]

`K = ℚ(ρ)`, `ρ` the real root of `f = x³ − x − 1` (signature (1,1)): one real
embedding `σ₁ : ρ ↦ r` and one conjugate pair `σ₂, σ̄₂ : ρ ↦ z, z̄` with `z`
non-real. Model (informal motivation): a discrete step of dynamics on the
transverse (complex-embedding) plane is multiplication by `σ₂(ρ) = z`; the
"record lattice" is `σ₂(ℤ[ρ])`, and a state "settles" onto a lattice point when
it enters a small ball around it. This module kernel-verifies the three
load-bearing mathematical facts:

* **T1 — exact contraction rate** (`tick_contraction`): `r·‖z‖² = 1`, i.e.
  every tick contracts the transverse plane by exactly `ρ^(−1/2)`
  (`norm_z_eq_rpow`: `‖z‖ = r^(−1/2)`).
* **T2 — Meyer separation inequality** (`meyer_separation`,
  `meyer_separation_rpow`): for every nonzero `x ∈ ℤ[ρ]` with coordinates
  `(a,b,c)`, writing `x₁ = a + b·r + c·r²` and `x₂ = a + b·z + c·z²`, the
  product `x₁·‖x₂‖²` is a nonzero rational integer (`normForm_factor`), hence
  `1 ≤ |x₁|·‖x₂‖²`, hence `‖x₂‖ ≥ |x₁|^(−1/2)`.
* **T3 — certification soundness**:
  (a) `lattice_tick_invariant`: multiplication by `z` maps `σ₂(ℤ[ρ])` onto
      itself (`ρ` is a unit, `ρ⁻¹ = ρ² − 1 ∈ ℤ[ρ]`);
  (b) `windowed_separation`: distinct lattice points whose real embeddings
      differ by at most `H` are at transverse distance `≥ H^(−1/2)`
      (uniform discreteness on any window of bounded Perron coordinate);
  (c) `certification_soundness`: if the state `w` is certified within
      `(1/2)·H^(−1/2)` of the lattice point `σ₂(ℓ)`, then after any number `n`
      of ticks the evolved state `zⁿ·w` remains strictly closer to the evolved
      committed point `zⁿ·σ₂(ℓ) = σ₂(ρⁿℓ)` than to every OTHER lattice point
      `σ₂(ℓ')` whose real embedding is within `H` of that of `ρⁿℓ` — the
      nearest-point reading within the window never changes.

## Faithfulness notes (reformulations, none weakening)

* `ℤ[ρ]` elements are represented by their coordinate triples
  `(a, b, c) : ℤ × ℤ × ℤ` in the power basis `(1, ρ, ρ²)`; the embeddings are
  `embed r` (real) and `embed z` (complex), `embed t (a,b,c) = a + b·t + c·t²`.
  "`x ≠ 0` in `ℤ[ρ]`" is `(a,b,c) ≠ 0`, and `embed_ne_zero` proves the two
  representations agree (nonzero triples embed to nonzero numbers; this uses
  irreducibility of `x³ − x − 1` over ℚ, imported from `Irreducibility`).
* The roots `r` and `z` are characterized by their defining equations
  `r³ = r + 1` (`r : ℝ`) and `z³ = z + 1, z.im ≠ 0` (`z : ℂ`) — every theorem
  quantifies over ALL such `r, z`, which is stronger than fixing particular
  roots. (The real cubic has exactly one real root and one conjugate pair, so
  these hypotheses pin the objects up to conjugation, under which every
  statement below is invariant.)
* T3(c) is stated with the explicit window hypothesis
  `|σ₁(ℓ') − σ₁(ρⁿℓ)| ≤ H`: the UNWINDOWED transverse
  projection of `ℤ[ρ]` is dense, so only the windowed/bounded-horizon
  statement is true, and that is what is proved. No unwindowed permanence is
  claimed.
* Multiplication by `n` ticks acts on coordinates by `tick^[n]` where
  `tick (a,b,c) = (c, a+c, b)` (multiplication by `ρ` in the power basis);
  `embed_tick_iter` proves `σ(ρⁿ·x) = σ(ρ)ⁿ·σ(x)` for both embeddings, so the
  committed point after `n` ticks may be written either as `zⁿ·embed z ℓ` or
  as the lattice point `embed z (tick^[n] ℓ)` — they are proved equal.
-/

open Polynomial

namespace Time

noncomputable section

/-! ## Coordinates, embeddings, the tick, and the norm form -/

/-- `embed t (a,b,c) = a + b·t + c·t²`: the image of the `ℤ[ρ]`-element with
power-basis coordinates `(a,b,c)` under the embedding sending `ρ ↦ t`. -/
def embed {K : Type*} [CommRing K] (t : K) (p : ℤ × ℤ × ℤ) : K :=
  (p.1 : K) + (p.2.1 : K) * t + (p.2.2 : K) * t ^ 2

/-- One tick on lattice coordinates: multiplication by `ρ` in the power basis
`(1, ρ, ρ²)`, using `ρ³ = ρ + 1`: `(a,b,c) ↦ (c, a+c, b)`. -/
def tick (p : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (p.2.2, p.1 + p.2.2, p.2.1)

/-- The cubic norm form of `ℚ(ρ)`: the determinant of multiplication by
`a + bρ + cρ²` on the power basis (an integer for integer coordinates). -/
def normForm (p : ℤ × ℤ × ℤ) : ℤ :=
  p.1 ^ 3 + p.2.1 ^ 3 + p.2.2 ^ 3 + 2 * p.1 ^ 2 * p.2.2 + p.1 * p.2.2 ^ 2
    - p.1 * p.2.1 ^ 2 - p.2.1 * p.2.2 ^ 2 - 3 * p.1 * p.2.1 * p.2.2

/-- `tick` on coordinates is multiplication by `t` under `embed`, in any
commutative ring in which `t³ = t + 1`. -/
lemma embed_tick {K : Type*} [CommRing K] (t : K) (ht : t ^ 3 = t + 1)
    (p : ℤ × ℤ × ℤ) : embed t (tick p) = t * embed t p := by
  obtain ⟨a, b, c⟩ := p
  simp only [embed, tick]
  push_cast
  linear_combination (-(c : K)) * ht

/-- `n` ticks on coordinates is multiplication by `tⁿ` under `embed`:
`σ(ρⁿ·x) = σ(ρ)ⁿ·σ(x)` in coordinates. -/
lemma embed_tick_iter {K : Type*} [CommRing K] (t : K) (ht : t ^ 3 = t + 1)
    (p : ℤ × ℤ × ℤ) (n : ℕ) : embed t (tick^[n] p) = t ^ n * embed t p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', embed_tick t ht, ih, pow_succ]
      ring

/-- `embed` is additive in the coordinates (difference form). -/
lemma embed_sub {K : Type*} [CommRing K] (t : K) (p q : ℤ × ℤ × ℤ) :
    embed t (p - q) = embed t p - embed t q := by
  simp only [embed, Prod.fst_sub, Prod.snd_sub]
  push_cast
  ring

/-- Complex conjugation commutes with `embed` (integer coordinates are real). -/
lemma conj_embed (z : ℂ) (p : ℤ × ℤ × ℤ) :
    (starRingEnd ℂ) (embed z p) = embed ((starRingEnd ℂ) z) p := by
  simp only [embed, map_add, map_mul, map_pow, map_intCast]

/-! ## T1 — the exact contraction rate -/

section RootPair

variable {r : ℝ} {z : ℂ}

private lemma z_ne_ofReal (him : z.im ≠ 0) : z ≠ (r : ℂ) := by
  intro h
  apply him
  rw [h, Complex.ofReal_im]

/-- A non-real root of `X³ − X − 1` satisfies the quadratic cofactor of
`X − r`: `z² + r·z + (r² − 1) = 0`. -/
lemma quad_of_nonreal_root (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) : z ^ 2 + (r : ℂ) * z + ((r : ℂ) ^ 2 - 1) = 0 := by
  have hrC : (r : ℂ) ^ 3 = (r : ℂ) + 1 := by exact_mod_cast hr
  have hfac : (z - (r : ℂ)) * (z ^ 2 + (r : ℂ) * z + ((r : ℂ) ^ 2 - 1)) = 0 := by
    linear_combination hz - hrC
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) (z_ne_ofReal him)
  · exact h

/-- The two non-real roots of the cubic are conjugate and sum to `−r`
(the trace of the quadratic cofactor). -/
lemma add_conj_root (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) : z + (starRingEnd ℂ) z = -(r : ℂ) := by
  have key := quad_of_nonreal_root hr hz him
  have key2 : ((starRingEnd ℂ) z) ^ 2 + (r : ℂ) * ((starRingEnd ℂ) z)
      + ((r : ℂ) ^ 2 - 1) = 0 := by
    have h := congrArg (starRingEnd ℂ) key
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero,
      Complex.conj_ofReal] at h
    exact h
  have hne : z - (starRingEnd ℂ) z ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact him (Complex.conj_eq_iff_im.mp h.symm)
  have hfac : (z - (starRingEnd ℂ) z) * (z + (starRingEnd ℂ) z + (r : ℂ)) = 0 := by
    linear_combination key - key2
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd h hne
  · linear_combination h

/-- The two non-real roots multiply to `r² − 1 = 1/r`
(the constant term of the quadratic cofactor). -/
lemma mul_conj_root (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) : z * (starRingEnd ℂ) z = (r : ℂ) ^ 2 - 1 := by
  have key := quad_of_nonreal_root hr hz him
  have hsum := add_conj_root hr hz him
  linear_combination z * hsum - key

/-- **T1 (exact contraction rate).** If `r` is the real root and `z` a
non-real root of `X³ − X − 1`, then `r·‖z‖² = 1`: one tick of the transverse
dynamics contracts area by exactly `1/ρ`, i.e. length by `ρ^(−1/2)`. -/
theorem tick_contraction (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) : r * ‖z‖ ^ 2 = 1 := by
  have h := mul_conj_root hr hz him
  rw [Complex.mul_conj] at h
  have h2 : Complex.normSq z = r ^ 2 - 1 := by exact_mod_cast h
  rw [← Complex.normSq_eq_norm_sq, h2]
  linear_combination hr

/-- The real root of `x³ − x − 1` exceeds 1 (so the tick strictly contracts
the transverse plane). -/
theorem one_lt_root (hr : r ^ 3 = r + 1) : 1 < r := by
  by_contra hle
  rw [not_lt] at hle
  have h1 : 0 ≤ (1 - r) * (r + 1) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : (1 - r) * (r + 1) ^ 2 = -r ^ 2 := by linear_combination -hr
  have h3 : r ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg r)
  have h4 : r = 0 := sq_eq_zero_iff.mp h3
  rw [h4] at hr
  norm_num at hr

/-- The transverse eigenvalue is a strict contraction: `‖z‖ < 1`. -/
theorem norm_z_lt_one (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) : ‖z‖ < 1 := by
  have h1 := tick_contraction hr hz him
  have h2 := one_lt_root hr
  nlinarith [norm_nonneg z, sq_nonneg (‖z‖ - 1), sq_nonneg (‖z‖ + 1)]

/-- **T1, rate form:** `‖z‖ = r^(−1/2)` — each tick contracts transverse
lengths by exactly `ρ^(−1/2)`. -/
theorem norm_z_eq_rpow (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) : ‖z‖ = r ^ (-(1 / 2) : ℝ) := by
  have h1 := tick_contraction hr hz him
  have hrpos : (0 : ℝ) < r := lt_trans one_pos (one_lt_root hr)
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have hz2 : ‖z‖ ^ 2 = r⁻¹ := by
    field_simp
    linear_combination h1
  calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
    _ = Real.sqrt r⁻¹ := by rw [hz2]
    _ = (r⁻¹) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
    _ = (r ^ ((-1 : ℝ))) ^ ((1 : ℝ) / 2) := by rw [Real.rpow_neg_one]
    _ = r ^ ((-1 : ℝ) * (1 / 2)) := (Real.rpow_mul hrpos.le _ _).symm
    _ = r ^ (-(1 / 2) : ℝ) := by norm_num

/-! ## T2 — the Meyer separation inequality -/

/-- **Norm-form factorization.** For integer coordinates `p = (a,b,c)`, the
product of the three embeddings of `a + bρ + cρ²` is the integer `normForm p`:
`x₁ · x₂ · x̄₂ = N(a,b,c)`. -/
lemma normForm_factor (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) (p : ℤ × ℤ × ℤ) :
    ((embed r p : ℝ) : ℂ) * embed z p * (starRingEnd ℂ) (embed z p)
      = ((normForm p : ℤ) : ℂ) := by
  obtain ⟨a, b, c⟩ := p
  have hrC : (r : ℂ) ^ 3 = (r : ℂ) + 1 := by exact_mod_cast hr
  have key := quad_of_nonreal_root hr hz him
  have hconj : (starRingEnd ℂ) z = -(r : ℂ) - z := by
    linear_combination add_conj_root hr hz him
  rw [conj_embed]
  simp only [embed, normForm]
  rw [hconj]
  push_cast
  linear_combination
    (2 * (a : ℂ) ^ 2 * c - a * (b : ℂ) ^ 2 + 3 * (a : ℂ) * b * c * r
      + (a : ℂ) * c ^ 2 * (r : ℂ) ^ 2 + (a : ℂ) * c ^ 2 * r * z
      + (a : ℂ) * c ^ 2 * z ^ 2 + (a : ℂ) * c ^ 2 - (b : ℂ) ^ 3 * r
      + (b : ℂ) * c ^ 2 * (r : ℂ) ^ 2 * z + (b : ℂ) * c ^ 2 * r * z ^ 2
      + (b : ℂ) * c ^ 2 * r - (c : ℂ) ^ 3 * (r : ℂ) ^ 4
      + (c : ℂ) ^ 3 * (r : ℂ) ^ 3 * z + (c : ℂ) ^ 3 * (r : ℂ) ^ 2 * z ^ 2
      + (c : ℂ) ^ 3 * (r : ℂ) ^ 2) * key
    + (-3 * (a : ℂ) * b * c + (b : ℂ) ^ 3 - (b : ℂ) * c ^ 2
      + (c : ℂ) ^ 3 * (r : ℂ) ^ 3 - (c : ℂ) ^ 3 * r + (c : ℂ) ^ 3) * hrC

/-- Real form of the factorization: `x₁ · ‖x₂‖²_normSq = N(a,b,c)` in `ℝ`. -/
lemma normForm_eq_mul_normSq (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) (p : ℤ × ℤ × ℤ) :
    (normForm p : ℝ) = embed r p * Complex.normSq (embed z p) := by
  have h := normForm_factor hr hz him p
  rw [mul_assoc, Complex.mul_conj] at h
  exact_mod_cast h.symm

/-- **Nonzero coordinates embed to nonzero numbers.** In any field `K` that is
a ℚ-algebra, if `t³ = t + 1` then `(a,b,c) ≠ 0` implies `a + bt + ct² ≠ 0`:
otherwise `t`, whose minimal polynomial is the irreducible cubic `X³ − X − 1`,
would satisfy a nonzero rational polynomial of degree ≤ 2. -/
lemma embed_ne_zero {K : Type*} [Field K] [Algebra ℚ K] {t : K}
    (ht : t ^ 3 = t + 1) {p : ℤ × ℤ × ℤ} (hp : p ≠ 0) : embed t p ≠ 0 := by
  obtain ⟨a, b, c⟩ := p
  have htroot : aeval t (X ^ 3 - X - 1 : ℚ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_one]
    linear_combination ht
  have hmonic : (X ^ 3 - X - 1 : ℚ[X]).Monic := by monicity!
  have hmin : minpoly ℚ t = X ^ 3 - X - 1 :=
    (minpoly.eq_of_irreducible_of_monic cubicQ_irreducible htroot hmonic).symm
  intro h0
  have hqz : aeval t (C (a : ℚ) + C (b : ℚ) * X + C (c : ℚ) * X ^ 2) = 0 := by
    simp only [map_add, map_mul, map_pow, aeval_X, map_intCast]
    simpa [embed] using h0
  have hqne : (C (a : ℚ) + C (b : ℚ) * X + C (c : ℚ) * X ^ 2) ≠ 0 := by
    intro hq0
    apply hp
    have ha' : a = 0 := by
      have h := congrArg (fun f => Polynomial.coeff f 0) hq0
      simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow, coeff_zero] at h
      norm_num at h
      exact h
    have hb' : b = 0 := by
      have h := congrArg (fun f => Polynomial.coeff f 1) hq0
      simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow, coeff_zero] at h
      norm_num at h
      exact h
    have hc' : c = 0 := by
      have h := congrArg (fun f => Polynomial.coeff f 2) hq0
      simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow, coeff_zero] at h
      norm_num at h
      exact h
    subst ha' hb' hc'
    rfl
  have hle := minpoly.degree_le_of_ne_zero ℚ t hqne hqz
  have h1 : (minpoly ℚ t).natDegree ≤
      (C (a : ℚ) + C (b : ℚ) * X + C (c : ℚ) * X ^ 2).natDegree :=
    Polynomial.natDegree_le_natDegree hle
  have h2 : (minpoly ℚ t).natDegree = 3 := by
    rw [hmin]
    compute_degree!
  have h3 : (C (a : ℚ) + C (b : ℚ) * X + C (c : ℚ) * X ^ 2).natDegree ≤ 2 := by
    compute_degree!
  omega

/-- **T2 (Meyer separation, product form).** For every nonzero coordinate
triple, `1 ≤ |x₁| · ‖x₂‖²`: the product of the real-embedding size and the
squared transverse distance from 0 is at least 1 (it is `|N| ≥ 1` for the
nonzero integer `N = normForm p`). -/
theorem meyer_separation (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) (p : ℤ × ℤ × ℤ) (hp : p ≠ 0) :
    1 ≤ |embed r p| * ‖embed z p‖ ^ 2 := by
  have hfac := normForm_eq_mul_normSq hr hz him p
  have h1 : embed r p ≠ 0 := embed_ne_zero (by exact_mod_cast hr) hp
  have h2 : embed z p ≠ 0 := embed_ne_zero hz hp
  have hNne : normForm p ≠ 0 := by
    intro h
    apply mul_ne_zero h1 (fun hh => h2 (Complex.normSq_eq_zero.mp hh))
    rw [← hfac, h, Int.cast_zero]
  have hN1 : (1 : ℤ) ≤ |normForm p| := Int.one_le_abs hNne
  calc (1 : ℝ) ≤ |(normForm p : ℝ)| := by exact_mod_cast hN1
    _ = |embed r p * Complex.normSq (embed z p)| := by rw [hfac]
    _ = |embed r p| * Complex.normSq (embed z p) := by
        rw [abs_mul, abs_of_nonneg (Complex.normSq_nonneg _)]
    _ = |embed r p| * ‖embed z p‖ ^ 2 := by rw [Complex.normSq_eq_norm_sq]

/-- **T2 (Meyer separation, radius form).** `‖x₂‖ ≥ |x₁|^(−1/2)` for every
nonzero coordinate triple: the certification radius is uniformly positive on
any window of bounded Perron coordinate. -/
theorem meyer_separation_rpow (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) (p : ℤ × ℤ × ℤ) (hp : p ≠ 0) :
    |embed r p| ^ (-(1 / 2) : ℝ) ≤ ‖embed z p‖ := by
  have hsep := meyer_separation hr hz him p hp
  have hx1 : embed r p ≠ 0 := embed_ne_zero (by exact_mod_cast hr) hp
  have habs : 0 < |embed r p| := abs_pos.mpr hx1
  have hsq : (|embed r p| ^ (-(1 / 2) : ℝ)) ^ 2 = |embed r p|⁻¹ := by
    rw [← Real.rpow_two, ← Real.rpow_mul habs.le]
    norm_num [Real.rpow_neg_one]
  have hinv : |embed r p| * |embed r p|⁻¹ = 1 := mul_inv_cancel₀ habs.ne'
  have hle2 : |embed r p|⁻¹ ≤ ‖embed z p‖ ^ 2 := by
    nlinarith [hsep, habs]
  have ht : 0 < |embed r p| ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos habs _
  nlinarith [hsq, hle2, ht, norm_nonneg (embed z p)]

/-! ## T3 — certification soundness -/

/-- The record lattice: the image `σ₂(ℤ[ρ]) ⊆ ℂ` of the ring of integers'
order `ℤ[ρ]` under the complex embedding `ρ ↦ z`. -/
def lattice (z : ℂ) : Set ℂ := Set.range (embed z)

/-- **T3(a) — lattice invariance.** Multiplication by `z` maps the record
lattice ONTO itself: `ρ` is a unit of `ℤ[ρ]` (`ρ⁻¹ = ρ² − 1`), so one tick
permutes the record lattice. -/
theorem lattice_tick_invariant (hz : z ^ 3 = z + 1) :
    (fun x => z * x) '' lattice z = lattice z := by
  ext y
  constructor
  · rintro ⟨x, ⟨p, rfl⟩, rfl⟩
    exact ⟨tick p, embed_tick z hz p⟩
  · rintro ⟨p, rfl⟩
    obtain ⟨a, b, c⟩ := p
    refine ⟨embed z (b - a, c, a), ⟨(b - a, c, a), rfl⟩, ?_⟩
    show z * embed z (b - a, c, a) = embed z (a, b, c)
    rw [← embed_tick z hz]
    have h : b - a + a = b := by omega
    show embed z (a, b - a + a, c) = embed z (a, b, c)
    rw [h]

/-- **T3(b) — windowed uniform discreteness.** Distinct lattice points whose
real embeddings differ by at most `H` are at transverse distance at least
`H^(−1/2)`. (Corollary of T2 applied to the difference.) -/
theorem windowed_separation (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) {p q : ℤ × ℤ × ℤ} (hpq : p ≠ q) {H : ℝ}
    (hH : |embed r p - embed r q| ≤ H) :
    H ^ (-(1 / 2) : ℝ) ≤ ‖embed z p - embed z q‖ := by
  have hne : p - q ≠ 0 := sub_ne_zero.mpr hpq
  have h1 := meyer_separation_rpow hr hz him (p - q) hne
  rw [embed_sub, embed_sub] at h1
  have habs : 0 < |embed r p - embed r q| := by
    rw [abs_pos, ← embed_sub]
    exact embed_ne_zero (by exact_mod_cast hr) hne
  exact le_trans (Real.rpow_le_rpow_of_nonpos habs hH (by norm_num)) h1

/-- **T3(c) — certification soundness (the two-line theorem, windowed).**
Suppose the state `w` is certified: `‖w − σ₂(ℓ)‖ < (1/2)·H^(−1/2)` for a
lattice point `ℓ` and window scale `H > 0`. After `n` ticks the state is
`zⁿ·w` and the committed point is `σ₂(ρⁿℓ) = zⁿ·σ₂(ℓ)`. Then for EVERY other
lattice point `ℓ' ≠ ρⁿℓ` whose real embedding lies within `H` of that of
`ρⁿℓ`, the evolved state is strictly closer to the committed point than to
`ℓ'`: the nearest-point reading within the window never changes. Proof =
exact equivariance + monotone contraction (`‖z‖ < 1`) + triangle inequality
against T3(b). The window hypothesis is essential and explicit (the
unwindowed transverse projection is dense). -/
theorem certification_soundness (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) (w : ℂ) (ℓ : ℤ × ℤ × ℤ) {H : ℝ} (hH : 0 < H)
    (hw : ‖w - embed z ℓ‖ < H ^ (-(1 / 2) : ℝ) / 2)
    (n : ℕ) (ℓ' : ℤ × ℤ × ℤ) (hne : ℓ' ≠ tick^[n] ℓ)
    (hwin : |embed r ℓ' - r ^ n * embed r ℓ| ≤ H) :
    ‖z ^ n * w - z ^ n * embed z ℓ‖ < ‖z ^ n * w - embed z ℓ'‖ := by
  have hdpos : 0 < H ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hH _
  have hzn : ‖z ^ n‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg z) (norm_z_lt_one hr hz him).le
  have hcommit : ‖z ^ n * w - z ^ n * embed z ℓ‖ < H ^ (-(1 / 2) : ℝ) / 2 := by
    calc ‖z ^ n * w - z ^ n * embed z ℓ‖ = ‖z ^ n‖ * ‖w - embed z ℓ‖ := by
          rw [← norm_mul, mul_sub]
      _ ≤ 1 * ‖w - embed z ℓ‖ := mul_le_mul_of_nonneg_right hzn (norm_nonneg _)
      _ = ‖w - embed z ℓ‖ := one_mul _
      _ < H ^ (-(1 / 2) : ℝ) / 2 := hw
  have hsep : H ^ (-(1 / 2) : ℝ) ≤ ‖embed z ℓ' - z ^ n * embed z ℓ‖ := by
    rw [← embed_tick_iter z hz]
    rw [← embed_tick_iter r hr] at hwin
    exact windowed_separation hr hz him hne hwin
  have htri : ‖embed z ℓ' - z ^ n * embed z ℓ‖ ≤
      ‖z ^ n * w - embed z ℓ'‖ + ‖z ^ n * w - z ^ n * embed z ℓ‖ := by
    calc ‖embed z ℓ' - z ^ n * embed z ℓ‖
        = ‖(z ^ n * w - z ^ n * embed z ℓ) - (z ^ n * w - embed z ℓ')‖ := by
          congr 1
          ring
      _ ≤ ‖z ^ n * w - z ^ n * embed z ℓ‖ + ‖z ^ n * w - embed z ℓ'‖ :=
          norm_sub_le _ _
      _ = ‖z ^ n * w - embed z ℓ'‖ + ‖z ^ n * w - z ^ n * embed z ℓ‖ := by
          ring
  linarith

end RootPair

end

end Time
