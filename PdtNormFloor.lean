module
public import PdtCommitment

@[expose] public section

/-!
# PdtNormFloor — the integrality floor on ℤ[ρ], stated on the full ring

Let `ρ` be the real root of `x³ − x − 1`, `K = ℚ(ρ)` (signature `(1,1)`), and
`σ₁ : ρ ↦ r` (the real place), `σ₂ : ρ ↦ z` (the complex place, `z` non-real).
For `x = a + bρ + cρ² ∈ ℤ[ρ]` the **separation functional** is
`|σ₁(x)| · ‖σ₂(x)‖²`.

This module states, on the FULL ring `ℤ[ρ]` in explicit power-basis coordinates
`(a, b, c) : ℤ × ℤ × ℤ`, that the separation functional never drops below `1`:

* `norm_factorization` — the exact signed identity
  `σ₁(x) · ‖σ₂(x)‖²_normSq = N(a,b,c)`, with `N` the explicit integer cubic form
  `N(a,b,c) = a³ + b³ + c³ + 2a²c + ac² − ab² − bc² − 3abc`
  (`= Res_x(x³ − x − 1, a + bx + cx²)` = `det` of multiplication-by-`x` on the
  power basis);
* `norm_ne_zero` — `N(a,b,c) ≠ 0` for every nonzero triple;
* `separation_eq_abs_norm` — `|σ₁(x)| · ‖σ₂(x)‖² = |N(x)|` EXACTLY (the
  separation functional IS the absolute field norm);
* `integrality_floor` / `integrality_floor_norm` — **the flagged claim**:
  `1 ≤ |σ₁(x)| · ‖σ₂(x)‖²` for every `x ∈ ℤ[ρ] \ {0}`, in both the `normSq`
  and the `‖·‖²` spelling.

and adds the **conservation law** under the unit tick (multiplication by `ρ`,
which acts on power-basis coordinates as `(a,b,c) ↦ (c, a+c, b)` because
`ρ³ = ρ + 1`):

* `N_tick` — `N(c, a+c, b) = N(a,b,c)`, an integer polynomial identity: the
  norm form is EXACTLY invariant under multiplication by `ρ` (`N(ρ) = 1`, so
  `ρ` is a unit);
* `separation_tick_invariant` — hence the separation functional itself is
  exactly conserved by one tick;
* `functional_mul_root` — the mechanism, in unlattice form: `|r·x|·‖z·y‖² =
  |x|·‖y‖²` for ALL `x : ℝ`, `y : ℂ`, because `r·‖z‖² = 1` (the Vieta
  identity). The conservation is the contraction identity, nothing more.

and certifies **non-vacuity** of the whole `(r, z)`-hypothesis family used
throughout `PdtCommitment` and this module:

* `exists_root_pair` — such a pair `(r : ℝ, z : ℂ)` with `r³ = r + 1`,
  `z³ = z + 1`, `z.im ≠ 0` EXISTS (explicit: `z = −r/2 + (√(3r²−4)/2)·i`);
* `norm_ne_zero_uncond` — therefore `N(a,b,c) ≠ 0` unconditionally, with no
  root hypotheses at all.

## Provenance (reuse, not reproof)

The factorization and the non-vanishing of the embeddings are IMPORTED from
`PdtCommitment` (`normForm`, `normForm_eq_mul_normSq`, `embed_ne_zero`,
`tick_contraction`, `one_lt_root`), which in turn imports irreducibility of
`x³ − x − 1` from `PdtIrreducible`. `PDT.meyer_separation` there already proves
the floor in packed-triple form; this module restates it in the explicit
coordinate shape the claim is made in, names the norm form as a standalone
`ℤ → ℤ → ℤ → ℤ` function, and adds the tick-conservation law and the
non-vacuity certificate, which are new here.

No physical claim appears in any statement: this is elementary algebra of the
cubic's roots. Any physical reading of the floor (Meyer separation, Landauer,
record individuation) is an identification, not a theorem, and is not made
here.
-/

namespace PDT
namespace NormFloor

open Complex

/-! ## The norm form -/

/-- The **cubic norm form** of `ℚ(ρ)` in the power basis `(1, ρ, ρ²)`:
`N(a,b,c) = ∏_σ σ(a + bρ + cρ²)`, the determinant of multiplication by
`a + bρ + cρ²`. Equivalently `Res_x(x³ − x − 1, a + bx + cx²)`. -/
def N (a b c : ℤ) : ℤ :=
  a ^ 3 + b ^ 3 + c ^ 3 + 2 * a ^ 2 * c + a * c ^ 2 - a * b ^ 2 - b * c ^ 2 - 3 * a * b * c

/-- `N` is `PdtCommitment.normForm`, uncurried. -/
theorem N_eq_normForm (a b c : ℤ) : N a b c = normForm (a, b, c) := rfl

/-- The value of `N` on the multiplicative unit `ρ = 0 + 1·ρ + 0·ρ²`: `N(ρ) = 1`. -/
theorem N_rho : N 0 1 0 = 1 := by decide

/-- `N(1) = 1`. -/
theorem N_one : N 1 0 0 = 1 := by decide

/-! ## The factorization over the two places -/

/-- **Norm factorization on the full ring.** For every integer triple `(a,b,c)`,
every real root `r` and every non-real root `z` of `x³ − x − 1`:
`σ₁(x) · ‖σ₂(x)‖²_normSq = N(a,b,c)`, an exact signed identity in `ℝ`. -/
theorem norm_factorization {r : ℝ} {z : ℂ} (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) (a b c : ℤ) :
    ((a : ℝ) + (b : ℝ) * r + (c : ℝ) * r ^ 2)
        * Complex.normSq ((a : ℂ) + (b : ℂ) * z + (c : ℂ) * z ^ 2)
      = (N a b c : ℝ) := by
  have h := normForm_eq_mul_normSq hr hz him (a, b, c)
  rw [N_eq_normForm, h]
  simp only [embed]

/-- **The coordinate encoding of "`x ≠ 0`" is faithful.** For a real root `r`,
`a + b·r + c·r² = 0` holds exactly when `(a,b,c) = (0,0,0)`: `(1, ρ, ρ²)` is a
ℤ-basis of `ℤ[ρ]`, so the hypothesis `¬(a = 0 ∧ b = 0 ∧ c = 0)` below IS the
hypothesis "`x ≠ 0` in `ℤ[ρ]`", with nothing lost in the encoding. -/
theorem embed_eq_zero_iff {r : ℝ} (hr : r ^ 3 = r + 1) (a b c : ℤ) :
    (a : ℝ) + (b : ℝ) * r + (c : ℝ) * r ^ 2 = 0 ↔ (a = 0 ∧ b = 0 ∧ c = 0) := by
  constructor
  · intro h
    by_contra hp
    have hne : ((a, b, c) : ℤ × ℤ × ℤ) ≠ 0 := by
      intro h0
      exact hp (by simpa [Prod.ext_iff] using h0)
    apply embed_ne_zero (K := ℝ) (t := r) (by exact_mod_cast hr) hne
    simp only [embed]
    exact h
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

/-- **The norm form never vanishes on a nonzero triple.** If `(a,b,c) ≠ (0,0,0)`
then `N(a,b,c) ≠ 0`: both embeddings of a nonzero element of `ℤ[ρ]` are nonzero,
because a vanishing embedding would make a root of the irreducible cubic satisfy
a nonzero rational polynomial of degree `≤ 2`. -/
theorem norm_ne_zero {r : ℝ} {z : ℂ} (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) (a b c : ℤ) (hp : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    N a b c ≠ 0 := by
  have hne : ((a, b, c) : ℤ × ℤ × ℤ) ≠ 0 := by
    intro h
    exact hp (by simpa [Prod.ext_iff] using h)
  have h1 : embed r (a, b, c) ≠ 0 := embed_ne_zero (by exact_mod_cast hr) hne
  have h2 : embed z (a, b, c) ≠ 0 := embed_ne_zero hz hne
  have hfac := normForm_eq_mul_normSq hr hz him (a, b, c)
  intro h
  have hzero : ((normForm (a, b, c) : ℤ) : ℝ) = 0 := by
    rw [← N_eq_normForm, h]; norm_num
  rw [hfac] at hzero
  rcases mul_eq_zero.mp hzero with h' | h'
  · exact h1 h'
  · exact h2 (Complex.normSq_eq_zero.mp h')

/-- **The separation functional IS the absolute field norm.** For every integer
triple, `|σ₁(x)| · ‖σ₂(x)‖²_normSq = |N(a,b,c)|` — exactly, with no hypothesis
on the triple. -/
theorem separation_eq_abs_norm {r : ℝ} {z : ℂ} (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) (a b c : ℤ) :
    |(a : ℝ) + (b : ℝ) * r + (c : ℝ) * r ^ 2|
        * Complex.normSq ((a : ℂ) + (b : ℂ) * z + (c : ℂ) * z ^ 2)
      = |(N a b c : ℝ)| := by
  rw [← norm_factorization hr hz him a b c, abs_mul,
    abs_of_nonneg (Complex.normSq_nonneg _)]

/-! ## The integrality floor -/

/-- **THE INTEGRALITY FLOOR, on the full ring.** For every nonzero
`x = a + bρ + cρ² ∈ ℤ[ρ]` — all integer triples, no restriction — the separation
functional is at least `1`:
`1 ≤ |σ₁(x)| · ‖σ₂(x)‖²`.
It equals `|N(x)|` (`separation_eq_abs_norm`) for the nonzero rational integer
`N(x)` (`norm_ne_zero`), and `|n| ≥ 1` for every nonzero `n : ℤ`. -/
theorem integrality_floor {r : ℝ} {z : ℂ} (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) (a b c : ℤ) (hp : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    1 ≤ |(a : ℝ) + (b : ℝ) * r + (c : ℝ) * r ^ 2|
          * Complex.normSq ((a : ℂ) + (b : ℂ) * z + (c : ℂ) * z ^ 2) := by
  have hN : (1 : ℤ) ≤ |N a b c| := Int.one_le_abs (norm_ne_zero hr hz him a b c hp)
  rw [separation_eq_abs_norm hr hz him a b c]
  exact_mod_cast hN

/-- **The integrality floor, `‖·‖²` spelling.** Same statement with the complex
norm squared in place of `normSq`. -/
theorem integrality_floor_norm {r : ℝ} {z : ℂ} (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) (a b c : ℤ) (hp : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    1 ≤ |(a : ℝ) + (b : ℝ) * r + (c : ℝ) * r ^ 2|
          * ‖(a : ℂ) + (b : ℂ) * z + (c : ℂ) * z ^ 2‖ ^ 2 := by
  have h := integrality_floor hr hz him a b c hp
  rwa [Complex.normSq_eq_norm_sq] at h

/-! ## Conservation under the unit tick -/

/-- **The norm form is exactly invariant under the unit tick.** Multiplication
by `ρ` sends power-basis coordinates `(a,b,c) ↦ (c, a+c, b)` (because
`ρ³ = ρ + 1`), and `N(c, a+c, b) = N(a,b,c)` identically in `ℤ[a,b,c]`: `ρ` is a
unit of norm `N(ρ) = 1`, so `N(ρx) = N(ρ)N(x) = N(x)`. -/
theorem N_tick (a b c : ℤ) : N c (a + c) b = N a b c := by
  unfold N; ring

/-- The tick, in the coordinate form used by `PdtCommitment.tick`. -/
theorem N_tick' (p : ℤ × ℤ × ℤ) : N (tick p).1 (tick p).2.1 (tick p).2.2 = N p.1 p.2.1 p.2.2 := by
  obtain ⟨a, b, c⟩ := p
  exact N_tick a b c

/-- **The mechanism of conservation.** For ALL `x : ℝ` and `y : ℂ`,
`|r·x| · ‖z·y‖² = |x| · ‖y‖²`: multiplying the real place by `r` and the complex
place by `z` leaves the product functional fixed, because `r·‖z‖² = 1`
(the Vieta identity, `PdtCommitment.tick_contraction`). No lattice,
no integrality: this is the contraction identity alone. -/
theorem functional_mul_root {r : ℝ} {z : ℂ} (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) (x : ℝ) (y : ℂ) :
    |r * x| * Complex.normSq (z * y) = |x| * Complex.normSq y := by
  have hrpos : (0 : ℝ) < r := lt_trans one_pos (one_lt_root hr)
  have hcon : r * ‖z‖ ^ 2 = 1 := tick_contraction hr hz him
  have hnsq : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
  rw [abs_mul, abs_of_pos hrpos, Complex.normSq_mul, hnsq]
  calc r * |x| * (‖z‖ ^ 2 * Complex.normSq y)
      = (r * ‖z‖ ^ 2) * (|x| * Complex.normSq y) := by ring
    _ = |x| * Complex.normSq y := by rw [hcon, one_mul]

/-- **The separation functional is exactly conserved by one tick.** The
functional of `ρ·x`, whose coordinates are `(c, a+c, b)`, equals that of `x`:
the distinguishability budget of `ℤ[ρ]` is an exactly conserved quantity under
the dynamics, in both directions (the tick is a lattice automorphism). -/
theorem separation_tick_invariant {r : ℝ} {z : ℂ} (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1)
    (him : z.im ≠ 0) (a b c : ℤ) :
    |(c : ℝ) + ((a + c : ℤ) : ℝ) * r + (b : ℝ) * r ^ 2|
        * Complex.normSq ((c : ℂ) + ((a + c : ℤ) : ℂ) * z + (b : ℂ) * z ^ 2)
      = |(a : ℝ) + (b : ℝ) * r + (c : ℝ) * r ^ 2|
          * Complex.normSq ((a : ℂ) + (b : ℂ) * z + (c : ℂ) * z ^ 2) := by
  rw [separation_eq_abs_norm hr hz him c (a + c) b,
    separation_eq_abs_norm hr hz him a b c, N_tick]

/-! ## Non-vacuity: the root pair exists -/

/-- **The hypothesis family is non-vacuous.** There is a real `r` and a non-real
`z` with `r³ = r + 1` and `z³ = z + 1`. Explicitly `z = −r/2 + (√(3r² − 4)/2)·i`,
the root of the Vieta quadratic `x² + rx + (r² − 1)` complementary to `r`; the
real root itself comes from the intermediate value theorem on `[1,2]`. -/
theorem exists_root_pair :
    ∃ (r : ℝ) (z : ℂ), r ^ 3 = r + 1 ∧ z ^ 3 = z + 1 ∧ z.im ≠ 0 := by
  -- a real root in [1,2] by the intermediate value theorem
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 - x - 1) (Set.Icc 1 2) := by fun_prop
  have hmem : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 3 - x - 1) 1)
      ((fun x : ℝ => x ^ 3 - x - 1) 2) := by
    constructor <;> norm_num
  obtain ⟨r, _, hr0⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hcont hmem
  have hr : r ^ 3 = r + 1 := by
    have : r ^ 3 - r - 1 = 0 := hr0
    linarith
  -- the discriminant of the complementary quadratic is positive
  have h1r : 1 < r := one_lt_root hr
  have hdisc : 0 < 3 * r ^ 2 - 4 := by nlinarith [hr, h1r]
  set t : ℝ := Real.sqrt (3 * r ^ 2 - 4) with ht_def
  have htpos : 0 < t := Real.sqrt_pos.mpr hdisc
  have ht : t ^ 2 = 3 * r ^ 2 - 4 := Real.sq_sqrt hdisc.le
  refine ⟨r, ((-r / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I, hr, ?_, ?_⟩
  · have hI : (Complex.I) ^ 2 = -1 := Complex.I_sq
    have htC : ((t : ℝ) : ℂ) ^ 2 = 3 * ((r : ℝ) : ℂ) ^ 2 - 4 := by exact_mod_cast ht
    have hrC : ((r : ℝ) : ℂ) ^ 3 = ((r : ℝ) : ℂ) + 1 := by exact_mod_cast hr
    have hquad : (((-r / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I) ^ 2
        = -((r : ℝ) : ℂ) * (((-r / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I)
          - (((r : ℝ) : ℂ) ^ 2 - 1) := by
      push_cast
      linear_combination (((t : ℝ) : ℂ) ^ 2 / 4) * hI - (1 / 4 : ℂ) * htC
    linear_combination (((-r / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I
      - ((r : ℝ) : ℂ)) * hquad + hrC
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
    positivity

/-- **The norm form never vanishes on a nonzero triple — unconditionally.** No
root hypotheses: the root pair exists (`exists_root_pair`), so this is a bare
statement about the integer cubic form `N`. -/
theorem norm_ne_zero_uncond (a b c : ℤ) (hp : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    N a b c ≠ 0 := by
  obtain ⟨r, z, hr, hz, him⟩ := exists_root_pair
  exact norm_ne_zero hr hz him a b c hp

/-- **`|N| ≥ 1` on the full ring, unconditionally** — the arithmetic content of
the integrality floor, stated with no analytic input at all. -/
theorem one_le_abs_norm (a b c : ℤ) (hp : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    1 ≤ |N a b c| :=
  Int.one_le_abs (norm_ne_zero_uncond a b c hp)

end NormFloor
end PDT

/-! ### Axiom audit -/

#print axioms PDT.NormFloor.N_eq_normForm
#print axioms PDT.NormFloor.N_rho
#print axioms PDT.NormFloor.N_one
#print axioms PDT.NormFloor.norm_factorization
#print axioms PDT.NormFloor.embed_eq_zero_iff
#print axioms PDT.NormFloor.norm_ne_zero
#print axioms PDT.NormFloor.separation_eq_abs_norm
#print axioms PDT.NormFloor.integrality_floor
#print axioms PDT.NormFloor.integrality_floor_norm
#print axioms PDT.NormFloor.N_tick
#print axioms PDT.NormFloor.N_tick'
#print axioms PDT.NormFloor.functional_mul_root
#print axioms PDT.NormFloor.separation_tick_invariant
#print axioms PDT.NormFloor.exists_root_pair
#print axioms PDT.NormFloor.norm_ne_zero_uncond
#print axioms PDT.NormFloor.one_le_abs_norm
