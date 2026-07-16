# The Arithmetic of Time

A Lean 4 formalization of the mathematics of time — the individuation of
moments, an arithmetic arrow of irreversibility, an aperiodic-but-not-random
tick, and the Pisot boundary that separates settling from spiraling.

Everything below is a machine-checked theorem, verified by the Lean 4 kernel
against Mathlib — with one clearly-marked exception, the numerical companion in
[`diffraction/`](./diffraction). The repository studies a small, self-contained
*mathematical model* of time built from two cubic/quartic units and the
geometry of their number fields; it makes no empirical claim about physical
time (see **Scope**).

## What is proved

1. **A moment is individuated; the arrow is arithmetic.** For the non-real roots
   `z` of `x³ − x − 1` (with real root `r = ρ`, the plastic number and the
   smallest Pisot number), the transverse dynamics contracts at an *exact* rate
   `r·‖z‖² = 1`, so `‖z‖ = r^(−1/2)` — one irreversible step
   (`Time.tick_contraction`, `Time.norm_z_eq_rpow` in `Settling.lean`). On the
   ring of integers `ℤ[ρ]` this is sharpened to a **Meyer-type separation
   inequality** `|σ₁(x)|·‖σ₂(x)‖² ≥ 1` for every nonzero `x`
   (`Time.meyer_separation`, `Time.meyer_separation_rpow`): distinct arithmetic
   states can never be confused within a bounded window, and the contraction is
   never undone. The same theorems are re-proved by an independent second route
   in `SettlingReplica.lean` (`TimeReplica.meyer_separation`,
   `TimeReplica.certification_soundness`).

2. **The clock is untunable.** The four algebraic constants
   `κ = (Q/ρ)²`, `r_in = √3/2`, `χ = Q/ρ`, and `A* = √(2ρ) − √(3/4 − ρ⁻²)`
   satisfy the *strict* chain `κ < r_in < χ < A*` (`Time.chain_strict` in
   `ConstantChain.lean`). Both threshold constants are proved **not** to be
   algebraic integers — `r_in` because `r_in² = 3/4 ∉ ℤ`
   (`Time.rin_not_isIntegral`), and `A*` via a cubic-field argument with no
   Galois machinery (`Time.Astar_not_isIntegral`) — while every monomial `ρᵃQᵇ`
   *is* an algebraic integer (indeed a unit, `Time.rho_norm_one`,
   `Time.Q_norm_neg_one`). Hence **no monomial `ρᵃQᵇ` can ever equal a
   threshold**, at any integer exponents (`Time.rin_ne_coupling_zmonomial`,
   `Time.Astar_ne_coupling_zmonomial` in `AlgebraicIntegers.lean`): the chain can
   never collapse into an algebraic coincidence.

3. **The tick is aperiodic but not random.** The mechanical (Beatty/Sturmian)
   word `m(n) = ⌊(n+1)β⌋ − ⌊nβ⌋` of an irrational slope `β ∈ (0,1)` is proved to
   be **two-valued** (`Time.m_mem`), of **density equal to the slope**
   (`Time.density_tendsto`, via the exact telescoping `Time.sum_m_eq`),
   **aperiodic** — it has no period for irrational `β` (`Time.aperiodic`) — and
   **balanced**: any two windows of equal length have 1-counts differing by at
   most one (`Time.balanced` in `MechanicalWord.lean`). Balance is the precise
   "maximally even, not random" property of a Sturmian word.

4. **The Pisot boundary — the cubic settles, the quartic spirals.** Directly from
   the two defining polynomials, every non-real root `z` of `x³ − x − 1` has
   `‖z‖ < 1` (`Time.cubic_conj_norm_lt_one`) — it *contracts*, so `ρ` is a Pisot
   number and its arithmetic settles — while every non-real root `w` of
   `x⁴ − x − 1` has `‖w‖ > 1` (`Time.quartic_conj_norm_gt_one`) — it *expands*, so
   `Q` is **not** a Pisot number. Together (`Time.pisot_boundary_dichotomy`):
   `‖z‖ < 1 ∧ 1 < ‖w‖` — the two roots sit on opposite sides of the unit circle.
   The proof is elementary and self-contained: writing `σ = w + conj w` and
   `s = w·conj w = ‖w‖²` and reducing modulo the Vieta quadratic `w² = σ·w − s`
   gives one real identity per polynomial — `s² − σ²·s = 1` (forcing `s > 1`) for
   the quartic, `s³ + s² = 1` (forcing `s < 1`) for the cubic — one flipped
   inequality, driven purely by the degree. This is the concrete
   `settling ⟺ Pisot` fact for the two polynomials; it does **not** prove Siegel's
   theorem that `ρ` is the *smallest* Pisot number, which needs Pisot theory
   outside Mathlib.

## Scope

These are machine-checked theorems about a mathematical *model* of time: the
individuation and irreversibility live in the arithmetic of `ℤ[ρ]`, the untunable
constants in the geometry of the fields `ℚ(ρ)` and `ℚ(Q)`, the tick in the
symbolic dynamics of a mechanical word, and the settle/spiral dichotomy in the
moduli of the roots. Whether this model *describes physical time* is a separate,
empirical question and is not claimed here; the repository asserts only the
mathematics that the kernel has checked.

## Build

```
lake exe cache get   # fetch the prebuilt Mathlib cache
lake build           # compiles the eight project modules
```

Toolchain `leanprover/lean4:v4.31.0`, Mathlib `v4.31.0` (pinned in
`lean-toolchain` and `lake-manifest.json`). The project modules are:

| Module | Content |
| --- | --- |
| `Irreducibility.lean` | `x³ − x − 1` and `x⁴ − x − 1` are irreducible over ℚ |
| `FieldNorm.lean` | field norms `N(ρ) = 1`, `N(Q) = −1` (ρ, Q are units) |
| `Settling.lean` | contraction rate, Meyer separation, certification soundness |
| `SettlingReplica.lean` | an independent second formalization of `Settling` |
| `ConstantChain.lean` | the strict chain `κ < r_in < χ < A*` and its identities |
| `AlgebraicIntegers.lean` | thresholds are not algebraic integers; no-identity |
| `MechanicalWord.lean` | the Sturmian word: two-valued, density, aperiodic, balanced |
| `PisotBoundary.lean` | the settle/spiral dichotomy: non-real roots of `x³−x−1` have `‖·‖<1`, of `x⁴−x−1` have `‖·‖>1` |

## Numerical companion: diffraction

[`diffraction/`](./diffraction) pictures the *spectral* face of the mechanical
word: laid out as positions and diffracted, it shows sharp Bragg peaks at the
incommensurate module `m + nβ` — quasicrystalline order — with the
crystal-forbidden peak growing `∝ N` while a Poisson gas of the same density
stays flat. That folder is **computation, not proof**; the underlying
pure-point property is a theorem of the model-set literature (Hof 1995;
Baake–Grimm 2013), cited there.

## Rigor note

Every theorem's axiom dependency is a subset of
`{propext, Classical.choice, Quot.sound}` — the standard classical foundation of
Mathlib. There is **no `sorry`**, **no `native_decide`**, and **no custom
axiom** anywhere in the development; the irrationality of the slope in
`MechanicalWord` (which lies beyond Mathlib) is carried as an explicit
hypothesis, never assumed as an axiom. You can reproduce the audit with
`#print axioms Time.balanced` (and likewise for any theorem above).

## License

MIT — see [`LICENSE`](./LICENSE).
