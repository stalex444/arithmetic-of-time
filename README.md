# The Arithmetic of Time

A Lean 4 formalization of the mathematics of time — the individuation of
moments, an arithmetic arrow of irreversibility, an aperiodic-but-not-random
tick, the handedness of the settled history, and the Pisot boundary that
separates settling from spiraling.

Everything below is a machine-checked theorem, verified by the Lean 4 kernel
against Mathlib — with one clearly-marked exception, the numerical companion in
[`diffraction/`](./diffraction). The repository's claim is stated in **Scope**,
and it is an identity, not an analogy: this arithmetic is not proposed as a
model of time. It is proposed as what time is.

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

5. **The settled history is handed.** For the Padovan substitution
   `s : a ↦ b, b ↦ c, c ↦ ab` (incidence matrix of characteristic polynomial
   `x³ − x − 1`), every occurrence of `a` in any iterate from any seed is
   immediately followed by `b` (`Time.Padovan.every_a_followed_by_b` in
   `Chirality.lean`); consequently `ca` is a factor of the language while `ac`
   is a factor of **no** iterate from **any** seed — proved from the invariant,
   with no enumeration (`Time.Padovan.chirality`). Read backwards, the settled
   word is provably a different object. Moreover **no factor of length ≥ 4 of
   any iterate `S^[n]`, from any seed and at any iterate (including `n = 0`),
   is a palindrome** (`ArithmeticOfTime.padovan_no_long_palindrome` in
   `Solution.lean`): for the seed `a` this is
   `Time.Padovan.no_long_palindromic_factor` — every factor of length ≤ 5 of a
   seed-`a` iterate lies in an explicit 57-word certificate
   (`Time.Padovan.factors_complete`), and that list contains no palindrome of
   length 4 or 5 — and every other seed reduces to the seed-`a` case by the
   index shift `S [a] = [b]`, `S [b] = [c]`; the short palindromic factors
   that do occur can be read off the same certificate. These are statements
   about factors of the iterates `S^[n] [x]`, not about an abstract subshift. Reflection
   asymmetry for this substitution's tiling space was found independently, by a
   different method, in Gähler (2026) — see the paper's citations.

6. **The marked origin.** Extending the mechanical word to integer indices,
   `sZ β n = ⌊(n+1)β⌋ − ⌊nβ⌋`, the word satisfies the exact reflection identity
   `sZ β (−n−1) = sZ β n` away from the integer-crossing indices
   (`Time.sZ_reflect` in `OriginDefect.lean`, with the unconditional ceiling
   form `Time.sZ_reflect_eq_ceil`), and carries a computable defect at the
   origin: `(sZ β (−1), sZ β 0) = (1, 0)` for `0 < β < 1`
   (`Time.origin_defect`). The origin — the unique lattice hit `0·β ∈ ℤ` — is
   marked in the word itself; `Time.sZ_natCast` ties the extension back to the
   `ℕ`-indexed word of `MechanicalWord.lean`.

## Scope: the claim

The position taken here is that **time is this arithmetic** — an identity, in
the same grammar as "heat is molecular motion," and earned the same way: by
coverage. The temporal invariants are, one by one, theorems of a single
structure. The tick is multiplication by a unit, and its contraction rate is
exact (`Time.tick_contraction`). The tick never repeats (the rotation is
irrational, `Time.aperiodic`), yet is never random (the word is balanced,
`Time.balanced`). And the settled history is *handed*: read backwards, it is
provably a different object — not by convention, but by theorem
(`Chirality.lean`). On this reading the history is one completed object; the
asymmetry of time is a property of the whole; and nothing needs to orient a
flow, because nothing flows — the "now" is where an observer sits in the
structure, with records on one side (the marked origin of
`OriginDefect.lean`).

Two kinds of statement appear in this repository, and the boundary between
them is kept explicit. **Theorems**: every mathematical claim in the Lean
modules compiles in the kernel; nothing rests on trust. **The
identification**: that physical time is this structure — rather than merely
being described by it — is an identification, the same kind of statement as
"the metric tensor is spacetime geometry." No experiment distinguishes an
exact description from an identity, so this is not a claim any theorem could
settle; it is validated the way every physical identification is validated,
through the measured consequences of the framework it belongs to (see [`paper/`](./paper) and the companion deposits, e.g. doi:10.5281/zenodo.20417378). The mathematics stands regardless. The claim is which
thing it is.

## Build

```
lake exe cache get   # fetch the prebuilt Mathlib cache
lake build           # compiles the ten project modules
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
| `Chirality.lean` | the Padovan factor language is chiral: `ca` occurs, `ac` never; no palindromic factor of length ≥ 4 in any iterate from the seed `a` (extended to every seed and every iterate in `Solution.lean`) |
| `OriginDefect.lean` | the ℤ-indexed mechanical word: exact reflection identity off the lattice hits, and the marked origin defect `(1, 0)` |

## Paper

[`paper/`](./paper) holds the LaTeX source of the companion paper, *The
Arithmetic of Time*, which states exactly what this repository proves at its
honest tier — kernel-verified results with their Lean declaration names,
classical results cited, the diffraction picture labeled computed — and closes
with a list of natural formalization targets (the Sturmian converse, Pisot's
theorem, Siegel minimality).

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
