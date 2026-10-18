# The Arithmetic of Time

A Lean 4 formalization of the mathematics of time — the individuation of
moments, an arithmetic arrow of irreversibility, an aperiodic-but-not-random
tick, the handedness of the settled history, and the Pisot boundary that
separates settling from spiraling.

Everything below is a machine-checked theorem, verified by the Lean 4 kernel
against Mathlib — with clearly-marked exceptions: the numerical companion in
[`diffraction/`](./diffraction), two computations labelled where they occur,
the cited results, and the identification stated in **Scope**. The
repository's claim is stated in **Scope**, and it is an identity, not an
analogy: this arithmetic is not proposed as a model of time. It is proposed
as what time is.

This is version 2 of the repository. Version 1, commit `c48eb12`, is
registered as PALOMAR-2026-08-19-000006, and the registered record compares
three statements at `c48eb12`: `ArithmeticOfTime.padovan_a_forces_b`,
`ArithmeticOfTime.padovan_chirality` and
`ArithmeticOfTime.padovan_no_long_palindrome`, over the definitions
`ArithmeticOfTime.s` and `ArithmeticOfTime.S`. Version 2 is new commits to this
repository, not a registry submission, and its compared surface
(`comparator.json`, `Challenge.lean`, `Solution.lean`) is the same three
statements, unchanged. The uniqueness results of item 1 below are registered
separately, as PALOMAR-2026-10-18-000019
([stalex444/arithmetic-of-time-slowest-clock](https://github.com/stalex444/arithmetic-of-time-slowest-clock)
at `49eafbab4af8899b2a66469697bf74683a88ce87`), which compares
`padovan_minimal_unique`, `padovan_eigenvalue_unique`,
`padovan_matrix_unique`, `pisot_ge_plastic` and `padovan_rules_chiral` over the
definitions `s`, `mir`, `inc` and `sub`; the same five statements, over the same
definitions, are proved here in `Supplement.lean`. Everything else in this
repository is public and kernel-checked but not compared. The additions come
first; the version-1 account follows it unchanged except where a fact has moved.

## New in version 2

1. **The slowest settling clock is unique, and it is handed.** The slowest
   settling clock on at most three letters is unique up to mirror image, and
   it is chiral: the arrow is forced, only its direction — one bit — is free.
   Precisely: let `σ` be a substitution on `k ≤ 3` letters and `θ > 1` a real
   eigenvalue of its incidence matrix that is a Pisot number (every other root
   of its minimal polynomial strictly inside the unit circle). Then `ρ ≤ θ`,
   and `θ = ρ` exactly when, after renaming the letters, `σ` is the Padovan
   substitution `a ↦ b, b ↦ c, c ↦ ab` or its mirror `c ↦ ba`
   (`ArithmeticOfTime.padovan_minimal_unique`). Neither primitivity nor the
   unit property is assumed. The classification holds for every real
   eigenvalue, with no Pisot hypothesis (`padovan_eigenvalue_unique`), and at
   the level of matrices: a `3 × 3` matrix over `ℕ` with characteristic
   polynomial `x³ − x − 1` is the Padovan matrix up to one simultaneous
   permutation of rows and columns (`padovan_matrix_unique`). Both minimal
   rules are chiral, in opposite directions: under the Padovan rule `ca`
   occurs and `ac` never does; under its mirror the reverse
   (`padovan_rules_chiral`). The two rules have the same matrix, so the same
   inflation factor and the same rate; they differ only in the order of the
   two letters in the image of `c`. That order is the one free bit.

   The bound `ρ ≤ θ` is Siegel's theorem (1944), which holds in every degree,
   restricted here to degree at most three (`pisot_ge_plastic`); it is not
   new, and it is proved here through the minimal Mahler measures of the
   registered entry PALOMAR-2026-08-31-000004. That the substitution with
   the fewest letters associated with the smallest Pisot number is unique up
   to reversal and relabelling was observed by Mercat (2020); the statement
   here is a kernel-checked classification over every substitution on at most
   three letters. The proofs are in `SlowestClock.lean`; the five statements
   named in this item are stated and proved in `Supplement.lean`, and they are
   the compared statements of PALOMAR-2026-10-18-000019, not of this
   repository.

2. **The threshold is four letters, not four ticks.** Orientation can be read
   from every factor of length at least four, and not from every factor of
   length three. The palindrome `aba` is a factor of an iterate from the seed
   `a` (`padovan_length_three_orientation_ambiguity`); if a word of length at
   least four is a factor of an iterate from some seed, its reversal is a
   factor of no iterate from any seed
   (`padovan_reversal_forbidden_of_four_le`); together,
   `padovan_exact_orientation_threshold_four`. All three are in
   `Supplement.lean` and are not compared. The four counts letters of the word,
   not substitution steps (`PdtFourTickThreshold.lean`).

3. **The rate identity.** For real `ρ > 0` and complex `σ ≠ 0` with
   `ρ · |σ|² = 1`, `−log |σ| = ½ log ρ` (`rate_eq_half_log`). For the Padovan
   matrix, whose determinant is `1`, `ρ` is the Perron root and `σ` either
   complex eigenvalue, so the decay rate of the non-Perron modes is fixed by
   the same matrix that fixes the inflation factor. The identity is
   elementary and is not compared; nor is its application to the Padovan
   matrix (`PdtArrowRate.lean`).

4. **The `ρQ` substitution.** The tensor of the Padovan substitution with the
   quartic substitution `0 ↦ 1, 1 ↦ 2, 2 ↦ 3, 3 ↦ 01` is a substitution on
   twelve letters whose incidence matrix has characteristic polynomial
   `x¹² − 3x⁹ − 2x⁸ + 2x⁶ − x⁵ − 3x⁴ − x³ + x − 1`, the minimal polynomial of
   `ρQ` (`rhoQ_substitution_charpoly`), and its factor language is chiral:
   `[(1, 1), (0, 0)]` is a factor of an iterate while its reversal is a factor
   of no iterate from any seed (`rhoQ_chirality`). The tensor is the
   direct-product construction (cf. Lind, Bull. AMS 9 (1983), Theorem 2);
   only this instance is stated, and the general product lemma is not
   claimed. Primitivity of the twelve-letter matrix was checked by
   computation and is not proved here. Neither statement is compared.

5. **Mirrors.** For any substitution on any alphabet, every iterate of its
   mirror (every image block read backwards) from a one-letter seed is the
   reversal of the corresponding iterate (`iterate_mir_seed`); mirroring both
   factors of a tensor reverses every iterate of the product
   (`iterate_tens_mir`); and the two single mirrors are mutual reversals
   (`single_mirrors_reverse`). These are elementary list identities, not
   compared; they are what makes the one bit of item 1 a reversal of the whole
   history (`PdtMirrorTensor.lean`).

6. **The distinguished slope is irrational.** For `ρ` the real root of
   `x³ − x − 1` and `w` a non-real root of `x⁴ − x − 1`, the slope
   `β = log ‖w‖ / (½ log ρ)` is irrational (`Time.beta_irrational` in
   `BetaIrrational.lean`, with the multiplicative form
   `Time.normSq_pow_ne_rho_pow`), so the aperiodicity theorem
   `Time.aperiodic` applies to it. This is a theorem of the repository, not a
   compared statement; that `0 < β < 1` is not proved there.

The repository also carries the supporting modules the companion paper cites
(trace-form signatures, the joint `ρQ` clock, record windows at the
cubic/quartic boundary); they are listed under **Build** and are not compared.

## What is proved (carried over from version 1)

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
   `settling ⟺ Pisot` fact for the two polynomials; it does **not** by itself
   prove Siegel's theorem that `ρ` is the *smallest* Pisot number. Siegel's
   theorem restricted to degree at most three is proved in version 2 (**New in
   version 2**, item 1); the general case needs Pisot theory outside Mathlib.

5. **The settled history is handed.** For the Padovan substitution
   `s : a ↦ b, b ↦ c, c ↦ ab` (incidence matrix of characteristic polynomial
   `x³ − x − 1`), every occurrence of `a` in any positive iterate
   `S^[n+1] [x]`, from any seed, is immediately followed by `b`
   (`Time.Padovan.every_a_followed_by_b` in `Chirality.lean`); consequently
   `ca` is a factor of an iterate (`S^[5] [a] = cab`) while `ac` is a factor
   of **no** iterate from **any** seed — the `ac` direction proved from the
   invariant, with no enumeration (`Time.Padovan.chirality`). Read backwards, the settled
   word is provably a different object. Moreover **no factor of length ≥ 4 of
   any iterate `S^[n]`, from any seed and at any iterate (including `n = 0`),
   is a palindrome** (`ArithmeticOfTime.padovan_no_long_palindrome` in
   `Solution.lean`): for the seed `a` this is
   `Time.Padovan.no_long_palindromic_factor` — every factor of length ≤ 5 of a
   seed-`a` iterate lies in an explicit 57-word certificate
   (`Time.Padovan.factors_complete`), and that list contains no palindrome of
   length 4 or 5 — and every other seed reduces to the seed-`a` case by the
   index shift `S [a] = [b]`, `S [b] = [c]`; the short palindromic factors
   all lie in the same certificate (which factors actually occur is checked
   outside the kernel and is not needed by any theorem). These are statements
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
lake build           # compiles the 44 project modules
```

Toolchain `leanprover/lean4:v4.35.0-rc2`, Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55` (pinned in `lean-toolchain`,
`lakefile.toml` and `lake-manifest.json`). The kernel check of
`PdtMahlerBox.lean` takes several minutes. `python3 scripts/check_axioms.py`
reruns the axiom audit of the **Rigor note**. The project modules are:

**The compared surface**

| Module | Content |
| --- | --- |
| `Challenge.lean` | the three compared statements of PALOMAR-2026-08-19-000006, as registered at `c48eb12`, with `sorry` placeholders |
| `Solution.lean` | the same three statements, proved, with an in-build axiom audit |

**Version 1**

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

**New in version 2**

| Module | Content |
| --- | --- |
| `Supplement.lean` | results of version 2 stated over the compared vocabulary and the definitions `mir`, `inc`, `sub` and `tens`, proved, not compared: the five uniqueness statements registered as PALOMAR-2026-10-18-000019, the exact orientation threshold and its two halves, the mirror identities, the rate identity, and the twelve-letter characteristic polynomial and chirality |
| `SlowestClock.lean` | Siegel's bound in degree ≤ 3; the matrix and substitution classifications; the slowest clock on at most three letters |
| `BetaIrrational.lean` | the distinguished slope `β = log ‖w‖ / (½ log ρ)` is irrational |
| `PdtFourTickThreshold.lean` | the exact orientation threshold: `aba` at length three, forbidden reversal from length four |
| `PdtArrowRate.lean` | `ρ·|σ|² = 1` forces `−log |σ| = ½ log ρ` |
| `PdtMirrorTensor.lean` | mirroring reverses iterates; mirror equivariance of the tensor of two substitutions |
| `PdtRhoQChirality.lean` | the twelve-letter `ρQ` substitution: successor invariant and chirality |
| `PdtCharpolyTensor.lean` | its incidence matrix has characteristic polynomial the minimal polynomial of `ρQ` |
| `PdtRulerMinpoly.lean` | the minimal polynomial of `ρQ`, of degree 12; `ℚ(ρQ) = ℚ(ρ, Q)` |
| `PdtChirality.lean`, `PdtIrreducible.lean`, `PdtPisotBoundary.lean`, `PdtCommitment.lean`, `Sturmian.lean` | the version-1 Padovan, irreducibility, Pisot-boundary, settling and mechanical-word results in the namespaces the new modules import |
| `PdtNormFloor.lean` | the integrality floor `1 ≤ |σ₁(x)|·‖σ₂(x)‖²` on all of `ℤ[ρ]`, and its invariance under one tick |
| `PdtSalemFamily.lean` | the Bedford–Kim family `x^(n+1)(x³ − x − 1) + (x³ + x² − 1)`: its roots below `ρ` increase to `ρ`, with Lehmer's polynomial at `n = 7`; a second conjugate of `ρQ` outside the unit circle |
| `PdtMahler.lean`, `PdtMahlerBox.lean`, `PdtMahlerMain.lean`, `PdtMahlerTheta.lean`, `PdtMahlerWindow.lean` | the minimal Mahler measures in degrees 2, 3, 4, from registered entry PALOMAR-2026-08-31-000004 |
| `PdtSignature.lean`, `PdtSignatureRho.lean`, `PdtTraceLink.lean`, `PdtTraceSignature.lean`, `PdtTraceCompositum.lean` | the trace forms: signatures `(3, 1)`, `(2, 1)` and, on the compositum `ℚ(ρ, Q)`, `(7, 5)` |
| `PdtJointClock.lean`, `PdtJointClockIrreducible.lean` | the joint `ρQ` tick on the compositum recovers both factor ticks and has no proper invariant subspace |
| `PdtCubicQuarticBridge.lean` | no nonzero additive intertwiner between the cubic and quartic ticks |
| `PdtRecordBoundary.lean`, `PdtQuarticSeparation.lean`, `PdtQuarticWindowDynamics.lean` | record windows: uniform separation on the cubic side; on the quartic side, nonzero records arbitrarily close to zero in the same window, and separation once both real embeddings are bounded |

## Paper

[`paper/`](./paper) holds the LaTeX source of the companion paper, *The
Arithmetic of Time*, which states exactly what this repository proves at its
honest tier — kernel-verified results with their Lean declaration names,
classical results cited, the diffraction picture labeled computed — and closes
with a list of natural formalization targets (the Sturmian converse, Pisot's
theorem, Siegel minimality in every degree).

## Numerical companion: diffraction

[`diffraction/`](./diffraction) pictures the *spectral* face of the mechanical
word: laid out as positions and diffracted, it shows sharp Bragg peaks at the
incommensurate module `m + nβ` — quasicrystalline order — with the
word's crystal-forbidden peak at `β` growing `∝ N` while a Poisson gas of the
same density stays flat. That folder is **computation, not proof**; the underlying
pure-point property is a theorem of the model-set literature (Hof 1995;
Baake–Grimm 2013), cited there.

## Rigor note

Every theorem's axiom dependency is a subset of
`{propext, Classical.choice, Quot.sound}` — the standard classical foundation of
Mathlib. There is **no `sorry`**, **no `native_decide`**, and **no custom
axiom** anywhere in the proved development (`Challenge.lean` states the
compared theorems with `sorry` placeholders, by the registry's challenge
format; `Solution.lean` proves them all); the irrationality of the slope in
`MechanicalWord` (which lies beyond Mathlib) is carried as an explicit
hypothesis, never assumed as an axiom. For the distinguished slope `β` it is
proved, in `BetaIrrational.lean`. You can reproduce the audit with
`#print axioms Time.balanced` (and likewise for any theorem above), or for
every theorem and lemma at once with `python3 scripts/check_axioms.py`.

## License

MIT — see [`LICENSE`](./LICENSE).
