import MechanicalWord

/-!
# OriginDefect — the ℤ-indexed mechanical word: reflection identity and the origin defect

`MechanicalWord` certifies the ℕ-indexed mechanical (Beatty) word
`m β n = ⌊(n+1)β⌋ − ⌊nβ⌋`. This sibling module extends the word to ℤ by the
same floor formula (`sZ`) and kernel-verifies the origin-defect floor
identities:

* **AGREEMENT** (`sZ_natCast`): on ℕ the ℤ-word IS the banked word `m β`.
* **REFLECTION** (`sZ_reflect`, `sZ_reflect_irrational`, `sZ_reflect_nat`):
  `sZ β (−n−1) = sZ β n` whenever neither `nβ` nor `(n+1)β` is an integer —
  the engine is `⌊−x⌋ = −⌊x⌋ − 1` for non-integer `x`
  (`floor_neg_of_not_int`). For irrational `β` the non-integrality is
  automatic for every `n ∉ {0, −1}`, so the word reads the same at `n` and
  at `−n−1` for ALL `n ≥ 1`: reflection through `−1/2` fixes the word away
  from the origin.
* **THE ORIGIN DEFECT** (`origin_defect`): at the origin the reflection
  identity FAILS, in exactly one place and in the forced way:
  `(sZ β (−1), sZ β 0) = (1, 0)` for every slope `0 < β < 1`. The defect
  comes from `⌊0⌋ = 0` being a lattice hit: `0·β ∈ ℤ` is the one exempt
  index, and there `⌊−β⌋ = −1` while `⌊β⌋ = 0`.
* **REVERSAL = CEILING WORD** (`sZ_reflect_eq_ceil`): unconditionally —
  no hypotheses at all — `sZ β (−n−1) = ⌈(n+1)β⌉ − ⌈nβ⌉`: the time-reversed
  word is the ceiling variant of the same slope, via `⌊−x⌋ = −⌈x⌉`.

## Scope (what is proved here, and what is deliberately NOT)

* All statements quantify over an abstract slope `β` with the exact
  hypotheses displayed (`0 < β < 1`, non-integrality, or `Irrational β`).
  As in `MechanicalWord`, that any concrete slope of interest lies in
  `(0,1)` and is irrational is NOT proved here; the hypotheses are honestly
  carried, never discharged.
* The reading of `sZ` on negative `n` as "the past of the clock history",
  and of the origin defect as a marked-origin/arrow statement, is an
  interpretive identification — out of scope here. This module proves the
  floor identities only.
-/

namespace Time

noncomputable section

/-- The ℤ-indexed mechanical word of slope `β`, by the same floor formula
as the banked ℕ-word `m β`: `sZ β n = ⌊(n+1)·β⌋ − ⌊n·β⌋`. -/
noncomputable def sZ (β : ℝ) (n : ℤ) : ℤ := ⌊((n : ℝ) + 1) * β⌋ - ⌊(n : ℝ) * β⌋

/-- **AGREEMENT.** On ℕ-indices the ℤ-word is the banked mechanical word
`m β` of `MechanicalWord`. -/
theorem sZ_natCast (β : ℝ) (n : ℕ) : sZ β (n : ℤ) = m β n := by
  unfold sZ m
  push_cast
  ring_nf

/-- **The engine.** For non-integer `x`, `⌊−x⌋ = −⌊x⌋ − 1`. From
`⌊−x⌋ = −⌈x⌉` and `⌈x⌉ = ⌊x⌋ + 1` off the integers. -/
theorem floor_neg_of_not_int {x : ℝ} (hx : ∀ k : ℤ, x ≠ (k : ℝ)) :
    ⌊-x⌋ = -⌊x⌋ - 1 := by
  have hnot : x ∉ Set.range ((↑) : ℤ → ℝ) := by
    rintro ⟨k, hk⟩
    exact hx k hk.symm
  have hceil : ⌈x⌉ = ⌊x⌋ + 1 := (Int.ceil_eq_floor_add_one_iff_notMem x).2 hnot
  rw [Int.floor_neg, hceil]
  ring

/-- **REFLECTION (exact hypotheses).** `sZ β (−n−1) = sZ β n` whenever
neither `nβ` nor `(n+1)β` is an integer. -/
theorem sZ_reflect (β : ℝ) (n : ℤ)
    (h1 : ∀ k : ℤ, (n : ℝ) * β ≠ (k : ℝ))
    (h2 : ∀ k : ℤ, ((n : ℝ) + 1) * β ≠ (k : ℝ)) :
    sZ β (-n - 1) = sZ β n := by
  unfold sZ
  have ha : (((-n - 1 : ℤ) : ℝ) + 1) * β = -((n : ℝ) * β) := by push_cast; ring
  have hb : ((-n - 1 : ℤ) : ℝ) * β = -(((n : ℝ) + 1) * β) := by push_cast; ring
  rw [ha, hb, floor_neg_of_not_int h1, floor_neg_of_not_int h2]
  ring

/-- **REFLECTION (irrational slope).** For irrational `β` the
non-integrality hypotheses hold automatically at every `n ∉ {0, −1}`. -/
theorem sZ_reflect_irrational (β : ℝ) (hβ : Irrational β) (n : ℤ)
    (hn0 : n ≠ 0) (hn1 : n ≠ -1) : sZ β (-n - 1) = sZ β n := by
  apply sZ_reflect
  · intro k
    exact (hβ.intCast_mul hn0).ne_int k
  · intro k
    have he : ((n : ℝ) + 1) = ((n + 1 : ℤ) : ℝ) := by push_cast; ring
    rw [he]
    exact (hβ.intCast_mul (by omega : n + 1 ≠ 0)).ne_int k

/-- **REFLECTION, ℕ form.** For irrational `β`, `sZ β (−n−1) = sZ β n` for
every natural `n ≥ 1` — the canonical statement `s(−n−1) = s(n)`, `n ≥ 1`. -/
theorem sZ_reflect_nat (β : ℝ) (hβ : Irrational β) (n : ℕ) (hn : 1 ≤ n) :
    sZ β (-(n : ℤ) - 1) = sZ β (n : ℤ) :=
  sZ_reflect_irrational β hβ (n : ℤ) (by omega) (by omega)

/-- **THE ORIGIN DEFECT.** At the origin the reflection identity fails in
exactly the forced way: `(sZ β (−1), sZ β 0) = (1, 0)` for every slope
`0 < β < 1`. The exempt index is the lattice hit `0·β = 0 ∈ ℤ`, where
`⌊−β⌋ = −1` while `⌊β⌋ = 0`. -/
theorem origin_defect (β : ℝ) (h0 : 0 < β) (h1 : β < 1) :
    sZ β (-1) = 1 ∧ sZ β 0 = 0 := by
  have hfloor : ⌊β⌋ = 0 := by
    rw [Int.floor_eq_zero_iff, Set.mem_Ico]
    exact ⟨h0.le, h1⟩
  have hneg : ⌊-β⌋ = -1 := by
    rw [Int.floor_eq_iff]
    constructor
    · push_cast
      linarith
    · push_cast
      linarith
  constructor
  · unfold sZ
    have ha : (((-1 : ℤ) : ℝ) + 1) * β = 0 := by push_cast; ring
    have hb : ((-1 : ℤ) : ℝ) * β = -β := by push_cast; ring
    rw [ha, hb, Int.floor_zero, hneg]
    ring
  · unfold sZ
    have ha : (((0 : ℤ) : ℝ) + 1) * β = β := by push_cast; ring
    have hb : ((0 : ℤ) : ℝ) * β = 0 := by push_cast; ring
    rw [ha, hb, Int.floor_zero, hfloor]
    ring

/-- **REVERSAL = CEILING WORD (unconditional).** With no hypotheses at all,
`sZ β (−n−1) = ⌈(n+1)β⌉ − ⌈nβ⌉`: reading the word backwards from `−1`
produces the ceiling variant of the same slope, by `⌊−x⌋ = −⌈x⌉`. -/
theorem sZ_reflect_eq_ceil (β : ℝ) (n : ℤ) :
    sZ β (-n - 1) = ⌈((n : ℝ) + 1) * β⌉ - ⌈(n : ℝ) * β⌉ := by
  unfold sZ
  have ha : (((-n - 1 : ℤ) : ℝ) + 1) * β = -((n : ℝ) * β) := by push_cast; ring
  have hb : ((-n - 1 : ℤ) : ℝ) * β = -(((n : ℝ) + 1) * β) := by push_cast; ring
  rw [ha, hb, Int.floor_neg, Int.floor_neg]
  ring

end

end Time

/-! ### Axiom audit -/

#print axioms Time.sZ_natCast
#print axioms Time.floor_neg_of_not_int
#print axioms Time.sZ_reflect
#print axioms Time.sZ_reflect_irrational
#print axioms Time.sZ_reflect_nat
#print axioms Time.origin_defect
#print axioms Time.sZ_reflect_eq_ceil
