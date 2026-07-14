import Mathlib

/-!
# MechanicalWord — a mechanical (Sturmian) word is aperiodic but not random

For a real slope `β`, the **mechanical (Beatty) word** records, step after step,
the forward difference `m β n = ⌊(n+1)β⌋ − ⌊nβ⌋`. For `0 < β < 1` this is a
two-valued sequence, the canonical object of one-dimensional symbolic dynamics.
(Motivation: such a word models a discrete "tick" of duration
`⌊(n+1)β⌋ − ⌊nβ⌋` at step `n` — deterministic, yet non-repeating.) This module
certifies, in the kernel, the four properties that make the word
**deterministic, structured and non-repeating** — the mechanical/Sturmian
properties of a Beatty word of a general slope `β`:

* **T1 — TWO-VALUED** (`m_mem`): for `0 < β < 1`, every value is `0` or `1`;
  the word uses a binary alphabet, with no third symbol.
* **T2 — DENSITY = β** (`sum_m_eq`, `sum_m_bounds`, `density_tendsto`): the
  running 1-count telescopes exactly to `⌊Nβ⌋`, and the frequency of `1`'s
  converges to `β`. The long-run rate is the slope itself.
* **T3 — APERIODIC** (`aperiodic`): for irrational `β` the word has NO period —
  it never repeats (deterministic yet non-periodic).
* **T4 — BALANCED** (`balanced`): any two windows of the SAME length have
  1-counts differing by at most `1`. This is the precise "not random / maximally
  even" Sturmian balance property — the strongest single statement here.

The object is the **mechanical (Beatty) word** `m β : ℕ → ℤ`,
`m β n = ⌊(n+1)·β⌋ − ⌊n·β⌋`, taken for an abstract slope. Every proof reduces to
elementary `Int.floor` facts (`Int.floor_le`, `Int.lt_floor_add_one`,
`Int.le_floor`, `Int.floor_lt`); no symbolic-dynamics API is used.

## Scope (what is proved here, and what is deliberately NOT)

* This module certifies the WORD'S structure for a general real slope `β`,
  taken abstractly. Whether a particular `β` arises from any specific dynamical
  system is out of scope; every statement is about the word `m β`.
* The bounds `0 < β < 1` enter T1/T2 as hypotheses; they are not established
  here for any specific slope.
* Irrationality of `β` is a **hypothesis** in the aperiodicity statement T3
  (and the T4-adjacent statements), never a kernel step — it is honestly
  carried, not discharged. (For a concrete `β` presented as a ratio of
  logarithms of multiplicatively independent algebraic numbers, irrationality
  would follow from Baker's theorem, which is not in Mathlib.)

All statements quantify over the slope `β`, so they apply to any particular
slope the instant the scope facts above are supplied from outside.
-/

namespace Time

noncomputable section

/-- The mechanical (Beatty) **tick-duration word** of slope `β`:
`m β n = ⌊(n+1)·β⌋ − ⌊n·β⌋`. This is the duration of the `n`-th tick. -/
noncomputable def m (β : ℝ) (n : ℕ) : ℤ := ⌊((n : ℝ) + 1) * β⌋ - ⌊(n : ℝ) * β⌋

/-- The **cumulative floor** `cumFloor β N = ⌊N·β⌋`; the running 1-count of the
word telescopes to this (`sum_m_eq`). -/
noncomputable def cumFloor (β : ℝ) (n : ℕ) : ℤ := ⌊(n : ℝ) * β⌋

/-- The tick word is the forward difference of the cumulative floor:
`m β n = cumFloor β (n+1) − cumFloor β n`. -/
theorem m_eq_cumFloor (β : ℝ) (n : ℕ) : m β n = cumFloor β (n + 1) - cumFloor β n := by
  unfold m cumFloor
  push_cast
  ring_nf

/-! ## Elementary floor lemma (the engine behind two-valued and balance) -/

/-- **The floor-additivity dichotomy.** For all reals `a, b`,
`⌊a+b⌋` is either `⌊a⌋+⌊b⌋` or `⌊a⌋+⌊b⌋+1`. Elementary: the lower bound is
`Int.le_floor` from `⌊a⌋ ≤ a`, `⌊b⌋ ≤ b`; the upper bound is `Int.floor_lt`
from `a < ⌊a⌋+1`, `b < ⌊b⌋+1`. -/
theorem floor_add_cases (a b : ℝ) :
    ⌊a + b⌋ = ⌊a⌋ + ⌊b⌋ ∨ ⌊a + b⌋ = ⌊a⌋ + ⌊b⌋ + 1 := by
  have hlo : ⌊a⌋ + ⌊b⌋ ≤ ⌊a + b⌋ := by
    rw [Int.le_floor]
    push_cast
    have ha := Int.floor_le a
    have hb := Int.floor_le b
    linarith
  have hhi : ⌊a + b⌋ ≤ ⌊a⌋ + ⌊b⌋ + 1 := by
    have h : ⌊a + b⌋ < ⌊a⌋ + ⌊b⌋ + 2 := by
      rw [Int.floor_lt]
      push_cast
      have ha := Int.lt_floor_add_one a
      have hb := Int.lt_floor_add_one b
      linarith
    omega
  omega

/-! ## T1 — TWO-VALUED (the binary alphabet) -/

/-- **T1 — TWO-VALUED.** For a slope `0 < β < 1`, every tick duration is `0`
or `1`: `m β n ∈ {0, 1}`. From `⌊nβ + β⌋ − ⌊nβ⌋ ∈ {⌊β⌋, ⌊β⌋+1} = {0,1}`. -/
theorem m_mem (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    m β n = 0 ∨ m β n = 1 := by
  have hfβ : ⌊β⌋ = 0 := by
    rw [Int.floor_eq_zero_iff, Set.mem_Ico]; exact ⟨hβ0.le, hβ1⟩
  unfold m
  rw [show ((n : ℝ) + 1) * β = (n : ℝ) * β + β by ring]
  rcases floor_add_cases ((n : ℝ) * β) β with h | h
  · rw [h, hfβ]; left; omega
  · rw [h, hfβ]; right; omega

/-! ## T2 — DENSITY (telescoping identity, two-sided bound, and the limit) -/

/-- **T2 — telescoping identity.** The running 1-count telescopes exactly:
`∑_{k<N} m β k = ⌊N·β⌋ = cumFloor β N`. -/
theorem sum_m_eq (β : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, m β k = cumFloor β N := by
  induction N with
  | zero => simp [cumFloor]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, m_eq_cumFloor β n]
    omega

/-- **T2 — two-sided bound.** The running 1-count brackets `N·β`:
`⌊N·β⌋ ≤ N·β < ⌊N·β⌋ + 1`, written on the telescoped sum. -/
theorem sum_m_bounds (β : ℝ) (N : ℕ) :
    ((∑ k ∈ Finset.range N, m β k : ℤ) : ℝ) ≤ (N : ℝ) * β ∧
      (N : ℝ) * β < ((∑ k ∈ Finset.range N, m β k : ℤ) : ℝ) + 1 := by
  rw [sum_m_eq]
  unfold cumFloor
  exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

/-- **T2 — DENSITY = β.** The frequency of `1`'s converges to the slope:
`(∑_{k<N} m β k)/N → β` as `N → ∞`. Squeeze on
`β − 1/N < ⌊Nβ⌋/N ≤ β`. -/
theorem density_tendsto (β : ℝ) :
    Filter.Tendsto (fun N : ℕ => ((∑ k ∈ Finset.range N, m β k : ℤ) : ℝ) / (N : ℝ))
      Filter.atTop (nhds β) := by
  have hg : Filter.Tendsto (fun N : ℕ => β - 1 / (N : ℝ)) Filter.atTop (nhds β) := by
    have h0 : Filter.Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hc : Filter.Tendsto (fun _ : ℕ => β) Filter.atTop (nhds β) := tendsto_const_nhds
    simpa using hc.sub h0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hg tendsto_const_nhds
  · filter_upwards [Filter.eventually_gt_atTop 0] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    rw [sum_m_eq]
    unfold cumFloor
    rw [le_div_iff₀ hNpos]
    have key : (β - 1 / (N : ℝ)) * (N : ℝ) = β * (N : ℝ) - 1 := by field_simp
    rw [key]
    have hlt := Int.lt_floor_add_one ((N : ℝ) * β)
    nlinarith [hlt]
  · filter_upwards [Filter.eventually_gt_atTop 0] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [sum_m_eq]
    unfold cumFloor
    rw [div_le_iff₀ hNpos]
    have hle := Int.floor_le ((N : ℝ) * β)
    nlinarith [hle]

/-! ## T4 — BALANCED (the crown: "not random" / maximally even) -/

/-- **Windowed telescoping.** The 1-count of the length-`L` window starting at
`i` telescopes: `∑_{k<L} m β (i+k) = cumFloor β (i+L) − cumFloor β i`. -/
theorem window_sum (β : ℝ) (i L : ℕ) :
    ∑ k ∈ Finset.range L, m β (i + k) = cumFloor β (i + L) - cumFloor β i := by
  induction L with
  | zero => simp
  | succ l ih =>
    rw [Finset.sum_range_succ, ih, m_eq_cumFloor β (i + l)]
    have he : i + (l + 1) = (i + l) + 1 := by omega
    rw [he]
    omega

/-- **Every window count lies in `{⌊Lβ⌋, ⌊Lβ⌋+1}`.** For any start `i` and
length `L`, the window 1-count is `⌊Lβ⌋` or `⌊Lβ⌋+1`. From `floor_add_cases`
with `a = iβ`, `b = Lβ`. -/
theorem window_mem (β : ℝ) (i L : ℕ) :
    cumFloor β (i + L) - cumFloor β i = ⌊(L : ℝ) * β⌋ ∨
      cumFloor β (i + L) - cumFloor β i = ⌊(L : ℝ) * β⌋ + 1 := by
  unfold cumFloor
  rw [show ((i + L : ℕ) : ℝ) * β = (i : ℝ) * β + (L : ℝ) * β by push_cast; ring]
  rcases floor_add_cases ((i : ℝ) * β) ((L : ℝ) * β) with h | h
  · left; rw [h]; omega
  · right; rw [h]; omega

/-- **T4 — BALANCED.** Any two windows of the SAME length `L` have 1-counts
differing by at most `1`:
`|∑_{k<L} m β (i+k) − ∑_{k<L} m β (j+k)| ≤ 1`.
Both counts lie in `{⌊Lβ⌋, ⌊Lβ⌋+1}` (`window_mem`), so they differ by ≤ 1.
This is the precise Sturmian balance property — the word is maximally even. -/
theorem balanced (β : ℝ) (L i j : ℕ) :
    |(∑ k ∈ Finset.range L, m β (i + k)) - (∑ k ∈ Finset.range L, m β (j + k))| ≤ 1 := by
  rw [window_sum, window_sum]
  rcases window_mem β i L with hi | hi <;> rcases window_mem β j L with hj | hj <;>
    rw [hi, hj, abs_le] <;> omega

/-! ## T3 — APERIODIC (the word never repeats, for irrational slope) -/

/-- **T3 — APERIODIC.** For an irrational slope `β`, the tick word has NO
period: there is no `p > 0` with `m β (n+p) = m β n` for all `n`.

Proof: a period `p` forces the cumulative floor to be additive over the period,
`cumFloor β (n+p) = cumFloor β n + cumFloor β p` (induction on `n` via the
forward-difference recurrence), hence `cumFloor β (M·p) = M·cumFloor β p` for
all `M`. Comparing with the floor bracket `Mpβ < cumFloor β (M·p) + 1` gives
`M · Int.fract(pβ) < 1` for ALL `M`; but `Int.fract(pβ) > 0` (as `pβ` is
irrational), so this fails for large `M` (Archimedean). -/
theorem aperiodic (β : ℝ) (hβ : Irrational β) :
    ¬ ∃ p : ℕ, 0 < p ∧ ∀ n : ℕ, m β (n + p) = m β n := by
  rintro ⟨p, hp, hper⟩
  -- forward-difference recurrence transported by the period
  have hrec : ∀ n : ℕ,
      cumFloor β (n + p + 1) - cumFloor β (n + p) = cumFloor β (n + 1) - cumFloor β n := by
    intro n
    have h3 := hper n
    rw [m_eq_cumFloor β (n + p), m_eq_cumFloor β n] at h3
    exact h3
  -- additive over the period
  have hadd : ∀ n : ℕ, cumFloor β (n + p) = cumFloor β n + cumFloor β p := by
    intro n
    induction n with
    | zero => simp [cumFloor]
    | succ k ih =>
      have hr := hrec k
      have he : k + 1 + p = k + p + 1 := by omega
      rw [he]
      omega
  -- linear over multiples of the period
  have hlin : ∀ M : ℕ, cumFloor β (M * p) = (M : ℤ) * cumFloor β p := by
    intro M
    induction M with
    | zero => simp [cumFloor]
    | succ k ih =>
      have hstep := hadd (k * p)
      have he : (k + 1) * p = k * p + p := by ring
      rw [he, hstep, ih]
      push_cast
      ring
  -- the fractional part of `pβ`
  set c : ℤ := cumFloor β p with hc
  set φ : ℝ := (p : ℝ) * β - (c : ℝ) with hφ
  have hφ_nonneg : 0 ≤ φ := by
    rw [hφ, hc]
    simp only [cumFloor]
    have := Int.floor_le ((p : ℝ) * β)
    linarith
  have hφ_ne : φ ≠ 0 := by
    rw [hφ]
    intro h
    have heq : ((p : ℝ) * β) = (c : ℝ) := by linarith
    exact Irrational.ne_int (Irrational.natCast_mul hβ hp.ne') c heq
  have hφ_pos : 0 < φ := lt_of_le_of_ne hφ_nonneg (Ne.symm hφ_ne)
  -- for every `M`, `M·φ < 1`
  have hbound : ∀ M : ℕ, (M : ℝ) * φ < 1 := by
    intro M
    have hfl : ((M * p : ℕ) : ℝ) * β < (cumFloor β (M * p) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    rw [hlin M] at hfl
    rw [hφ]
    have hexp : (M : ℝ) * ((p : ℝ) * β - (c : ℝ)) = (M : ℝ) * (p : ℝ) * β - (M : ℝ) * (c : ℝ) := by
      ring
    rw [hexp]
    push_cast at hfl
    linarith [hfl]
  -- Archimedean contradiction
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / φ)
  have hb := hbound M
  rw [div_lt_iff₀ hφ_pos] at hM
  linarith

end

end Time
