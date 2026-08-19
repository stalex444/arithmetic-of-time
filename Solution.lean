import PisotBoundary
import MechanicalWord

/-!
# Solution: proved versions of the Challenge declarations

Each declaration below has exactly the statement of its `Challenge.lean`
counterpart. The proofs are supplied by the project modules `PisotBoundary`
(the settle/spiral dichotomy, by an elementary Vieta reduction on the
conjugate pair) and `MechanicalWord` (the Sturmian tick word), where
`ArithmeticOfTime.tick` is definitionally `Time.m`.
-/

namespace ArithmeticOfTime

theorem cubic_conj_norm_lt_one (z : ℂ) (hz : z ^ 3 = z + 1) (him : z.im ≠ 0) :
    ‖z‖ < 1 :=
  Time.cubic_conj_norm_lt_one z hz him

theorem quartic_conj_norm_gt_one (w : ℂ) (hw : w ^ 4 = w + 1) (him : w.im ≠ 0) :
    1 < ‖w‖ :=
  Time.quartic_conj_norm_gt_one w hw him

theorem pisot_boundary_dichotomy
    (z : ℂ) (hz : z ^ 3 = z + 1) (hzim : z.im ≠ 0)
    (w : ℂ) (hw : w ^ 4 = w + 1) (hwim : w.im ≠ 0) :
    ‖z‖ < 1 ∧ 1 < ‖w‖ :=
  Time.pisot_boundary_dichotomy z hz hzim w hw hwim

noncomputable def tick (β : ℝ) (n : ℕ) : ℤ := ⌊((n : ℝ) + 1) * β⌋ - ⌊(n : ℝ) * β⌋

theorem tick_two_valued (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    tick β n = 0 ∨ tick β n = 1 := by
  simpa [tick, Time.m] using Time.m_mem β hβ0 hβ1 n

theorem tick_density (β : ℝ) :
    Filter.Tendsto (fun N : ℕ => ((∑ k ∈ Finset.range N, tick β k : ℤ) : ℝ) / (N : ℝ))
      Filter.atTop (nhds β) := by
  simpa [tick, Time.m] using Time.density_tendsto β

theorem tick_aperiodic (β : ℝ) (hβ : Irrational β) :
    ¬ ∃ p : ℕ, 0 < p ∧ ∀ n : ℕ, tick β (n + p) = tick β n := by
  simpa [tick, Time.m] using Time.aperiodic β hβ

theorem tick_balanced (β : ℝ) (L i j : ℕ) :
    |(∑ k ∈ Finset.range L, tick β (i + k)) - (∑ k ∈ Finset.range L, tick β (j + k))| ≤ 1 := by
  simpa [tick, Time.m] using Time.balanced β L i j

end ArithmeticOfTime
