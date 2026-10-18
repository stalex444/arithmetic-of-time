module
public import PdtQuarticSeparation

@[expose] public section

/-!
# Residence in a fixed quartic arithmetic window

The quartic unit acts invertibly on integer power-basis coordinates. A record
whose positive real embedding is nonzero eventually exceeds any fixed bound
under forward ticks. A record whose contracting real embedding is nonzero
eventually exceeds any fixed bound under inverse ticks. These are statements
about fixed arithmetic windows and unit dynamics; no physical time direction
or invariant physical observation window is selected here.
-/

namespace PDT.QuarticWindowDynamics

open PDT.RecordBoundary

noncomputable section

/-- Multiplication by the quartic unit, using t^4 = t + 1. -/
def tick4 (p : Quad) : Quad := (p.2.2.2, p.1 + p.2.2.2, p.2.1, p.2.2.1)

theorem tick4_untick4 (p : Quad) : tick4 (untick4 p) = p := by
  rcases p with ⟨a, b, c, d⟩
  simp [tick4, untick4]

theorem untick4_tick4 (p : Quad) : untick4 (tick4 p) = p := by
  rcases p with ⟨a, b, c, d⟩
  simp [tick4, untick4]

theorem embed4_tick {F : Type*} [CommRing F] {t : F}
    (ht : t ^ 4 = t + 1) (p : Quad) :
    embed4 t (tick4 p) = t * embed4 t p := by
  simp only [embed4, tick4, Int.cast_add]
  linear_combination -(p.2.2.2 : F) * ht

theorem embed4_tick_iter {F : Type*} [CommRing F] {t : F}
    (ht : t ^ 4 = t + 1) (p : Quad) (n : ℕ) :
    embed4 t (tick4^[n] p) = t ^ n * embed4 t p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', embed4_tick ht, ih, pow_succ]
      ring

/-- The same coefficient vector satisfies both real-coordinate bounds. -/
def Within (q s H K : ℝ) (p : Quad) : Prop :=
  |embed4 q p| ≤ H ∧ |embed4 s p| ≤ K

/-- A second explicit quartic unit, with an integer-polynomial inverse. -/
theorem window_unit_inverse {F : Type*} [CommRing F] {t : F}
    (ht : t ^ 4 = t + 1) : (t ^ 2 - 1) * (t ^ 3 + t - 1) = 1 := by
  linear_combination t * ht

theorem window_unit_positive_contracts {q : ℝ} (hq : q ^ 4 = q + 1)
    (hq1 : 1 < q) : 0 < |q ^ 2 - 1| ∧ |q ^ 2 - 1| < 1 := by
  have hlt := PDT.SalemFamily.Q_lt hq
  have hsqlo : 1 < q ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hq1) (by linarith : 0 < q + 1)]
  have hsqhi : q ^ 2 < 2 := by
    nlinarith [mul_pos (sub_pos.mpr hlt) (by linarith : 0 < 5 / 4 + q)]
  rw [abs_of_pos (by linarith : 0 < q ^ 2 - 1)]
  constructor <;> linarith

theorem window_unit_negative_contracts {s : ℝ} (hslow : -1 < s)
    (hsneg : s < 0) : 0 < |s ^ 2 - 1| ∧ |s ^ 2 - 1| < 1 := by
  have hsqlo : 0 < s ^ 2 := sq_pos_of_ne_zero (ne_of_lt hsneg)
  have hsqhi : s ^ 2 < 1 := by
    nlinarith [mul_pos (by linarith : 0 < 1 - s) (by linarith : 0 < 1 + s)]
  rw [abs_of_neg (by linarith : s ^ 2 - 1 < 0)]
  constructor <;> linarith

theorem scaled_powers_eventually_exceed {a b : ℝ} (ha : 1 < a)
    (hb : 0 < b) (H : ℝ) : ∃ N : ℕ, ∀ n ≥ N, H < a ^ n * b := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (H / b) ha
  refine ⟨N, fun n hn => ?_⟩
  apply (div_lt_iff₀ hb).mp
  exact hN.trans_le (pow_le_pow_right₀ ha.le hn)

theorem forward_eventually_exceeds {q : ℝ} (hq : q ^ 4 = q + 1)
    (hq1 : 1 < q) {p : Quad} (hp : embed4 q p ≠ 0) (H : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, H < |embed4 q (tick4^[n] p)| := by
  obtain ⟨N, hN⟩ := scaled_powers_eventually_exceed hq1 (abs_pos.mpr hp) H
  refine ⟨N, fun n hn => ?_⟩
  rw [embed4_tick_iter hq, abs_mul, abs_pow, abs_of_pos (by linarith : 0 < q)]
  exact hN n hn

theorem backward_eventually_exceeds {s : ℝ} (hs : s ^ 4 = s + 1)
    (hs0 : 0 < |s|) (hs1 : |s| < 1) {p : Quad}
    (hp : embed4 s p ≠ 0) (K : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, K < |embed4 s (untick4^[n] p)| := by
  obtain ⟨N, hN⟩ := scaled_powers_eventually_exceed
    ((one_lt_inv₀ hs0).2 hs1) (abs_pos.mpr hp) K
  refine ⟨N, fun n hn => ?_⟩
  rw [embed4_untick_iter hs, abs_mul, abs_pow, abs_inv]
  exact hN n hn

/-- Both tails of a unit orbit leave every fixed two-real window. -/
theorem both_tails_exit {q s : ℝ} (hq : q ^ 4 = q + 1) (hq1 : 1 < q)
    (hs : s ^ 4 = s + 1) (hs0 : 0 < |s|) (hs1 : |s| < 1)
    {p : Quad} (hpq : embed4 q p ≠ 0) (hps : embed4 s p ≠ 0)
    (H K : ℝ) : ∃ N : ℕ, ∀ n ≥ N,
      ¬ Within q s H K (tick4^[n] p) ∧
      ¬ Within q s H K (untick4^[n] p) := by
  obtain ⟨A, hA⟩ := forward_eventually_exceeds hq hq1 hpq H
  obtain ⟨B, hB⟩ := backward_eventually_exceeds hs hs0 hs1 hps K
  refine ⟨max A B, fun n hn => ⟨?_, ?_⟩⟩
  · intro h
    exact (not_le.mpr (hA n ((le_max_left A B).trans hn))) h.1
  · intro h
    exact (not_le.mpr (hB n ((le_max_right A B).trans hn))) h.2

/-- Each half of the unit orbit visits the fixed window at only finitely many indices. -/
theorem finite_residence {q s : ℝ} (hq : q ^ 4 = q + 1) (hq1 : 1 < q)
    (hs : s ^ 4 = s + 1) (hs0 : 0 < |s|) (hs1 : |s| < 1)
    {p : Quad} (hpq : embed4 q p ≠ 0) (hps : embed4 s p ≠ 0) (H K : ℝ) :
    Set.Finite {n : ℕ | Within q s H K (tick4^[n] p)} ∧
    Set.Finite {n : ℕ | Within q s H K (untick4^[n] p)} := by
  obtain ⟨N, hN⟩ := both_tails_exit hq hq1 hs hs0 hs1 hpq hps H K
  constructor
  · apply (Set.finite_Iio N).subset
    intro n hn
    exact lt_of_not_ge (fun hnN => (hN n hnN).1 hn)
  · apply (Set.finite_Iio N).subset
    intro n hn
    exact lt_of_not_ge (fun hnN => (hN n hnN).2 hn)

/-- Nonzero integer coordinates suffice: irreducibility supplies nonzero evaluations. -/
theorem nonzero_finite_residence {q s : ℝ} (hq : q ^ 4 = q + 1)
    (hq1 : 1 < q) (hs : s ^ 4 = s + 1) (hslow : -1 < s) (hsneg : s < 0)
    {p : Quad} (hp : p ≠ 0) (H K : ℝ) :
    Set.Finite {n : ℕ | Within q s H K (tick4^[n] p)} ∧
    Set.Finite {n : ℕ | Within q s H K (untick4^[n] p)} := by
  apply finite_residence hq hq1 hs
    (abs_pos.mpr (ne_of_lt hsneg))
    (by rw [abs_of_neg hsneg]; linarith)
    (PDT.QuarticSeparation.embed4_ne_zero hq hp)
    (PDT.QuarticSeparation.embed4_ne_zero hs hp)

/-- The second unit contracts both real places and expands at the complex place. -/
theorem window_unit_complex_expands {q s : ℝ} {z : ℂ}
    (hq : q ^ 4 = q + 1) (hq1 : 1 < q) (hs : s ^ 4 = s + 1)
    (hslow : -1 < s) (hsneg : s < 0) (hz : z ^ 4 = z + 1) (him : z.im ≠ 0) :
    1 < ‖z ^ 2 - 1‖ := by
  have hqs : q ≠ s := by linarith
  have hbound := PDT.QuarticSeparation.norm_product_ge_one hq hs hqs hz him
    (-1, 0, 1, 0) (by decide)
  simp only [embed4, Int.cast_neg, Int.cast_one, Int.cast_zero, zero_mul,
    one_mul, add_zero] at hbound
  have hqU := window_unit_positive_contracts hq hq1
  have hsU := window_unit_negative_contracts hslow hsneg
  have hprod : |q ^ 2 - 1| * |s ^ 2 - 1| < 1 := by
    nlinarith [mul_lt_mul_of_pos_right hqU.2 hsU.1]
  have hprod0 : 0 ≤ |q ^ 2 - 1| * |s ^ 2 - 1| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hbound' : 1 ≤ |q ^ 2 - 1| * |s ^ 2 - 1| * ‖z ^ 2 - 1‖ ^ 2 := by
    simpa only [sub_eq_add_neg, add_comm] using hbound
  by_contra h
  have hnorm : ‖z ^ 2 - 1‖ ≤ 1 := le_of_not_gt h
  have hsq : ‖z ^ 2 - 1‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (z ^ 2 - 1)]
  nlinarith [mul_le_mul_of_nonneg_left hsq hprod0]

end
end PDT.QuarticWindowDynamics

#print axioms PDT.QuarticWindowDynamics.tick4
#print axioms PDT.QuarticWindowDynamics.tick4_untick4
#print axioms PDT.QuarticWindowDynamics.untick4_tick4
#print axioms PDT.QuarticWindowDynamics.embed4_tick
#print axioms PDT.QuarticWindowDynamics.embed4_tick_iter
#print axioms PDT.QuarticWindowDynamics.Within
#print axioms PDT.QuarticWindowDynamics.window_unit_inverse
#print axioms PDT.QuarticWindowDynamics.window_unit_positive_contracts
#print axioms PDT.QuarticWindowDynamics.window_unit_negative_contracts
#print axioms PDT.QuarticWindowDynamics.scaled_powers_eventually_exceed
#print axioms PDT.QuarticWindowDynamics.forward_eventually_exceeds
#print axioms PDT.QuarticWindowDynamics.backward_eventually_exceeds
#print axioms PDT.QuarticWindowDynamics.both_tails_exit
#print axioms PDT.QuarticWindowDynamics.finite_residence
#print axioms PDT.QuarticWindowDynamics.nonzero_finite_residence
#print axioms PDT.QuarticWindowDynamics.window_unit_complex_expands
