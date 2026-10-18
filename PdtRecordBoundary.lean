module
public import PdtCommitment
public import PdtPisotBoundary
public import PdtSalemFamily

@[expose] public section

/-!
# Arithmetic record windows at the cubic/quartic boundary

The same criterion is used on both sides: read the complex embedding, and
bound the positive real embedding by a fixed H > 0. The cubic has a uniform
separation bound. For the quartic, inverse powers of its unit are nonzero
records approaching zero inside every such window. This rules out uniform
discreteness for this specified projection/window, not for all quartic
cut-and-project constructions or all Q-inflation tilings.

The negative real embedding grows along this quartic witness. Bounding that
additional coordinate excludes the tail. No identification of an embedding
coordinate with a physical dimension is assumed or concluded.
-/

namespace PDT.RecordBoundary

noncomputable section

abbrev Quad := ℤ × ℤ × ℤ × ℤ

def embed4 {K : Type*} [Ring K] (t : K) (p : Quad) : K :=
  p.1 + p.2.1 * t + p.2.2.1 * t ^ 2 + p.2.2.2 * t ^ 3

def untick4 (p : Quad) : Quad := (p.2.1 - p.1, p.2.2.1, p.2.2.2, p.1)

lemma quartic_ne_zero {K : Type*} [Field K] {t : K} (ht : t ^ 4 = t + 1) : t ≠ 0 := by
  intro h
  simp [h] at ht

lemma embed4_untick {K : Type*} [Field K] {t : K} (ht : t ^ 4 = t + 1)
    (p : Quad) : embed4 t (untick4 p) = t⁻¹ * embed4 t p := by
  have he : t * embed4 t (untick4 p) = embed4 t p := by
    simp only [embed4, untick4, Int.cast_sub]
    linear_combination (p.1 : K) * ht
  calc
    embed4 t (untick4 p) = t⁻¹ * (t * embed4 t (untick4 p)) := by
      rw [← mul_assoc, inv_mul_cancel₀ (quartic_ne_zero ht), one_mul]
    _ = t⁻¹ * embed4 t p := by rw [he]

lemma embed4_untick_iter {K : Type*} [Field K] {t : K} (ht : t ^ 4 = t + 1)
    (p : Quad) (n : ℕ) : embed4 t (untick4^[n] p) = (t⁻¹) ^ n * embed4 t p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', embed4_untick ht, ih, pow_succ]
    ring

def inverseUnit (n : ℕ) : Quad := untick4^[n] (1, 0, 0, 0)

lemma inverseUnit_embedding {K : Type*} [Field K] {t : K} (ht : t ^ 4 = t + 1)
    (n : ℕ) : embed4 t (inverseUnit n) = (t⁻¹) ^ n := by
  unfold inverseUnit
  rw [embed4_untick_iter ht]
  simp [embed4]

/-- For either degree, a record set uses one positive-real window and one
complex observable. This definition is independent of the coefficient type. -/
def recordWindow {A : Type*} (realPlace : A → ℝ) (complexPlace : A → ℂ)
    (H : ℝ) : Set ℂ := {w | ∃ p, |realPlace p| ≤ H ∧ complexPlace p = w}

def HasUniformGap (S : Set ℂ) : Prop :=
  ∃ d : ℝ, 0 < d ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → d ≤ ‖x - y‖

/-- The previously proved cubic separation bound applied to an absolute
window: pairwise real differences are bounded by 2H. -/
theorem cubic_window_uniform_gap {r : ℝ} {z : ℂ}
    (hr : r ^ 3 = r + 1) (hz : z ^ 3 = z + 1) (him : z.im ≠ 0)
    {H : ℝ} (hH : 0 < H) : HasUniformGap (recordWindow (PDT.embed r) (PDT.embed z) H) := by
  refine ⟨(2 * H) ^ (-(1 / 2) : ℝ), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  rintro x ⟨p, hp, rfl⟩ y ⟨q, hq, rfl⟩ hne
  have hpq : p ≠ q := by intro h; exact hne (congrArg (PDT.embed z) h)
  apply PDT.windowed_separation hr hz him hpq
  exact (abs_sub _ _).trans (by linarith)

lemma simultaneous_inverse_powers {r a H ε : ℝ}
    (hr : 1 < r) (ha : 1 < a) (hH : 0 < H) (hε : 0 < ε) :
    ∃ n : ℕ, (r⁻¹) ^ n < H ∧ (a⁻¹) ^ n < ε := by
  have hr0 : 0 < r := by linarith
  have ha0 : 0 < a := by linarith
  have hr1 : r⁻¹ < 1 := (inv_lt_one₀ hr0).2 hr
  have ha1 : a⁻¹ < 1 := (inv_lt_one₀ ha0).2 ha
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hH hr1
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε ha1
  refine ⟨max m k, ?_, ?_⟩
  · exact (pow_le_pow_of_le_one (inv_nonneg.mpr hr0.le) hr1.le (le_max_left m k)).trans_lt hm
  · exact (pow_le_pow_of_le_one (inv_nonneg.mpr ha0.le) ha1.le (le_max_right m k)).trans_lt hk

/-- A concrete sequence of nonzero quartic records approaches zero while
remaining inside any prescribed positive-real window. -/
theorem quartic_arbitrarily_close_records {q : ℝ} {z : ℂ}
    (hq : q ^ 4 = q + 1) (hq1 : 1 < q) (hz : z ^ 4 = z + 1) (him : z.im ≠ 0)
    {H ε : ℝ} (hH : 0 < H) (hε : 0 < ε) :
    ∃ n : ℕ, |embed4 q (inverseUnit n)| < H ∧
      embed4 z (inverseUnit n) ≠ 0 ∧ ‖embed4 z (inverseUnit n)‖ < ε := by
  obtain ⟨n, hn, hzn⟩ := simultaneous_inverse_powers hq1
    (PDT.quartic_conj_norm_gt_one z hz him) hH hε
  refine ⟨n, ?_, ?_, ?_⟩
  · rw [inverseUnit_embedding hq, abs_of_pos (pow_pos (inv_pos.mpr (by linarith)) n)]
    exact hn
  · rw [inverseUnit_embedding hz]
    exact pow_ne_zero n (inv_ne_zero (quartic_ne_zero hz))
  · simpa only [inverseUnit_embedding hz, norm_pow, norm_inv] using hzn

theorem quartic_window_no_uniform_gap {q : ℝ} {z : ℂ}
    (hq : q ^ 4 = q + 1) (hq1 : 1 < q) (hz : z ^ 4 = z + 1) (him : z.im ≠ 0)
    {H : ℝ} (hH : 0 < H) : ¬ HasUniformGap (recordWindow (embed4 q) (embed4 z) H) := by
  rintro ⟨d, hd, hgap⟩
  obtain ⟨n, hn, hne, hsmall⟩ := quartic_arbitrarily_close_records hq hq1 hz him hH hd
  have hmem : embed4 z (inverseUnit n) ∈ recordWindow (embed4 q) (embed4 z) H :=
    ⟨inverseUnit n, hn.le, rfl⟩
  have hzero : (0 : ℂ) ∈ recordWindow (embed4 q) (embed4 z) H := by
    refine ⟨(0, 0, 0, 0), ?_, ?_⟩ <;> simp [embed4, hH.le]
  have hbound := hgap _ hmem 0 hzero hne
  simp only [sub_zero] at hbound
  exact (not_lt_of_ge hbound) hsmall

/-- The same unit sequence escapes every bound at a contracting real place.
Thus this explicit crowding witness is excluded if that place is also bounded. -/
theorem contracting_real_place_escapes {s : ℝ} (hs : s ^ 4 = s + 1)
    (hs0 : 0 < |s|) (hs1 : |s| < 1) (K : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, K < |embed4 s (inverseUnit n)| := by
  have hinv : 1 < |s|⁻¹ := (one_lt_inv₀ hs0).2 hs1
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt K hinv
  refine ⟨N, fun n hn => ?_⟩
  rw [inverseUnit_embedding hs, abs_pow, abs_inv]
  exact hN.trans_le (pow_le_pow_right₀ hinv.le hn)

/-- The escaping place exists for the actual quartic, with no extra root
existence assumption. The imported theorem brackets it between -0.73 and -0.72. -/
theorem exists_escaping_quartic_place :
    ∃ s : ℝ, s ^ 4 = s + 1 ∧ -1 < s ∧ s < 0 ∧
      ∀ K : ℝ, ∃ N : ℕ, ∀ n ≥ N, K < |embed4 s (inverseUnit n)| := by
  obtain ⟨s, hs, hlo, hhi⟩ := PDT.SalemFamily.exists_r2
  have hsneg : s < 0 := by linarith
  refine ⟨s, hs, by linarith, hsneg, fun K => ?_⟩
  apply contracting_real_place_escapes hs
  · exact abs_pos.mpr (ne_of_lt hsneg)
  · rw [abs_of_neg hsneg]
    linarith

end
end PDT.RecordBoundary

#print axioms PDT.RecordBoundary.cubic_window_uniform_gap
#print axioms PDT.RecordBoundary.quartic_arbitrarily_close_records
#print axioms PDT.RecordBoundary.quartic_window_no_uniform_gap
#print axioms PDT.RecordBoundary.contracting_real_place_escapes
#print axioms PDT.RecordBoundary.exists_escaping_quartic_place

#print axioms PDT.RecordBoundary.Quad

#print axioms PDT.RecordBoundary.embed4

#print axioms PDT.RecordBoundary.untick4

#print axioms PDT.RecordBoundary.quartic_ne_zero

#print axioms PDT.RecordBoundary.embed4_untick

#print axioms PDT.RecordBoundary.embed4_untick_iter

#print axioms PDT.RecordBoundary.inverseUnit

#print axioms PDT.RecordBoundary.inverseUnit_embedding

#print axioms PDT.RecordBoundary.recordWindow

#print axioms PDT.RecordBoundary.HasUniformGap

#print axioms PDT.RecordBoundary.simultaneous_inverse_powers
