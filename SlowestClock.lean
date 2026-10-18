module
public import Mathlib
public import PdtMahlerWindow
public import PdtMirrorTensor
public import Irreducibility
public import Settling

@[expose] public section

/-!
# SlowestClock — the slowest settling clock on at most three letters

For a substitution `σ` on an alphabet of `k ≤ 3` letters with integer incidence
matrix `inc σ` (entry `(i, j)` counts the letter `i` in the image of `j`):

* `pisot_ge_rho` — every Pisot number `θ` of degree at most `3` satisfies
  `ρ ≤ θ`, where `ρ` is the real root of `x³ = x + 1`. A Pisot number equals
  the Mahler measure of its minimal polynomial (`mahler_eq_of_pisot`), and the
  registered Mahler minima (`PDT.Mahler.quadratic_mahler_min'`,
  `PDT.Mahler.cubic_mahler_min'`, from the package of
  PALOMAR-2026-08-31-000004, copied here with statements and proofs
  unchanged) bound that measure below by the golden ratio in degree `2` and by
  `ρ` in degree `3`. Degree `1` gives an
  integer `≥ 2`. This is Siegel's theorem (Duke Math. J. 11 (1944)), which
  holds in every degree, restricted here to degree at most `3`.
* `matrix_unique` — a `3 × 3` matrix with entries in `ℕ` and characteristic
  polynomial `x³ − x − 1` equals the Padovan incidence matrix
  `!![0, 0, 1; 1, 0, 1; 0, 1, 0]` after one simultaneous permutation of rows
  and columns. The trace `0` forces a zero diagonal; the sum of the principal
  `2 × 2` minors, `−1`, leaves exactly one `2`-cycle; the determinant, `1`,
  leaves exactly one `3`-cycle. That fixes all nine entries, in six matrices,
  each a relabelling of the Padovan matrix.
* `clock_unique` — for a real eigenvalue `θ` of `inc σ` with `k ≤ 3`,
  `θ = ρ` if and only if, after renaming the letters, `σ` is the Padovan
  substitution `a ↦ b, b ↦ c, c ↦ ab` or its mirror `c ↦ ba`. An incidence
  matrix fixes each image as a multiset; only the two-letter image `c ↦ {a, b}`
  can be ordered in two ways.
* `slowest_clock` — the two together.

Neither primitivity nor the unit property is assumed: the bound holds for every
Pisot eigenvalue, and the classification for every real eigenvalue.
-/

namespace Time.Clock

open Polynomial

/-- The Padovan substitution on `Fin 3`: `0 ↦ [1]`, `1 ↦ [2]`, `2 ↦ [0, 1]`. -/
def pad : Fin 3 → List (Fin 3)
  | 0 => [1]
  | 1 => [2]
  | 2 => [0, 1]

/-- The incidence matrix of a substitution: the entry at `(i, j)` counts the
occurrences of `i` in the image of `j`. -/
def inc {A : Type*} [DecidableEq A] (σ : A → List A) : Matrix A A ℤ :=
  fun i j => ((σ j).count i : ℤ)

/-- The Padovan incidence matrix. -/
def padMat : Matrix (Fin 3) (Fin 3) ℕ := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

lemma padMat_eq_count (a b : Fin 3) : padMat a b = (pad b).count a := by
  fin_cases a <;> fin_cases b <;> rfl

/-! ### The characteristic polynomial of a `3 × 3` matrix, evaluated -/

lemma charpoly_eval_fin_three {R : Type*} [CommRing R] (N : Matrix (Fin 3) (Fin 3) R)
    (t : R) :
    N.charpoly.eval t = (t - N 0 0) * (t - N 1 1) * (t - N 2 2)
      - (t - N 0 0) * N 1 2 * N 2 1 - N 0 1 * N 1 0 * (t - N 2 2)
      - N 0 1 * N 1 2 * N 2 0 - N 0 2 * N 1 0 * N 2 1
      - N 0 2 * (t - N 1 1) * N 2 0 := by
  rw [Matrix.eval_charpoly, Matrix.det_fin_three]
  simp [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply] <;> ring

/-! ### The matrix classification -/

/-- Nine entries determine a `3 × 3` matrix. -/
lemma mat_eq_of_entries (M : Matrix (Fin 3) (Fin 3) ℕ) {a b c d e f g h i : ℕ}
    (h00 : M 0 0 = a) (h01 : M 0 1 = b) (h02 : M 0 2 = c)
    (h10 : M 1 0 = d) (h11 : M 1 1 = e) (h12 : M 1 2 = f)
    (h20 : M 2 0 = g) (h21 : M 2 1 = h) (h22 : M 2 2 = i) :
    M = !![a, b, c; d, e, f; g, h, i] := by
  ext x y
  fin_cases x <;> fin_cases y <;> simp [h00, h01, h02, h10, h11, h12, h20, h21, h22]

private def eA1 : Fin 3 ≃ Fin 3 :=
  ⟨![2, 1, 0], ![2, 1, 0], by intro x; fin_cases x <;> rfl, by intro x; fin_cases x <;> rfl⟩
private def eA2 : Fin 3 ≃ Fin 3 :=
  ⟨![1, 0, 2], ![1, 0, 2], by intro x; fin_cases x <;> rfl, by intro x; fin_cases x <;> rfl⟩
private def eA3 : Fin 3 ≃ Fin 3 :=
  ⟨![0, 2, 1], ![0, 2, 1], by intro x; fin_cases x <;> rfl, by intro x; fin_cases x <;> rfl⟩
private def eB1 : Fin 3 ≃ Fin 3 :=
  ⟨![1, 2, 0], ![2, 0, 1], by intro x; fin_cases x <;> rfl, by intro x; fin_cases x <;> rfl⟩
private def eB2 : Fin 3 ≃ Fin 3 :=
  ⟨![2, 0, 1], ![1, 2, 0], by intro x; fin_cases x <;> rfl, by intro x; fin_cases x <;> rfl⟩

/-- **The matrix classification.** A `3 × 3` matrix with entries in `ℕ` and
characteristic polynomial `x³ − x − 1` is the Padovan incidence matrix after a
simultaneous permutation of rows and columns. -/
theorem matrix_unique (M : Matrix (Fin 3) (Fin 3) ℕ)
    (h : (M.map (Nat.cast : ℕ → ℤ)).charpoly = X ^ 3 - X - 1) :
    ∃ e : Fin 3 ≃ Fin 3, ∀ i j, M i j = padMat (e i) (e j) := by
  have hev : ∀ t : ℤ, (M.map (Nat.cast : ℕ → ℤ)).charpoly.eval t = t ^ 3 - t - 1 := by
    intro t; rw [h]; simp
  have h0 := hev 0
  have h1 := hev 1
  have hm1 := hev (-1)
  rw [charpoly_eval_fin_three] at h0 h1 hm1
  simp only [Matrix.map_apply] at h0 h1 hm1
  -- the trace vanishes, so the diagonal is zero
  have htr : 2 * ((M 0 0 : ℤ) + M 1 1 + M 2 2) = 0 := by
    linear_combination -(h1 + hm1 - 2 * h0)
  have hd0 : M 0 0 = 0 := by omega
  have hd1 : M 1 1 = 0 := by omega
  have hd2 : M 2 2 = 0 := by omega
  simp only [hd0, hd1, hd2, Nat.cast_zero] at h0 h1 hm1
  -- one `2`-cycle and one `3`-cycle
  have h2S : 2 * ((M 0 1 : ℤ) * M 1 0 + M 0 2 * M 2 0 + M 1 2 * M 2 1) = 2 := by
    linear_combination hm1 - h1
  have hP2 : (M 0 1 : ℤ) * M 1 0 + M 0 2 * M 2 0 + M 1 2 * M 2 1 = 1 := by linarith
  have hP3 : (M 0 1 : ℤ) * M 1 2 * M 2 0 + M 0 2 * M 1 0 * M 2 1 = 1 := by
    linear_combination -h0
  have hP2N : M 0 1 * M 1 0 + M 0 2 * M 2 0 + M 1 2 * M 2 1 = 1 := by exact_mod_cast hP2
  have hP3N : M 0 1 * M 1 2 * M 2 0 + M 0 2 * M 1 0 * M 2 1 = 1 := by exact_mod_cast hP3
  have hcases : (M 0 1 * M 1 2 * M 2 0 = 1) ∨ (M 0 2 * M 1 0 * M 2 1 = 1) := by
    generalize M 0 1 * M 1 2 * M 2 0 = u at hP3N
    generalize M 0 2 * M 1 0 * M 2 1 = v at hP3N
    omega
  rcases hcases with hu | hv
  · have a1 : M 0 1 = 1 := Nat.eq_one_of_mul_eq_one_right (Nat.eq_one_of_mul_eq_one_right hu)
    have a2 : M 1 2 = 1 := Nat.eq_one_of_mul_eq_one_left (Nat.eq_one_of_mul_eq_one_right hu)
    have a3 : M 2 0 = 1 := Nat.eq_one_of_mul_eq_one_left hu
    rw [a1, a2, a3] at hP2N
    have hb : (M 1 0 = 1 ∧ M 0 2 = 0 ∧ M 2 1 = 0) ∨ (M 1 0 = 0 ∧ M 0 2 = 1 ∧ M 2 1 = 0) ∨
        (M 1 0 = 0 ∧ M 0 2 = 0 ∧ M 2 1 = 1) := by omega
    rcases hb with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩
    · rw [mat_eq_of_entries M hd0 a1 b2 b1 hd1 a2 a3 b3 hd2]
      exact ⟨eA1, fun i j => by fin_cases i <;> fin_cases j <;> rfl⟩
    · rw [mat_eq_of_entries M hd0 a1 b2 b1 hd1 a2 a3 b3 hd2]
      exact ⟨eA2, fun i j => by fin_cases i <;> fin_cases j <;> rfl⟩
    · rw [mat_eq_of_entries M hd0 a1 b2 b1 hd1 a2 a3 b3 hd2]
      exact ⟨eA3, fun i j => by fin_cases i <;> fin_cases j <;> rfl⟩
  · have a1 : M 0 2 = 1 := Nat.eq_one_of_mul_eq_one_right (Nat.eq_one_of_mul_eq_one_right hv)
    have a2 : M 1 0 = 1 := Nat.eq_one_of_mul_eq_one_left (Nat.eq_one_of_mul_eq_one_right hv)
    have a3 : M 2 1 = 1 := Nat.eq_one_of_mul_eq_one_left hv
    rw [a1, a2, a3] at hP2N
    have hb : (M 0 1 = 1 ∧ M 2 0 = 0 ∧ M 1 2 = 0) ∨ (M 0 1 = 0 ∧ M 2 0 = 1 ∧ M 1 2 = 0) ∨
        (M 0 1 = 0 ∧ M 2 0 = 0 ∧ M 1 2 = 1) := by omega
    rcases hb with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩
    · rw [mat_eq_of_entries M hd0 b1 a1 a2 hd1 b3 b2 a3 hd2]
      exact ⟨eB1, fun i j => by fin_cases i <;> fin_cases j <;> rfl⟩
    · rw [mat_eq_of_entries M hd0 b1 a1 a2 hd1 b3 b2 a3 hd2]
      exact ⟨eB2, fun i j => by fin_cases i <;> fin_cases j <;> rfl⟩
    · rw [mat_eq_of_entries M hd0 b1 a1 a2 hd1 b3 b2 a3 hd2]
      exact ⟨Equiv.refl _, fun i j => by fin_cases i <;> fin_cases j <;> rfl⟩

/-! ### The real root of the cubic -/

lemma rho_bounds {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) : 1 < ρ ∧ ρ ≤ 4 / 3 ∧ 4 / 3 < ρ ^ 2 := by
  have h1 : 1 < ρ := one_lt_root hρ
  refine ⟨h1, ?_, ?_⟩
  · nlinarith [sq_nonneg (ρ - 4 / 3), sq_nonneg ρ]
  · nlinarith [sq_nonneg (ρ - 1)]

/-- The real root of `x³ = x + 1` is unique. -/
lemma cubic_root_unique {ρ θ : ℝ} (hρ : ρ ^ 3 = ρ + 1) (hθ : θ ^ 3 = θ + 1) : θ = ρ := by
  obtain ⟨_, _, hρ2⟩ := rho_bounds hρ
  have hfac : (θ - ρ) * (θ ^ 2 + θ * ρ + ρ ^ 2 - 1) = 0 := by linear_combination hθ - hρ
  have hpos : 0 < θ ^ 2 + θ * ρ + ρ ^ 2 - 1 := by nlinarith [sq_nonneg (2 * θ + ρ)]
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · linarith

/-! ### The substitution classification -/

/-- The incidence matrix as a matrix of naturals. -/
lemma inc_eq_map {k : ℕ} (σ : Fin k → List (Fin k)) :
    inc σ = (Matrix.of fun i j => (σ j).count i).map (Nat.cast : ℕ → ℤ) := rfl

lemma perm_pair_fin3 {l : List (Fin 3)} (h : l.Perm [0, 1]) : l = [0, 1] ∨ l = [1, 0] := by
  have hl : l.length = 2 := by simpa using h.length_eq
  obtain ⟨p, q, rfl⟩ := List.length_eq_two.mp hl
  revert h
  revert p q
  decide

/-- If the incidence matrix of `σ` on `Fin 3` is a relabelling of the Padovan
matrix, then `σ` is the Padovan substitution or its mirror, after renaming. -/
lemma subst_of_matrix (σ : Fin 3 → List (Fin 3)) (e : Fin 3 ≃ Fin 3)
    (he : ∀ i j, (σ j).count i = padMat (e i) (e j)) :
    (∀ x, (σ x).map e = pad (e x)) ∨ (∀ x, (σ x).map e = PdtMirror.mir pad (e x)) := by
  have hperm : ∀ x, ((σ x).map e).Perm (pad (e x)) := by
    intro x
    rw [List.perm_iff_count]
    intro y
    rw [show y = e (e.symm y) by simp, List.count_map_of_injective _ _ e.injective, he,
      Equiv.apply_symm_apply, padMat_eq_count]
  have hx0 : (σ (e.symm 0)).map e = [1] := by
    have := hperm (e.symm 0); simpa [pad] using this
  have hx1 : (σ (e.symm 1)).map e = [2] := by
    have := hperm (e.symm 1); simpa [pad] using this
  have hx2 := hperm (e.symm 2)
  simp only [Equiv.apply_symm_apply] at hx2
  rcases perm_pair_fin3 hx2 with h2 | h2
  · left
    intro x
    obtain ⟨y, rfl⟩ := e.symm.surjective x
    simp only [Equiv.apply_symm_apply]
    fin_cases y
    · simpa [pad] using hx0
    · simpa [pad] using hx1
    · simpa [pad] using h2
  · right
    intro x
    obtain ⟨y, rfl⟩ := e.symm.surjective x
    simp only [Equiv.apply_symm_apply]
    fin_cases y
    · simpa [pad, PdtMirror.mir] using hx0
    · simpa [pad, PdtMirror.mir] using hx1
    · simpa [pad, PdtMirror.mir] using h2

/-- The incidence matrix of a renamed substitution is the renamed incidence matrix. -/
lemma inc_eq_reindex (σ : Fin 3 → List (Fin 3)) (τ : Fin 3 → List (Fin 3))
    (e : Fin 3 ≃ Fin 3) (he : ∀ x, (σ x).map e = τ (e x)) :
    inc σ = Matrix.reindex e.symm e.symm (inc τ) := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, inc]
  rw [← he, List.count_map_of_injective _ _ e.injective]

lemma inc_mir (τ : Fin 3 → List (Fin 3)) : inc (PdtMirror.mir τ) = inc τ := by
  ext i j
  simp [inc, PdtMirror.mir, List.count_reverse]

lemma inc_pad : inc pad = !![0, 0, 1; 1, 0, 1; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

lemma aeval_charpoly_pad (θ : ℝ) : aeval θ (inc pad).charpoly = θ ^ 3 - θ - 1 := by
  rw [aeval_def, eval₂_eq_eval_map, ← Matrix.charpoly_map, charpoly_eval_fin_three, inc_pad]
  simp [Matrix.map_apply] <;> ring

/-- **The classification.** For a real eigenvalue `θ` of the incidence matrix of a
substitution on `k ≤ 3` letters, `θ = ρ` if and only if the substitution is, after
renaming its letters, the Padovan substitution or its mirror. -/
theorem clock_unique {k : ℕ} (hk : k ≤ 3) (σ : Fin k → List (Fin k)) (θ : ℝ)
    (hθ : aeval θ (inc σ).charpoly = 0) {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    θ = ρ ↔ ∃ e : Fin k ≃ Fin 3,
      (∀ x, (σ x).map e = pad (e x)) ∨ (∀ x, (σ x).map e = PdtMirror.mir pad (e x)) := by
  constructor
  · intro hθρ
    subst hθρ
    have hmin : minpoly ℚ θ = X ^ 3 - X - 1 := by
      refine (minpoly.eq_of_irreducible_of_monic cubicQ_irreducible ?_ (by monicity!)).symm
      simp only [map_sub, map_pow, aeval_X, map_one]
      linear_combination hρ
    have hPm : ((inc σ).charpoly.map (Int.castRingHom ℚ)).Monic :=
      (Matrix.charpoly_monic _).map _
    have hPdeg : ((inc σ).charpoly.map (Int.castRingHom ℚ)).natDegree = k := by
      rw [(Matrix.charpoly_monic _).natDegree_map, Matrix.charpoly_natDegree_eq_dim,
        Fintype.card_fin]
    have hroot : aeval θ ((inc σ).charpoly.map (Int.castRingHom ℚ)) = 0 := by
      rw [← algebraMap_int_eq, aeval_map_algebraMap]
      exact hθ
    have hdvd : minpoly ℚ θ ∣ (inc σ).charpoly.map (Int.castRingHom ℚ) :=
      minpoly.dvd ℚ θ hroot
    rw [hmin] at hdvd
    have hcub : (X ^ 3 - X - 1 : ℚ[X]).natDegree = 3 := by compute_degree!
    have hk3 : k = 3 := by
      have := natDegree_le_of_dvd hdvd hPm.ne_zero
      omega
    subst hk3
    have hPeq : (inc σ).charpoly.map (Int.castRingHom ℚ) = X ^ 3 - X - 1 :=
      eq_of_monic_of_dvd_of_natDegree_le (by monicity!) hPm hdvd (by rw [hPdeg, hcub])
    have hZ : (inc σ).charpoly = X ^ 3 - X - 1 := by
      apply Polynomial.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
      rw [hPeq]
      simp
    rw [inc_eq_map] at hZ
    obtain ⟨e, he⟩ := matrix_unique _ hZ
    exact ⟨e, subst_of_matrix σ e (fun i j => he i j)⟩
  · rintro ⟨e, he⟩
    have hk3 : k = 3 := by simpa using Fintype.card_congr e
    subst hk3
    have hinc : inc σ = Matrix.reindex e.symm e.symm (inc pad) := by
      rcases he with he | he
      · exact inc_eq_reindex σ pad e he
      · rw [inc_eq_reindex σ _ e he, inc_mir]
    rw [hinc, Matrix.charpoly_reindex, aeval_charpoly_pad] at hθ
    exact cubic_root_unique hρ (by linarith)

/-! ### Pisot numbers of degree at most three -/

/-- **A Pisot number is the Mahler measure of its minimal polynomial.** -/
lemma mahler_eq_of_pisot {θ : ℝ} (h1 : 1 < θ) (hint : IsIntegral ℤ θ)
    (hpisot : ∀ z ∈ (minpoly ℚ θ).aroots ℂ, z ≠ (θ : ℂ) → ‖z‖ < 1) :
    ((minpoly ℤ θ).map (Int.castRingHom ℂ)).mahlerMeasure = θ := by
  classical
  have hθQ : IsIntegral ℚ θ := hint.tower_top
  have hQ : minpoly ℚ θ = (minpoly ℤ θ).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
  have hpC : (minpoly ℤ θ).map (Int.castRingHom ℂ) = (minpoly ℚ θ).map (algebraMap ℚ ℂ) := by
    rw [hQ, Polynomial.map_map]
    congr 1
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hpC]
  have hlc : ((minpoly ℚ θ).map (algebraMap ℚ ℂ)).leadingCoeff = 1 :=
    ((minpoly.monic hθQ).map _).leadingCoeff
  rw [hlc, norm_one, one_mul]
  change (((minpoly ℚ θ).aroots ℂ).map fun a => max 1 ‖a‖).prod = θ
  have hnodup : ((minpoly ℚ θ).aroots ℂ).Nodup :=
    nodup_roots (PerfectField.separable_of_irreducible (minpoly.irreducible hθQ)).map
  have hmem : (θ : ℂ) ∈ (minpoly ℚ θ).aroots ℂ := by
    rw [mem_aroots]
    refine ⟨minpoly.ne_zero hθQ, ?_⟩
    have : ((θ : ℂ)) = algebraMap ℝ ℂ θ := rfl
    rw [this, aeval_algebraMap_apply, minpoly.aeval, map_zero]
  rw [Multiset.prod_map_eq_pow_single (θ : ℂ) (fun a ha hm => ?_),
    Multiset.count_eq_one_of_mem hnodup hmem, pow_one]
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact max_eq_right h1.le
  · exact max_eq_left (hpisot a hm ha).le

/-- **Siegel's bound in degree at most three.** Every Pisot number of degree at
most `3` is at least `ρ`. -/
theorem pisot_ge_rho {θ : ℝ} (h1 : 1 < θ) (hint : IsIntegral ℤ θ)
    (hdeg : (minpoly ℚ θ).natDegree ≤ 3)
    (hpisot : ∀ z ∈ (minpoly ℚ θ).aroots ℂ, z ≠ (θ : ℂ) → ‖z‖ < 1)
    {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) : ρ ≤ θ := by
  obtain ⟨hρ1, hρ43, -⟩ := rho_bounds hρ
  set p := minpoly ℤ θ with hp
  have hpm : p.Monic := minpoly.monic hint
  have hpi : Irreducible p := minpoly.irreducible hint
  have hQ : minpoly ℚ θ = p.map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
  have hdp : p.natDegree ≤ 3 := by rwa [hQ, hpm.natDegree_map] at hdeg
  have hd1 : 0 < p.natDegree := minpoly.natDegree_pos hint
  have hM := mahler_eq_of_pisot h1 hint hpisot
  rw [← hp] at hM
  have hM1 : 1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure := by rw [hM]; exact h1
  interval_cases hd : p.natDegree
  · -- degree one: `θ` is an integer greater than one
    have hlin := hpm.eq_X_add_C hd
    have hroot : aeval θ p = 0 := minpoly.aeval ℤ θ
    rw [hlin] at hroot
    simp at hroot
    have hc : θ = -(p.coeff 0 : ℝ) := by linarith
    have hc1 : (1 : ℝ) < -(p.coeff 0 : ℝ) := hc ▸ h1
    have hc2 : (2 : ℤ) ≤ -(p.coeff 0) := by
      have : (1 : ℤ) < -(p.coeff 0) := by exact_mod_cast hc1
      omega
    have hc3 : (2 : ℝ) ≤ -(p.coeff 0 : ℝ) := by exact_mod_cast hc2
    linarith
  · -- degree two: at least the golden ratio
    have hmin := PDT.Mahler.quadratic_mahler_min' p hpm hd hpi hM1
    have hφ := PDT.Mahler.mahler_quadratic_phi
    rw [PDT.Mahler.zq2_fam] at hφ
    obtain ⟨hφ2, hφ1⟩ := hφ
    rw [hM] at hmin
    nlinarith
  · -- degree three: at least `ρ`
    have hmin := PDT.Mahler.cubic_mahler_min' p hpm hd hpi hM1
    have hm := PDT.Mahler.mahler_cubic_rho
    rw [PDT.Mahler.zq3_fam] at hm
    obtain ⟨hm3, -⟩ := hm
    rw [hM, cubic_root_unique hρ hm3] at hmin
    exact hmin

/-- **The slowest settling clock.** For a substitution on `k ≤ 3` letters and a
real eigenvalue `θ > 1` of its incidence matrix that is a Pisot number:
`ρ ≤ θ`, with equality exactly for the Padovan substitution and its mirror, up to
renaming the letters. -/
theorem slowest_clock {k : ℕ} (hk : k ≤ 3) (σ : Fin k → List (Fin k)) (θ : ℝ)
    (hθ : aeval θ (inc σ).charpoly = 0) (h1 : 1 < θ)
    (hpisot : ∀ z ∈ (minpoly ℚ θ).aroots ℂ, z ≠ (θ : ℂ) → ‖z‖ < 1)
    {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) :
    ρ ≤ θ ∧ (θ = ρ ↔ ∃ e : Fin k ≃ Fin 3,
      (∀ x, (σ x).map e = pad (e x)) ∨ (∀ x, (σ x).map e = PdtMirror.mir pad (e x))) := by
  refine ⟨?_, clock_unique hk σ θ hθ hρ⟩
  have hint : IsIntegral ℤ θ := ⟨(inc σ).charpoly, Matrix.charpoly_monic _, by
    rw [← aeval_def]; exact hθ⟩
  have hroot : aeval θ ((inc σ).charpoly.map (Int.castRingHom ℚ)) = 0 := by
    rw [← algebraMap_int_eq, aeval_map_algebraMap]
    exact hθ
  have hdvd : minpoly ℚ θ ∣ (inc σ).charpoly.map (Int.castRingHom ℚ) := minpoly.dvd ℚ θ hroot
  have hdeg : (minpoly ℚ θ).natDegree ≤ 3 := by
    have hne : (inc σ).charpoly.map (Int.castRingHom ℚ) ≠ 0 :=
      ((Matrix.charpoly_monic _).map _).ne_zero
    have := natDegree_le_of_dvd hdvd hne
    rw [(Matrix.charpoly_monic _).natDegree_map, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin] at this
    omega
  exact pisot_ge_rho h1 hint hdeg hpisot hρ

end Time.Clock

/-! ### Axiom audit -/

#print axioms Time.Clock.matrix_unique
#print axioms Time.Clock.clock_unique
#print axioms Time.Clock.mahler_eq_of_pisot
#print axioms Time.Clock.pisot_ge_rho
#print axioms Time.Clock.slowest_clock
