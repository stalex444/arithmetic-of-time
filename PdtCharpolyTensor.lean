/-
# The rhoQ substitution's incidence matrix has characteristic polynomial minpoly(rhoQ)

The 12-letter substitution `PdtRhoQ.s` (the tensor of the cubic and quartic
rules) has inflation factor `rhoQ`; a computation found that its incidence
matrix has characteristic polynomial exactly `minpoly(rhoQ)` and that its tenth
power `K^10` is positive.

This file proves the first of those two in the kernel. `K^10 > 0` (primitivity)
is NOT touched here, and neither is dominance of `rhoQ` over the other
eigenvalues: only the characteristic-polynomial statement is proved.

WHAT IS PROVED, in two steps.

`charpoly_tensor`  the matrix statement: for `A` the cubic substitution's
incidence matrix and `B` the quartic's, `charpoly (A ⊗ B) = rulerPoly`.

`substitution_charpoly`  the statement about the SUBSTITUTION: the incidence
matrix of `PdtRhoQ.s` itself — counting occurrences of each letter in each image
word — has that same characteristic polynomial. This
is the step that keeps the theorem from being about a matrix literal: it certifies
that the 12x12 matrix really is the abelianization of `p1 -> q2, ..., r4 ->
p1 p2 q1 q2`.

THE ROUTE, and why it is not a corollary of what was already held. Mathlib has no
`charpoly_kronecker` (checked at this pin), and `PdtRulerMinpoly.ruler_factorization`
— which does write out the composed product — is a polynomial identity mentioning
no matrix. So the eigenvalue is exhibited directly instead, by explicit
eigenvectors: `A v = rho v` for `v = (1, rho^2, rho)`, `B w = Q w` for
`w = (1, Q^3, Q^2, Q)`, hence `(A ⊗ B)(v ⊗ w) = rhoQ (v ⊗ w)` with `v ⊗ w` nonzero.
Then `minpoly rhoQ` divides the charpoly, both are monic of degree 12, and
`PdtRulerMinpoly.ruler_minpoly` identifies the minpoly.

CALIBRATION, so this is not read as more surprising than it is. Minimality CAN
fail: Fibonacci tensor Fibonacci gives `(x+1)^2 (x^2 - 3x + 1)`, two spurious
eigenvalues at -1 — the degenerate case of the direct-product construction in
the published literature (Frank). But across 49 ordered pairs of a small
natural family it holds 40 times (a computation not included here), and every
failure is a same-polynomial pair where `deg(alpha^2) < m^2` is forced. For
distinct degrees it is the typical outcome. It is a real property that can fail; it is not discriminating.
-/

module
public import Mathlib
public import PdtRulerMinpoly
public import PdtRhoQChirality

@[expose] public section

open Matrix Polynomial
open scoped Kronecker

namespace PdtCharpolyTensor

/-! ## The Kronecker lemma Mathlib does not have -/

/-- A Kronecker product acts on a product vector factorwise. Absent from Mathlib
at this pin, and the only missing piece of the route. -/
theorem kron_mulVec {R : Type*} [CommSemiring R] {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m R) (B : Matrix n n R) (v : m → R) (w : n → R) :
    (A ⊗ₖ B) *ᵥ (fun p : m × n => v p.1 * w p.2)
      = fun p : m × n => (A *ᵥ v) p.1 * (B *ᵥ w) p.2 := by
  funext p
  obtain ⟨i, j⟩ := p
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, kronecker_apply]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-! ## The two founding incidence matrices -/

/-- The cubic substitution `a -> b, b -> c, c -> ab`. This is exactly the
plastic-number matrix published as Example 1 of Bertrand-Mathis and Nguema Ndong,
INTEGERS 21 (2021) A50. -/
def Acub : Matrix (Fin 3) (Fin 3) ℚ := !![0,0,1; 1,0,1; 0,1,0]

/-- The quartic substitution `1 -> 2, 2 -> 3, 3 -> 4, 4 -> 12`. -/
def Bqua : Matrix (Fin 4) (Fin 4) ℚ := !![0,0,0,1; 1,0,0,1; 0,1,0,0; 0,0,1,0]

def Mten : Matrix (Fin 3 × Fin 4) (Fin 3 × Fin 4) ℚ := Acub ⊗ₖ Bqua

noncomputable def AR : Matrix (Fin 3) (Fin 3) ℝ := Acub.map (algebraMap ℚ ℝ)
noncomputable def BR : Matrix (Fin 4) (Fin 4) ℝ := Bqua.map (algebraMap ℚ ℝ)

lemma map_Mten : Mten.map (algebraMap ℚ ℝ) = AR ⊗ₖ BR := by
  ext ⟨i,j⟩ ⟨k,l⟩; simp [Mten, AR, BR, Matrix.map_apply]

/-! ## rhoQ is an eigenvalue, by explicit eigenvectors -/

lemma A_eigen {r : ℝ} (hr : r ^ 3 = r + 1) :
    AR *ᵥ ![1, r^2, r] = fun i => r * (![1, r^2, r] i) := by
  funext i
  fin_cases i <;>
    simp [AR, Acub, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.map_apply] <;>
    linarith [hr]

lemma B_eigen {q : ℝ} (hq : q ^ 4 = q + 1) :
    BR *ᵥ ![1, q^3, q^2, q] = fun i => q * (![1, q^3, q^2, q] i) := by
  funext i
  fin_cases i <;>
    simp [BR, Bqua, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.map_apply] <;>
    linarith [hq]

lemma tensor_eigen {r q : ℝ} (hr : r ^ 3 = r + 1) (hq : q ^ 4 = q + 1) :
    (AR ⊗ₖ BR) *ᵥ (fun p : Fin 3 × Fin 4 => (![1, r^2, r] p.1) * (![1, q^3, q^2, q] p.2))
      = fun p : Fin 3 × Fin 4 => (r*q) * ((![1, r^2, r] p.1) * (![1, q^3, q^2, q] p.2)) := by
  rw [kron_mulVec, A_eigen hr, B_eigen hq]
  funext p; ring

lemma det_zero {r q : ℝ} (hr : r ^ 3 = r + 1) (hq : q ^ 4 = q + 1) :
    ((Matrix.scalar (Fin 3 × Fin 4)) (r*q) - (AR ⊗ₖ BR)).det = 0 := by
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨fun p : Fin 3 × Fin 4 => (![1, r^2, r] p.1) * (![1, q^3, q^2, q] p.2), ?_, ?_⟩
  · intro h
    have h0 := congrFun h (0,0)
    simp at h0
  · rw [Matrix.sub_mulVec, tensor_eigen hr hq]
    funext p
    simp [Matrix.scalar, Matrix.mulVec, dotProduct, Matrix.diagonal, Finset.sum_ite_eq]

/-! ## The matrix theorem -/

/-- **The charpoly of the tensor is the ruler minimal polynomial.** -/
theorem charpoly_tensor : Mten.charpoly = PDT.RulerMinpoly.rulerPoly := by
  obtain ⟨r, hr⟩ := PDT.RulerMinpoly.exists_cubic_root
  obtain ⟨q, hq, -⟩ := PDT.RulerMinpoly.exists_quartic_root
  have hroot : (aeval (r*q)) Mten.charpoly = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, ← Matrix.charpoly_map Mten (algebraMap ℚ ℝ), map_Mten,
        Matrix.eval_charpoly]
    exact det_zero hr hq
  have hdvd : minpoly ℚ (r*q) ∣ Mten.charpoly := minpoly.dvd ℚ _ hroot
  rw [PDT.RulerMinpoly.ruler_minpoly hr hq] at hdvd
  have hdeg : Mten.charpoly.natDegree = 12 := by
    rw [Matrix.charpoly_natDegree_eq_dim]; simp
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    PDT.RulerMinpoly.rulerPoly_monic (Matrix.charpoly_monic _) hdvd
    (by rw [hdeg, PDT.RulerMinpoly.rulerPoly_natDegree])

/-! ## The statement about the SUBSTITUTION -/

open PdtRhoQ

/-- The incidence matrix of the 12-letter substitution itself: `inc i j` counts
the occurrences of letter `i` in the image word `s j`. -/
def inc : Matrix Letter Letter ℕ := fun i j => (s j).count i

/-- The product alphabet really is a product: `{p,q,r} x {1,2,3,4}`. -/
def idx : Letter ≃ Fin 3 × Fin 4 where
  toFun
    | .p1 => (0,0) | .p2 => (0,1) | .p3 => (0,2) | .p4 => (0,3)
    | .q1 => (1,0) | .q2 => (1,1) | .q3 => (1,2) | .q4 => (1,3)
    | .r1 => (2,0) | .r2 => (2,1) | .r3 => (2,2) | .r4 => (2,3)
  invFun p :=
    match p with
    | (0,0) => .p1 | (0,1) => .p2 | (0,2) => .p3 | (0,3) => .p4
    | (1,0) => .q1 | (1,1) => .q2 | (1,2) => .q3 | (1,3) => .q4
    | (2,0) => .r1 | (2,1) => .r2 | (2,2) => .r3 | (2,3) => .r4
  left_inv := by intro x; cases x <;> rfl
  right_inv := by rintro ⟨i, j⟩; fin_cases i <;> fin_cases j <;> rfl

/-- **The substitution's abelianization IS the tensor.** This is the step that
keeps the result from being a statement about a matrix literal. -/
theorem inc_eq_tensor (i j : Letter) :
    ((inc i j : ℕ) : ℚ) = Mten (idx i) (idx j) := by
  cases i <;> cases j <;>
    norm_num [inc, s, Mten, Acub, Bqua, idx, Matrix.kroneckerMap_apply,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;>
    decide

/-- **The substitution's characteristic polynomial.** The characteristic polynomial of the 12-letter
substitution's own incidence matrix is `minpoly(rhoQ)`. -/
theorem substitution_charpoly :
    ((inc.map (fun n : ℕ => (n : ℚ))).reindex idx idx).charpoly
      = PDT.RulerMinpoly.rulerPoly := by
  have h : (inc.map (fun n : ℕ => (n : ℚ))).reindex idx idx = Mten := by
    ext a b
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
    simpa using inc_eq_tensor (idx.symm a) (idx.symm b)
  rw [h, charpoly_tensor]

end PdtCharpolyTensor
