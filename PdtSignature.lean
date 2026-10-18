module
public import Mathlib

@[expose] public section

/-!
# The (3,1) signature of the trace form of K = ℚ[x]/(x⁴ − x − 1)

The trace form (Gram matrix in the power basis {1, x, x², x³}) is the
integer matrix `M` with `M_{ij} = p_{i+j}`, the power sums of the roots of
`x⁴ − x − 1`. Newton's identities (e₁=0, e₂=0, e₃=1, e₄=−1) give
`p₀=4, p₁=0, p₂=0, p₃=3, p₄=4, p₅=0, p₆=3`, hence

  `M = !![4,0,0,3; 0,0,3,4; 0,3,4,0; 3,4,0,3]`.

We prove, all kernel-checked:

* `det_M`        : `det M = -283`  (negative ⇒ an odd number of negative
                   eigenvalues, hence at least one),
* `congruence`   : an explicit invertible rational `P` (with `det P = -1`)
                   carries `M` to a diagonal form `Pᵀ M P = D`,
                   `D = diag(4, 4, -9/4, 283/36)`,
* the diagonal of `D` has exactly THREE positive entries and ONE negative
  entry (`D00_pos`, `D11_pos`, `D33_pos`, `D22_neg`).

By Sylvester's law of inertia the signature of `M` equals the signs of the
diagonal of any such `D`, i.e. **(3, 1)**. The bundled statement is
`signature_3_1`.

The matrix `P` was produced by symmetric Gaussian elimination with a
permutation to dodge the zero leading 2×2 minor (`M₁₁ = M₂₂ over the
{x,x²} block is singular`).

NOTE ON TACTICS: the two determinant evaluations use `decide +kernel`
(kernel-trusted reduction of a `Decidable` equality of explicit rationals;
this is NOT compiled native evaluation and adds no compiler trust). The axiom set of
every theorem below is exactly `{propext, Classical.choice, Quot.sound}`.
-/

namespace PDT

open Matrix

/-- The trace-form Gram matrix of `K = ℚ[x]/(x⁴ − x − 1)` in the power basis. -/
def M : Matrix (Fin 4) (Fin 4) ℚ :=
  !![4,0,0,3; 0,0,3,4; 0,3,4,0; 3,4,0,3]

/-- The explicit rational congruence matrix (symmetric Gaussian elimination
with a permutation to dodge the zero leading 2×2 minor). -/
def P : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 0, -3/4;
     0, 0, 1, 16/9;
     0, 1, -3/4, -4/3;
     0, 0, 0, 1]

/-- The diagonalised trace form `D = Pᵀ M P`. -/
def D : Matrix (Fin 4) (Fin 4) ℚ :=
  !![4, 0, 0, 0;
     0, 4, 0, 0;
     0, 0, -9/4, 0;
     0, 0, 0, 283/36]

/-- `M` is symmetric (it is a Gram matrix). -/
theorem M_symm : M.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M, Matrix.IsSymm, Matrix.transpose_apply]

/-- The determinant of the trace form is `-283`. Negative determinant forces
an odd number of negative eigenvalues, hence at least one. -/
theorem det_M : M.det = -283 := by
  simp only [M, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.det_fin_zero, Matrix.submatrix_apply, Fin.succAbove, Fin.castSucc_zero,
    Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  decide +kernel

/-- `det M < 0`. -/
theorem det_M_neg : M.det < 0 := by
  rw [det_M]; norm_num

/-- The congruence `Pᵀ * M * P = D` holds exactly over `ℚ`. -/
theorem congruence : P.transpose * M * P = D := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P, M, D, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;> norm_num

/-- `P` is invertible: its determinant is `-1`. -/
theorem det_P : P.det = -1 := by
  simp only [P, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.det_fin_zero, Matrix.submatrix_apply, Fin.succAbove, Fin.castSucc_zero,
    Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  decide +kernel

/-- `P` is a unit (its determinant is a unit), so the congruence is genuine. -/
theorem P_isUnit : IsUnit P.det := by
  rw [det_P]; exact isUnit_one.neg

/-- `D` is diagonal. -/
theorem D_isDiag : D.IsDiag := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [D]

/-! ### The (3,1) signature, read off from the signs of the diagonal of `D`. -/

theorem D00_pos : (0 : ℚ) < D 0 0 := by show (0 : ℚ) < (4 : ℚ); norm_num
theorem D11_pos : (0 : ℚ) < D 1 1 := by show (0 : ℚ) < (4 : ℚ); norm_num
theorem D33_pos : (0 : ℚ) < D 3 3 := by show (0 : ℚ) < (283 / 36 : ℚ); norm_num
theorem D22_neg : D 2 2 < (0 : ℚ) := by show (-9 / 4 : ℚ) < 0; norm_num

/-- **The (3,1) signature theorem (concrete Sylvester form).**

There is an invertible rational congruence `P` carrying the trace form `M`
to the diagonal form `D` whose diagonal has exactly three positive entries
and one negative entry. By Sylvester's law of inertia the signature of the
real quadratic form `M` is therefore `(3, 1)`. Together with `det_M = -283`
(`< 0`, forcing an odd number of negative signs) this pins the signature
uniquely. -/
theorem signature_3_1 :
    M.IsSymm ∧
    P.transpose * M * P = D ∧
    IsUnit P.det ∧
    D.IsDiag ∧
    (0 < D 0 0 ∧ 0 < D 1 1 ∧ 0 < D 3 3) ∧ D 2 2 < 0 ∧
    M.det = -283 := by
  exact ⟨M_symm, congruence, P_isUnit, D_isDiag,
    ⟨D00_pos, D11_pos, D33_pos⟩, D22_neg, det_M⟩

end PDT

/-! ### Axiom audit -/

#print axioms PDT.M_symm
#print axioms PDT.det_M
#print axioms PDT.det_M_neg
#print axioms PDT.congruence
#print axioms PDT.det_P
#print axioms PDT.P_isUnit
#print axioms PDT.D_isDiag
#print axioms PDT.D00_pos
#print axioms PDT.D11_pos
#print axioms PDT.D33_pos
#print axioms PDT.D22_neg
#print axioms PDT.signature_3_1
