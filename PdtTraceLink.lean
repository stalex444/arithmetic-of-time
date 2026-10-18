module
public import Mathlib
public import PdtSignature
public import PdtSignatureRho

@[expose] public section

/-!
# The integer matrices `M` and `Mρ` are the trace-form Gram matrices

`PdtSignature` fixes the integer matrix

  `M = !![4,0,0,3; 0,0,3,4; 0,3,4,0; 3,4,0,3]`,  `det M = -283`,

and `PdtSignatureRho` fixes

  `Mρ = !![3,0,2; 0,2,3; 2,3,2]`,  `det Mρ = -23`.

Both are introduced there by hand, with Newton's identities quoted in a
comment. This file *proves* the link: `M` and `Mρ` really are the Gram
matrices of the trace form `(x, y) ↦ Tr_{K/ℚ}(x y)` in the power basis
`1, r, r², …` of `K = ℚ[X]/(f)` for `f = X⁴ − X − 1` resp. `X³ − X − 1`,
and their determinants are the power-basis discriminants `Algebra.discr`.

Everything is done with `AdjoinRoot`, `PowerBasis` and `Algebra.traceMatrix`.
-/

namespace PDT

open Polynomial Module

/-! ### The two polynomials -/

/-- The quartic `X⁴ − X − 1`. -/
noncomputable def fQ : ℚ[X] := X ^ 4 - X - 1

/-- The cubic `X³ − X − 1`. -/
noncomputable def fρ : ℚ[X] := X ^ 3 - X - 1

theorem fQ_monic : fQ.Monic := by
  unfold fQ; monicity!

theorem fρ_monic : fρ.Monic := by
  unfold fρ; monicity!

theorem fQ_natDegree : fQ.natDegree = 4 := by
  unfold fQ; compute_degree!

theorem fρ_natDegree : fρ.natDegree = 3 := by
  unfold fρ; compute_degree!

/-! ### The power bases -/

/-- The power basis `1, r, r², r³` of `ℚ[X]/(X⁴ − X − 1)`. -/
noncomputable def pbQ : PowerBasis ℚ (AdjoinRoot fQ) := AdjoinRoot.powerBasis' fQ_monic

/-- The power basis `1, r, r²` of `ℚ[X]/(X³ − X − 1)`. -/
noncomputable def pbρ : PowerBasis ℚ (AdjoinRoot fρ) := AdjoinRoot.powerBasis' fρ_monic

theorem pbQ_dim : pbQ.dim = 4 := fQ_natDegree

theorem pbρ_dim : pbρ.dim = 3 := fρ_natDegree

theorem pbQ_gen : pbQ.gen = AdjoinRoot.root fQ := rfl

theorem pbρ_gen : pbρ.gen = AdjoinRoot.root fρ := rfl

/-! ### The defining relations satisfied by the roots -/

theorem rQ_pow_four : (AdjoinRoot.root fQ) ^ 4 = AdjoinRoot.root fQ + 1 := by
  have h : (Polynomial.aeval (AdjoinRoot.root fQ)) fQ = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have h2 : (Polynomial.aeval (AdjoinRoot.root fQ)) (X ^ 4 - X - 1 : ℚ[X]) = 0 := h
  simp only [map_sub, map_pow, map_one, Polynomial.aeval_X] at h2
  linear_combination h2

theorem rρ_pow_three : (AdjoinRoot.root fρ) ^ 3 = AdjoinRoot.root fρ + 1 := by
  have h : (Polynomial.aeval (AdjoinRoot.root fρ)) fρ = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have h2 : (Polynomial.aeval (AdjoinRoot.root fρ)) (X ^ 3 - X - 1 : ℚ[X]) = 0 := h
  simp only [map_sub, map_pow, map_one, Polynomial.aeval_X] at h2
  linear_combination h2

theorem rQ_pow_five :
    (AdjoinRoot.root fQ) ^ 5 = (AdjoinRoot.root fQ) ^ 2 + AdjoinRoot.root fQ := by
  linear_combination (AdjoinRoot.root fQ) * rQ_pow_four

theorem rQ_pow_six :
    (AdjoinRoot.root fQ) ^ 6 = (AdjoinRoot.root fQ) ^ 3 + (AdjoinRoot.root fQ) ^ 2 := by
  linear_combination (AdjoinRoot.root fQ) ^ 2 * rQ_pow_four

theorem rρ_pow_four :
    (AdjoinRoot.root fρ) ^ 4 = (AdjoinRoot.root fρ) ^ 2 + AdjoinRoot.root fρ := by
  linear_combination (AdjoinRoot.root fρ) * rρ_pow_three

/-! ### The power bases, reindexed by `Fin 4` and `Fin 3` -/

/-- The power basis of `ℚ[X]/(X⁴ − X − 1)`, indexed by `Fin 4`. -/
noncomputable def bQ : Basis (Fin 4) ℚ (AdjoinRoot fQ) :=
  pbQ.basis.reindex (finCongr pbQ_dim)

/-- The power basis of `ℚ[X]/(X³ − X − 1)`, indexed by `Fin 3`. -/
noncomputable def bρ : Basis (Fin 3) ℚ (AdjoinRoot fρ) :=
  pbρ.basis.reindex (finCongr pbρ_dim)

theorem bQ_apply (i : Fin 4) : bQ i = AdjoinRoot.root fQ ^ (i : ℕ) := by
  show (pbQ.basis.reindex (finCongr pbQ_dim)) i = _
  rw [Basis.reindex_apply, pbQ.basis_eq_pow, pbQ_gen]
  simp

theorem bρ_apply (i : Fin 3) : bρ i = AdjoinRoot.root fρ ^ (i : ℕ) := by
  show (pbρ.basis.reindex (finCongr pbρ_dim)) i = _
  rw [Basis.reindex_apply, pbρ.basis_eq_pow, pbρ_gen]
  simp

theorem bQ0 : bQ 0 = 1 := by simp [bQ_apply]
theorem bQ1 : bQ 1 = AdjoinRoot.root fQ := by simp [bQ_apply]
theorem bQ2 : bQ 2 = AdjoinRoot.root fQ ^ 2 := by simp [bQ_apply]
theorem bQ3 : bQ 3 = AdjoinRoot.root fQ ^ 3 := by simp [bQ_apply]

theorem bρ0 : bρ 0 = 1 := by simp [bρ_apply]
theorem bρ1 : bρ 1 = AdjoinRoot.root fρ := by simp [bρ_apply]
theorem bρ2 : bρ 2 = AdjoinRoot.root fρ ^ 2 := by simp [bρ_apply]

/-! ### The trace, expanded in the power basis -/

theorem traceQ_eq (x : AdjoinRoot fQ) :
    Algebra.trace ℚ (AdjoinRoot fQ) x
      = bQ.repr (x * bQ 0) 0 + bQ.repr (x * bQ 1) 1
        + bQ.repr (x * bQ 2) 2 + bQ.repr (x * bQ 3) 3 := by
  rw [Algebra.trace_eq_matrix_trace bQ x]
  simp only [Matrix.trace, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Fin.sum_univ_four]

theorem traceρ_eq (x : AdjoinRoot fρ) :
    Algebra.trace ℚ (AdjoinRoot fρ) x
      = bρ.repr (x * bρ 0) 0 + bρ.repr (x * bρ 1) 1 + bρ.repr (x * bρ 2) 2 := by
  rw [Algebra.trace_eq_matrix_trace bρ x]
  simp only [Matrix.trace, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Fin.sum_univ_three]

/-! ### The higher powers of the root, expanded in the power basis -/

theorem powQ4 : AdjoinRoot.root fQ ^ 4 = bQ 0 + bQ 1 := by
  rw [bQ0, bQ1]; linear_combination rQ_pow_four

theorem powQ5 : AdjoinRoot.root fQ ^ 5 = bQ 1 + bQ 2 := by
  rw [bQ1, bQ2]; linear_combination rQ_pow_five

theorem powQ6 : AdjoinRoot.root fQ ^ 6 = bQ 2 + bQ 3 := by
  rw [bQ2, bQ3]; linear_combination rQ_pow_six

theorem powρ3 : AdjoinRoot.root fρ ^ 3 = bρ 0 + bρ 1 := by
  rw [bρ0, bρ1]; linear_combination rρ_pow_three

theorem powρ4 : AdjoinRoot.root fρ ^ 4 = bρ 1 + bρ 2 := by
  rw [bρ1, bρ2]; linear_combination rρ_pow_four

/-! ### The power sums `p_k = Tr(r^k)` -/

theorem tQ0 : Algebra.trace ℚ (AdjoinRoot fQ) 1 = 4 := by
  simpa using Algebra.trace_algebraMap_of_basis bQ (1 : ℚ)

theorem tQ1 : Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ) = 0 := by
  rw [traceQ_eq]
  have e0 : AdjoinRoot.root fQ * bQ 0 = bQ 1 := by rw [bQ0, bQ1]; ring
  have e1 : AdjoinRoot.root fQ * bQ 1 = bQ 2 := by rw [bQ1, bQ2]; ring
  have e2 : AdjoinRoot.root fQ * bQ 2 = bQ 3 := by rw [bQ2, bQ3]; ring
  have e3 : AdjoinRoot.root fQ * bQ 3 = bQ 0 + bQ 1 := by rw [← powQ4, bQ3]; ring
  rw [e0, e1, e2, e3]
  simp

theorem tQ2 : Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ 2) = 0 := by
  rw [traceQ_eq]
  have e0 : AdjoinRoot.root fQ ^ 2 * bQ 0 = bQ 2 := by rw [bQ0, bQ2]; ring
  have e1 : AdjoinRoot.root fQ ^ 2 * bQ 1 = bQ 3 := by rw [bQ1, bQ3]; ring
  have e2 : AdjoinRoot.root fQ ^ 2 * bQ 2 = bQ 0 + bQ 1 := by rw [← powQ4, bQ2]; ring
  have e3 : AdjoinRoot.root fQ ^ 2 * bQ 3 = bQ 1 + bQ 2 := by rw [← powQ5, bQ3]; ring
  rw [e0, e1, e2, e3]
  simp

theorem tQ3 : Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ 3) = 3 := by
  rw [traceQ_eq]
  have e0 : AdjoinRoot.root fQ ^ 3 * bQ 0 = bQ 3 := by rw [bQ0, bQ3]; ring
  have e1 : AdjoinRoot.root fQ ^ 3 * bQ 1 = bQ 0 + bQ 1 := by rw [← powQ4, bQ1]; ring
  have e2 : AdjoinRoot.root fQ ^ 3 * bQ 2 = bQ 1 + bQ 2 := by rw [← powQ5, bQ2]; ring
  have e3 : AdjoinRoot.root fQ ^ 3 * bQ 3 = bQ 2 + bQ 3 := by rw [← powQ6, bQ3]; ring
  rw [e0, e1, e2, e3]
  simp
  norm_num

theorem tQ4 : Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ 4) = 4 := by
  rw [rQ_pow_four, map_add, tQ1, tQ0]; norm_num

theorem tQ5 : Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ 5) = 0 := by
  rw [rQ_pow_five, map_add, tQ2, tQ1]; norm_num

theorem tQ6 : Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ 6) = 3 := by
  rw [rQ_pow_six, map_add, tQ3, tQ2]; norm_num

theorem tρ0 : Algebra.trace ℚ (AdjoinRoot fρ) 1 = 3 := by
  simpa using Algebra.trace_algebraMap_of_basis bρ (1 : ℚ)

theorem tρ1 : Algebra.trace ℚ (AdjoinRoot fρ) (AdjoinRoot.root fρ) = 0 := by
  rw [traceρ_eq]
  have e0 : AdjoinRoot.root fρ * bρ 0 = bρ 1 := by rw [bρ0, bρ1]; ring
  have e1 : AdjoinRoot.root fρ * bρ 1 = bρ 2 := by rw [bρ1, bρ2]; ring
  have e2 : AdjoinRoot.root fρ * bρ 2 = bρ 0 + bρ 1 := by rw [← powρ3, bρ2]; ring
  rw [e0, e1, e2]
  simp

theorem tρ2 : Algebra.trace ℚ (AdjoinRoot fρ) (AdjoinRoot.root fρ ^ 2) = 2 := by
  rw [traceρ_eq]
  have e0 : AdjoinRoot.root fρ ^ 2 * bρ 0 = bρ 2 := by rw [bρ0, bρ2]; ring
  have e1 : AdjoinRoot.root fρ ^ 2 * bρ 1 = bρ 0 + bρ 1 := by rw [← powρ3, bρ1]; ring
  have e2 : AdjoinRoot.root fρ ^ 2 * bρ 2 = bρ 1 + bρ 2 := by rw [← powρ4, bρ2]; ring
  rw [e0, e1, e2]
  simp
  norm_num

theorem tρ3 : Algebra.trace ℚ (AdjoinRoot fρ) (AdjoinRoot.root fρ ^ 3) = 3 := by
  rw [rρ_pow_three, map_add, tρ1, tρ0]; norm_num

theorem tρ4 : Algebra.trace ℚ (AdjoinRoot fρ) (AdjoinRoot.root fρ ^ 4) = 2 := by
  rw [rρ_pow_four, map_add, tρ2, tρ1]; norm_num

/-- The power sums of `X⁴ − X − 1`: `p₀,…,p₆ = 4, 0, 0, 3, 4, 0, 3`. -/
theorem trace_rootQ_pow (k : ℕ) (hk : k ≤ 6) :
    Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ k)
      = ![4, 0, 0, 3, 4, 0, 3] (⟨k, by omega⟩ : Fin 7) := by
  have h : ∀ i : Fin 7, Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ (i : ℕ))
      = ![4, 0, 0, 3, 4, 0, 3] i := by
    intro i
    fin_cases i <;> simp [tQ0, tQ1, tQ2, tQ3, tQ4, tQ5, tQ6]
  exact h ⟨k, by omega⟩

/-- The power sums of `X³ − X − 1`: `p₀,…,p₄ = 3, 0, 2, 3, 2`. -/
theorem trace_rootρ_pow (k : ℕ) (hk : k ≤ 4) :
    Algebra.trace ℚ (AdjoinRoot fρ) (AdjoinRoot.root fρ ^ k)
      = ![3, 0, 2, 3, 2] (⟨k, by omega⟩ : Fin 5) := by
  have h : ∀ i : Fin 5, Algebra.trace ℚ (AdjoinRoot fρ) (AdjoinRoot.root fρ ^ (i : ℕ))
      = ![3, 0, 2, 3, 2] i := by
    intro i
    fin_cases i <;> simp [tρ0, tρ1, tρ2, tρ3, tρ4]
  exact h ⟨k, by omega⟩

/-! ### The Gram matrices of the trace form -/

theorem traceMatrix_bQ_apply (i j : Fin 4) :
    Algebra.traceMatrix ℚ (⇑bQ) i j
      = Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ ((i : ℕ) + (j : ℕ))) := by
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, bQ_apply, bQ_apply, ← pow_add]

theorem traceMatrix_bρ_apply (i j : Fin 3) :
    Algebra.traceMatrix ℚ (⇑bρ) i j
      = Algebra.trace ℚ (AdjoinRoot fρ) (AdjoinRoot.root fρ ^ ((i : ℕ) + (j : ℕ))) := by
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, bρ_apply, bρ_apply, ← pow_add]

/-- **The quartic link.** The integer matrix `M` of `PdtSignature` is the Gram matrix
of the trace form of `ℚ[X]/(X⁴ − X − 1)` in the power basis `1, r, r², r³`. -/
theorem traceMatrix_bQ : Algebra.traceMatrix ℚ (⇑bQ) = M := by
  ext i j
  rw [traceMatrix_bQ_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [M, tQ0, tQ1, tQ2, tQ3, tQ4, tQ5, tQ6]

/-- **The cubic link.** The integer matrix `Mρ` of `PdtSignatureRho` is the Gram matrix
of the trace form of `ℚ[X]/(X³ − X − 1)` in the power basis `1, r, r²`. -/
theorem traceMatrix_bρ : Algebra.traceMatrix ℚ (⇑bρ) = Mρ := by
  ext i j
  rw [traceMatrix_bρ_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [Mρ, tρ0, tρ1, tρ2, tρ3, tρ4]

/-- The same statement, phrased for the unreindexed `PowerBasis` of `AdjoinRoot fQ`. -/
theorem traceMatrix_Q (i j : Fin pbQ.dim) :
    Algebra.traceMatrix ℚ (⇑pbQ.basis) i j = M (Fin.cast pbQ_dim i) (Fin.cast pbQ_dim j) := by
  have h : Algebra.traceMatrix ℚ (⇑bQ) (finCongr pbQ_dim i) (finCongr pbQ_dim j)
      = Algebra.traceMatrix ℚ (⇑pbQ.basis) i j := by
    show Algebra.traceMatrix ℚ (⇑(pbQ.basis.reindex (finCongr pbQ_dim)))
        (finCongr pbQ_dim i) (finCongr pbQ_dim j) = _
    rw [Algebra.traceMatrix_reindex]
    simp
  rw [← h, traceMatrix_bQ]
  rfl

/-- The same statement, phrased for the unreindexed `PowerBasis` of `AdjoinRoot fρ`. -/
theorem traceMatrix_ρ (i j : Fin pbρ.dim) :
    Algebra.traceMatrix ℚ (⇑pbρ.basis) i j = Mρ (Fin.cast pbρ_dim i) (Fin.cast pbρ_dim j) := by
  have h : Algebra.traceMatrix ℚ (⇑bρ) (finCongr pbρ_dim i) (finCongr pbρ_dim j)
      = Algebra.traceMatrix ℚ (⇑pbρ.basis) i j := by
    show Algebra.traceMatrix ℚ (⇑(pbρ.basis.reindex (finCongr pbρ_dim)))
        (finCongr pbρ_dim i) (finCongr pbρ_dim j) = _
    rw [Algebra.traceMatrix_reindex]
    simp
  rw [← h, traceMatrix_bρ]
  rfl

/-! ### The power-basis discriminants -/

/-- **The discriminant of the power basis of `ℚ[X]/(X⁴ − X − 1)` is `−283`.** -/
theorem discr_Q : Algebra.discr ℚ pbQ.basis = -283 := by
  have h : Algebra.discr ℚ (⇑bQ) = Algebra.discr ℚ (⇑pbQ.basis) := by
    show Algebra.discr ℚ (⇑(pbQ.basis.reindex (finCongr pbQ_dim))) = _
    rw [Basis.coe_reindex]
    exact Algebra.discr_reindex ℚ pbQ.basis (finCongr pbQ_dim)
  rw [← h, Algebra.discr_def, traceMatrix_bQ, det_M]

/-- **The discriminant of the power basis of `ℚ[X]/(X³ − X − 1)` is `−23`.** -/
theorem discr_ρ : Algebra.discr ℚ pbρ.basis = -23 := by
  have h : Algebra.discr ℚ (⇑bρ) = Algebra.discr ℚ (⇑pbρ.basis) := by
    show Algebra.discr ℚ (⇑(pbρ.basis.reindex (finCongr pbρ_dim))) = _
    rw [Basis.coe_reindex]
    exact Algebra.discr_reindex ℚ pbρ.basis (finCongr pbρ_dim)
  rw [← h, Algebra.discr_def, traceMatrix_bρ, detMρ]

end PDT
