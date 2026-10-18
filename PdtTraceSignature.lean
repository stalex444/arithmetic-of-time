module
public import Mathlib
public import PdtSignature
public import PdtSignatureRho
public import PdtTraceLink

@[expose] public section

/-!
# Sylvester signatures of the trace forms of `ℚ[x]/(x⁴ − x − 1)` and `ℚ[x]/(x³ − x − 1)`

`PdtSignature` and `PdtSignatureRho` exhibit explicit rational congruences carrying the
Gram matrices `M` and `Mρ` to diagonal matrices `D = diag(4, 4, -9/4, 283/36)` and
`Dρ = diag(3, 2, -23/6)`, and `PdtTraceLink` proves that `M` and `Mρ` really are the Gram
matrices of the trace forms in the power bases.

This file upgrades those matrix statements to statements about the *quadratic form itself*,
using Mathlib's basis-free invariants `sigPos` and `sigNeg` (the maximal dimension of a
positive- resp. negative-definite subspace).  The results

* `sigPos_traceQ`, `sigNeg_traceQ` : the trace form of `ℚ[x]/(x⁴ − x − 1)` has
  signature `(3, 1)`;
* `sigPos_traceρ`, `sigNeg_traceρ` : the trace form of `ℚ[x]/(x³ − x − 1)` has
  signature `(2, 1)`

are therefore *intrinsic invariants of the field*, independent of the chosen basis and of
the chosen diagonalising congruence.  The uniqueness half of Sylvester's law of inertia is
supplied by `QuadraticForm.sigPos_of_equiv_weightedSumSquares`.
-/

namespace PDT

open Module QuadraticMap

/-! ## The quartic side: `K = ℚ[x]/(x⁴ − x − 1)` -/

/-- The trace form `(x, y) ↦ Tr_{K/ℚ}(x y)` of `K = ℚ[x]/(x⁴ − x − 1)`, viewed as a
quadratic form `x ↦ Tr_{K/ℚ}(x²)`. -/
noncomputable def qTraceQ : QuadraticForm ℚ (AdjoinRoot fQ) :=
  LinearMap.BilinMap.toQuadraticMap (Algebra.traceForm ℚ (AdjoinRoot fQ))

theorem qTraceQ_apply (x : AdjoinRoot fQ) :
    qTraceQ x = Algebra.trace ℚ (AdjoinRoot fQ) (x * x) := by
  rw [qTraceQ, LinearMap.BilinMap.toQuadraticMap_apply, Algebra.traceForm_apply]

/-- The Gram matrix entries of the trace form in the power basis are the entries of `M`. -/
theorem traceForm_bQ (i j : Fin 4) :
    Algebra.traceForm ℚ (AdjoinRoot fQ) (bQ i) (bQ j) = M i j := by
  have h : Algebra.traceMatrix ℚ (⇑bQ) i j
      = Algebra.traceForm ℚ (AdjoinRoot fQ) (bQ i) (bQ j) := by
    rw [Algebra.traceMatrix_apply]
  rw [traceMatrix_bQ] at h
  exact h.symm

/-- The value of the trace form on a general combination of the power basis. -/
theorem qTraceQ_comb (a₀ a₁ a₂ a₃ : ℚ) :
    qTraceQ (a₀ • bQ 0 + a₁ • bQ 1 + a₂ • bQ 2 + a₃ • bQ 3)
      = 4 * a₀ * a₀ + 6 * a₀ * a₃ + 6 * a₁ * a₂ + 8 * a₁ * a₃ + 4 * a₂ * a₂ + 3 * a₃ * a₃ := by
  rw [qTraceQ, LinearMap.BilinMap.toQuadraticMap_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    traceForm_bQ, M, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  ring

/-! ### The diagonalising basis: the columns of `P` -/

/-- The basis of `K` whose transition matrix from the power basis is `P`; by
`PDT.congruence` it is orthogonal for the trace form. -/
noncomputable def cQ : Basis (Fin 4) ℚ (AdjoinRoot fQ) :=
  bQ.map (Matrix.toLinearEquiv bQ P P_isUnit)

theorem cQ_apply (i : Fin 4) : cQ i = ∑ j, P j i • bQ j := by
  show (bQ.map (Matrix.toLinearEquiv bQ P P_isUnit)) i = _
  rw [Basis.map_apply]
  simp

theorem sum_cQ (w : Fin 4 → ℚ) :
    ∑ i, w i • cQ i
      = (w 0 + (-3 / 4) * w 3) • bQ 0 + (w 2 + (16 / 9) * w 3) • bQ 1
        + (w 1 + (-3 / 4) * w 2 + (-4 / 3) * w 3) • bQ 2 + (w 3) • bQ 3 := by
  simp only [cQ_apply, Fin.sum_univ_four, P, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const]
  module

/-- The basis representation of the trace form in the basis `cQ` is the weighted sum of
squares with weights the diagonal of `D = diag(4, 4, -9/4, 283/36)`. -/
theorem basisRepr_cQ_apply (w : Fin 4 → ℚ) :
    qTraceQ.basisRepr cQ w = weightedSumSquares ℚ (fun i : Fin 4 => D i i) w := by
  rw [QuadraticMap.basisRepr_apply, sum_cQ, qTraceQ_comb, weightedSumSquares_apply]
  simp only [Fin.sum_univ_four, smul_eq_mul, D, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const]
  ring

theorem basisRepr_cQ : qTraceQ.basisRepr cQ = weightedSumSquares ℚ (fun i : Fin 4 => D i i) := by
  ext w
  exact basisRepr_cQ_apply w

/-- **The quartic trace form is equivalent to `diag(4, 4, -9/4, 283/36)`.** -/
theorem qTraceQ_equiv :
    QuadraticMap.Equivalent qTraceQ (weightedSumSquares ℚ (fun i : Fin 4 => D i i)) := by
  refine ⟨?_⟩
  rw [← basisRepr_cQ]
  exact QuadraticMap.isometryEquivBasisRepr qTraceQ cQ

/-! ### The signature -/

/-- **The trace form of `ℚ[x]/(x⁴ − x − 1)` has three positive squares.** -/
theorem sigPos_traceQ : sigPos qTraceQ = 3 := by
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares qTraceQ_equiv, Set.ncard_eq_three]
  refine ⟨0, 1, 3, by decide, by decide, by decide, ?_⟩
  ext i
  fin_cases i <;> norm_num [D] <;> decide

/-- **The trace form of `ℚ[x]/(x⁴ − x − 1)` has one negative square.** -/
theorem sigNeg_traceQ : sigNeg qTraceQ = 1 := by
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares qTraceQ_equiv, Set.ncard_eq_one]
  refine ⟨2, ?_⟩
  ext i
  fin_cases i <;> norm_num [D] <;> decide

/-- **Signature `(3, 1)` for `ℚ[x]/(x⁴ − x − 1)`, as an intrinsic invariant.** -/
theorem traceForm_signature_Q : sigPos qTraceQ = 3 ∧ sigNeg qTraceQ = 1 :=
  ⟨sigPos_traceQ, sigNeg_traceQ⟩

/-! ## The cubic side: `k = ℚ[x]/(x³ − x − 1)` -/

/-- The trace form `(x, y) ↦ Tr_{k/ℚ}(x y)` of `k = ℚ[x]/(x³ − x − 1)`, viewed as a
quadratic form `x ↦ Tr_{k/ℚ}(x²)`. -/
noncomputable def qTraceρ : QuadraticForm ℚ (AdjoinRoot fρ) :=
  LinearMap.BilinMap.toQuadraticMap (Algebra.traceForm ℚ (AdjoinRoot fρ))

theorem qTraceρ_apply (x : AdjoinRoot fρ) :
    qTraceρ x = Algebra.trace ℚ (AdjoinRoot fρ) (x * x) := by
  rw [qTraceρ, LinearMap.BilinMap.toQuadraticMap_apply, Algebra.traceForm_apply]

/-- The Gram matrix entries of the trace form in the power basis are the entries of `Mρ`. -/
theorem traceForm_bρ (i j : Fin 3) :
    Algebra.traceForm ℚ (AdjoinRoot fρ) (bρ i) (bρ j) = Mρ i j := by
  have h : Algebra.traceMatrix ℚ (⇑bρ) i j
      = Algebra.traceForm ℚ (AdjoinRoot fρ) (bρ i) (bρ j) := by
    rw [Algebra.traceMatrix_apply]
  rw [traceMatrix_bρ] at h
  exact h.symm

/-- The value of the trace form on a general combination of the power basis. -/
theorem qTraceρ_comb (a₀ a₁ a₂ : ℚ) :
    qTraceρ (a₀ • bρ 0 + a₁ • bρ 1 + a₂ • bρ 2)
      = 3 * a₀ * a₀ + 4 * a₀ * a₂ + 2 * a₁ * a₁ + 6 * a₁ * a₂ + 2 * a₂ * a₂ := by
  rw [qTraceρ, LinearMap.BilinMap.toQuadraticMap_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    traceForm_bρ, Mρ, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  ring

/-- The basis of `k` whose transition matrix from the power basis is `Pρ`; by
`PDT.congruenceρ` it is orthogonal for the trace form. -/
noncomputable def cρ : Basis (Fin 3) ℚ (AdjoinRoot fρ) :=
  bρ.map (Matrix.toLinearEquiv bρ Pρ Pρ_isUnit)

theorem cρ_apply (i : Fin 3) : cρ i = ∑ j, Pρ j i • bρ j := by
  show (bρ.map (Matrix.toLinearEquiv bρ Pρ Pρ_isUnit)) i = _
  rw [Basis.map_apply]
  simp

theorem sum_cρ (w : Fin 3 → ℚ) :
    ∑ i, w i • cρ i
      = (w 0 + (-2 / 3) * w 2) • bρ 0 + (w 1 + (-3 / 2) * w 2) • bρ 1 + (w 2) • bρ 2 := by
  simp only [cρ_apply, Fin.sum_univ_three, Pρ, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const]
  module

/-- The basis representation of the trace form in the basis `cρ` is the weighted sum of
squares with weights the diagonal of `Dρ = diag(3, 2, -23/6)`. -/
theorem basisRepr_cρ_apply (w : Fin 3 → ℚ) :
    qTraceρ.basisRepr cρ w = weightedSumSquares ℚ (fun i : Fin 3 => Dρ i i) w := by
  rw [QuadraticMap.basisRepr_apply, sum_cρ, qTraceρ_comb, weightedSumSquares_apply]
  simp only [Fin.sum_univ_three, smul_eq_mul, Dρ, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const]
  ring

theorem basisRepr_cρ : qTraceρ.basisRepr cρ = weightedSumSquares ℚ (fun i : Fin 3 => Dρ i i) := by
  ext w
  exact basisRepr_cρ_apply w

/-- **The cubic trace form is equivalent to `diag(3, 2, -23/6)`.** -/
theorem qTraceρ_equiv :
    QuadraticMap.Equivalent qTraceρ (weightedSumSquares ℚ (fun i : Fin 3 => Dρ i i)) := by
  refine ⟨?_⟩
  rw [← basisRepr_cρ]
  exact QuadraticMap.isometryEquivBasisRepr qTraceρ cρ

/-- **The trace form of `ℚ[x]/(x³ − x − 1)` has two positive squares.** -/
theorem sigPos_traceρ : sigPos qTraceρ = 2 := by
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares qTraceρ_equiv, Set.ncard_eq_two]
  refine ⟨0, 1, by decide, ?_⟩
  ext i
  fin_cases i <;> norm_num [Dρ]

/-- **The trace form of `ℚ[x]/(x³ − x − 1)` has one negative square.** -/
theorem sigNeg_traceρ : sigNeg qTraceρ = 1 := by
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares qTraceρ_equiv, Set.ncard_eq_one]
  refine ⟨2, ?_⟩
  ext i
  fin_cases i <;> norm_num [Dρ] <;> decide

/-- **Signature `(2, 1)` for `ℚ[x]/(x³ − x − 1)`, as an intrinsic invariant.** -/
theorem traceForm_signature_ρ : sigPos qTraceρ = 2 ∧ sigNeg qTraceρ = 1 :=
  ⟨sigPos_traceρ, sigNeg_traceρ⟩

end PDT
