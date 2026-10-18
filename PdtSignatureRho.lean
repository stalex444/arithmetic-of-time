module
public import Mathlib

@[expose] public section

namespace PDT
open Matrix

/-!
# The (2,1) signature of the trace form of K = ℚ[x]/(x³ − x − 1)  (the ρ / 3-space side)

Companion to `PdtSignature` (the quartic Q / 4D side, signature (3,1)). The cubic
ρ = real root of x³ − x − 1 governs 3-space; its trace form has signature (2,1).
Power sums of the roots (Newton, e₁=0, e₂=−1, e₃=1): p₀=3, p₁=0, p₂=2, p₃=3, p₄=2,
so the Gram matrix in the power basis {1,x,x²} is `Mρ = !![3,0,2; 0,2,3; 2,3,2]`
(Mρ_{ij} = p_{i+j}). We prove, all kernel-checked: `det Mρ = −23 = disc(x³−x−1)`,
and an explicit ℚ-congruence `Pρᵀ Mρ Pρ = Dρ = diag(3, 2, −23/6)` with two positive
and one negative diagonal entry, so by Sylvester's law the signature is (2,1).
-/

def Mρ : Matrix (Fin 3) (Fin 3) ℚ := !![3,0,2; 0,2,3; 2,3,2]
def Pρ : Matrix (Fin 3) (Fin 3) ℚ := !![1,0,-2/3; 0,1,-3/2; 0,0,1]
def Dρ : Matrix (Fin 3) (Fin 3) ℚ := !![3,0,0; 0,2,0; 0,0,-23/6]

theorem Mρ_symm : Mρ.IsSymm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Mρ, Matrix.transpose_apply]

theorem detMρ : Mρ.det = -23 := by
  simp [Matrix.det_fin_three, Mρ]; norm_num

theorem detMρ_neg : Mρ.det < 0 := by rw [detMρ]; norm_num

theorem congruenceρ : Pρ.transpose * Mρ * Pρ = Dρ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pρ, Mρ, Dρ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;> norm_num

theorem detPρ : Pρ.det = 1 := by
  simp [Matrix.det_fin_three, Pρ]

theorem Pρ_isUnit : IsUnit Pρ.det := by rw [detPρ]; exact isUnit_one

theorem Dρ_isDiag : Dρ.IsDiag := by
  intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [Dρ]

theorem Dρ00_pos : (0:ℚ) < Dρ 0 0 := by show (0:ℚ) < 3; norm_num
theorem Dρ11_pos : (0:ℚ) < Dρ 1 1 := by show (0:ℚ) < 2; norm_num
theorem Dρ22_neg : Dρ 2 2 < (0:ℚ) := by show (-23/6:ℚ) < 0; norm_num

/-- **The (2,1) signature theorem (ρ / 3-space side).** An explicit invertible ℚ-congruence
carries the trace form `Mρ` to `diag(3, 2, −23/6)` (two positive, one negative); with
`det Mρ = −23 < 0` (odd # of negative signs) this pins the signature as (2,1) by Sylvester. -/
theorem signature_2_1 :
    Mρ.IsSymm ∧ Pρ.transpose * Mρ * Pρ = Dρ ∧ IsUnit Pρ.det ∧ Dρ.IsDiag ∧
    (0 < Dρ 0 0 ∧ 0 < Dρ 1 1) ∧ Dρ 2 2 < 0 ∧ Mρ.det = -23 :=
  ⟨Mρ_symm, congruenceρ, Pρ_isUnit, Dρ_isDiag, ⟨Dρ00_pos, Dρ11_pos⟩, Dρ22_neg, detMρ⟩

end PDT

/-! ### Axiom audit -/

#print axioms PDT.Mρ_symm
#print axioms PDT.detMρ
#print axioms PDT.detMρ_neg
#print axioms PDT.congruenceρ
#print axioms PDT.detPρ
#print axioms PDT.Pρ_isUnit
#print axioms PDT.Dρ_isDiag
#print axioms PDT.Dρ00_pos
#print axioms PDT.Dρ11_pos
#print axioms PDT.Dρ22_neg
#print axioms PDT.signature_2_1
