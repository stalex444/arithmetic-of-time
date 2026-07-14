import Mathlib

open Polynomial

namespace Time

noncomputable section

/-- The quartic `x^4 - x - 1`, whose real root is `Q`. -/
def fQ : ℚ[X] := X ^ 4 - X - 1

/-- The cubic `x^3 - x - 1`, whose real root is `ρ`. -/
def fρ : ℚ[X] := X ^ 3 - X - 1

theorem monic_fQ : (fQ).Monic := by
  unfold fQ
  monicity!

theorem monic_fρ : (fρ).Monic := by
  unfold fρ
  monicity!

theorem fQ_ne_zero : fQ ≠ 0 := monic_fQ.ne_zero
theorem fρ_ne_zero : fρ ≠ 0 := monic_fρ.ne_zero

theorem natDegree_fQ : fQ.natDegree = 4 := by
  unfold fQ; compute_degree!

theorem natDegree_fρ : fρ.natDegree = 3 := by
  unfold fρ; compute_degree!

theorem coeff_zero_fQ : fQ.coeff 0 = -1 := by
  unfold fQ; simp

theorem coeff_zero_fρ : fρ.coeff 0 = -1 := by
  unfold fρ; simp

/-- The genuine algebra norm `N(Q) = -1`, where `Q = AdjoinRoot.root (x^4 - x - 1)`.
    `Algebra.norm ℚ` is the determinant of multiplication-by-`Q` on the rank-4
    free ℚ-algebra `AdjoinRoot fQ`; it equals `(-1)^4 · (minpoly Q).coeff 0`. -/
theorem norm_Q :
    Algebra.norm ℚ (AdjoinRoot.root fQ) = -1 := by
  set pb := AdjoinRoot.powerBasis (f := fQ) fQ_ne_zero with hpb
  have hgen : pb.gen = AdjoinRoot.root fQ := AdjoinRoot.powerBasis_gen fQ_ne_zero
  have hmin : minpoly ℚ pb.gen = fQ :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic monic_fQ fQ_ne_zero
  have hdim : pb.dim = 4 := by
    rw [hpb, AdjoinRoot.powerBasis_dim fQ_ne_zero, natDegree_fQ]
  have key := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
  rw [hdim, hmin, coeff_zero_fQ, hgen] at key
  rw [key]
  norm_num

/-- The genuine algebra norm `N(ρ) = 1`, where `ρ = AdjoinRoot.root (x^3 - x - 1)`. -/
theorem norm_ρ :
    Algebra.norm ℚ (AdjoinRoot.root fρ) = 1 := by
  set pb := AdjoinRoot.powerBasis (f := fρ) fρ_ne_zero with hpb
  have hgen : pb.gen = AdjoinRoot.root fρ := AdjoinRoot.powerBasis_gen fρ_ne_zero
  have hmin : minpoly ℚ pb.gen = fρ :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic monic_fρ fρ_ne_zero
  have hdim : pb.dim = 3 := by
    rw [hpb, AdjoinRoot.powerBasis_dim fρ_ne_zero, natDegree_fρ]
  have key := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
  rw [hdim, hmin, coeff_zero_fρ, hgen] at key
  rw [key]
  norm_num

end

end Time
