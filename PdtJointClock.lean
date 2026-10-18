module
public import PdtTraceCompositum
public import PdtRulerMinpoly

@[expose] public section

/-!
# The joint rho-Q clock and recovery of its factor ticks

The separate cubic and quartic coordinate ticks admit no nonzero additive
one-step intertwiner.  On the degree-12 tensor compositum, however, their two
commuting left-multiplication actions have product equal to multiplication by
the ruler `rho*Q`.  A primitive-element identity recovers each factor
action as a rational polynomial in that single joint action.

This is an internal operator decomposition on the full joint space.  It is not
a projection to a lower-dimensional state space and makes no physical clock or
time identification.
-/

namespace PDT.JointClock

open Polynomial Module TensorProduct

noncomputable section

def rhoInclusion : AdjoinRoot PDT.fρ →ₐ[ℚ] PDT.L :=
  Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ)

def qInclusion : AdjoinRoot PDT.fQ →ₐ[ℚ] PDT.L :=
  Algebra.TensorProduct.includeRight

/-- The cubic generator inside the tensor compositum. -/
def rhoL : PDT.L := rhoInclusion (AdjoinRoot.root PDT.fρ)

/-- The quartic generator inside the tensor compositum. -/
def qL : PDT.L := qInclusion (AdjoinRoot.root PDT.fQ)

/-- The ruler generator inside the tensor compositum. -/
def uL : PDT.L := rhoL * qL

theorem rhoL_cubic : rhoL ^ 3 = rhoL + 1 := by
  calc
    rhoL ^ 3 = rhoInclusion ((AdjoinRoot.root PDT.fρ) ^ 3) := by rw [map_pow]; rfl
    _ = rhoInclusion (AdjoinRoot.root PDT.fρ + 1) := by rw [PDT.rρ_pow_three]
    _ = rhoInclusion (AdjoinRoot.root PDT.fρ) + rhoInclusion 1 := map_add _ _ _
    _ = rhoL + 1 := by rw [map_one]; rfl

theorem qL_quartic : qL ^ 4 = qL + 1 := by
  calc
    qL ^ 4 = qInclusion ((AdjoinRoot.root PDT.fQ) ^ 4) := by rw [map_pow]; rfl
    _ = qInclusion (AdjoinRoot.root PDT.fQ + 1) := by rw [PDT.rQ_pow_four]
    _ = qInclusion (AdjoinRoot.root PDT.fQ) + qInclusion 1 := map_add _ _ _
    _ = qL + 1 := by rw [map_one]; rfl

/-- The integer numerator of the cubic-factor recovery polynomial. -/
noncomputable def rhoNumerator : ℚ[X] :=
  C (-17) + C (-35) * X + C (-26) * X ^ 2 + C (-56) * X ^ 3
    + C 24 * X ^ 4 + C 19 * X ^ 5 + C (-17) * X ^ 6 + C (-105) * X ^ 7
    + C (-59) * X ^ 8 + C (-7) * X ^ 9 + C 16 * X ^ 10 + C 24 * X ^ 11

/-- The explicit rational polynomial recovering the cubic factor. -/
noncomputable def cubicRecovery : ℚ[X] := C (1 / 53 : ℚ) * rhoNumerator

theorem rhoNumerator_joint :
    aeval uL rhoNumerator = (53 : ℚ) • rhoL := by
  have h := PDT.RulerMinpoly.ruler_generates rhoL qL rhoL_cubic qL_quartic
  have hmap (n : ℤ) : algebraMap ℚ PDT.L (n : ℚ) = (n : PDT.L) :=
    map_intCast _ _
  have hm17 : algebraMap ℚ PDT.L (-17 : ℚ) = (-17 : PDT.L) := by
    simpa only [Int.cast_neg, Int.cast_ofNat] using hmap (-17)
  have hm35 : algebraMap ℚ PDT.L (-35 : ℚ) = (-35 : PDT.L) := by
    simpa only [Int.cast_neg, Int.cast_ofNat] using hmap (-35)
  have hm26 : algebraMap ℚ PDT.L (-26 : ℚ) = (-26 : PDT.L) := by
    simpa only [Int.cast_neg, Int.cast_ofNat] using hmap (-26)
  have hm56 : algebraMap ℚ PDT.L (-56 : ℚ) = (-56 : PDT.L) := by
    simpa only [Int.cast_neg, Int.cast_ofNat] using hmap (-56)
  have hm105 : algebraMap ℚ PDT.L (-105 : ℚ) = (-105 : PDT.L) := by
    simpa only [Int.cast_neg, Int.cast_ofNat] using hmap (-105)
  have hm59 : algebraMap ℚ PDT.L (-59 : ℚ) = (-59 : PDT.L) := by
    simpa only [Int.cast_neg, Int.cast_ofNat] using hmap (-59)
  have hm7 : algebraMap ℚ PDT.L (-7 : ℚ) = (-7 : PDT.L) := by
    simpa only [Int.cast_neg, Int.cast_ofNat] using hmap (-7)
  have hp24 : algebraMap ℚ PDT.L (24 : ℚ) = (24 : PDT.L) := by
    simpa only [Int.cast_ofNat] using hmap 24
  have hp19 : algebraMap ℚ PDT.L (19 : ℚ) = (19 : PDT.L) := by
    simpa only [Int.cast_ofNat] using hmap 19
  have hp16 : algebraMap ℚ PDT.L (16 : ℚ) = (16 : PDT.L) := by
    simpa only [Int.cast_ofNat] using hmap 16
  have hp53 : algebraMap ℚ PDT.L (53 : ℚ) = (53 : PDT.L) := by
    simpa only [Int.cast_ofNat] using hmap 53
  rw [Algebra.smul_def]
  simp only [rhoNumerator, map_add, map_mul, map_pow, aeval_C, aeval_X]
  rw [hm17, hm35, hm26, hm56, hp24, hp19, hm105, hm59, hm7, hp16, hp53]
  simp only [uL, mul_pow]
  linear_combination -h

/-- The existing recovery polynomial, now evaluated at the joint generator. -/
theorem rho_from_joint :
    aeval uL cubicRecovery = rhoL := by
  rw [cubicRecovery, map_mul, aeval_C, rhoNumerator_joint]
  rw [← Algebra.smul_def]
  simp [smul_smul]

/-- A rational polynomial recovering the quartic generator from the ruler. -/
noncomputable def qOfRuler : ℚ[X] :=
  X * (cubicRecovery ^ 2 - 1)

theorem q_from_joint : aeval uL qOfRuler = qL := by
  have hinv : rhoL * (rhoL ^ 2 - 1) = 1 := by
    linear_combination rhoL_cubic
  simp only [qOfRuler, map_mul, map_sub, map_pow, map_one, aeval_X]
  rw [rho_from_joint]
  calc
    uL * (rhoL ^ 2 - 1) = qL * (rhoL * (rhoL ^ 2 - 1)) := by
      simp only [uL]
      ring
    _ = qL := by rw [hinv, mul_one]

/-! ## Left-multiplication clocks on the full compositum -/

/-- Cubic factor tick acting on the full 12-dimensional compositum. -/
def cubicFactorTick : Module.End ℚ PDT.L := Algebra.lmul ℚ PDT.L rhoL

/-- Quartic factor tick acting on the full 12-dimensional compositum. -/
def quarticFactorTick : Module.End ℚ PDT.L := Algebra.lmul ℚ PDT.L qL

/-- The single ruler tick acting on the full 12-dimensional compositum. -/
def jointTick : Module.End ℚ PDT.L := Algebra.lmul ℚ PDT.L uL

theorem joint_factorizes : jointTick = cubicFactorTick * quarticFactorTick := by
  exact map_mul (Algebra.lmul ℚ PDT.L) rhoL qL

theorem factor_ticks_commute :
    cubicFactorTick * quarticFactorTick = quarticFactorTick * cubicFactorTick := by
  calc
    cubicFactorTick * quarticFactorTick = Algebra.lmul ℚ PDT.L (rhoL * qL) := by
      exact (map_mul (Algebra.lmul ℚ PDT.L) rhoL qL).symm
    _ = Algebra.lmul ℚ PDT.L (qL * rhoL) := by rw [mul_comm]
    _ = quarticFactorTick * cubicFactorTick := by
      exact map_mul (Algebra.lmul ℚ PDT.L) qL rhoL

/-- Polynomial evaluation commutes with the left regular representation. -/
theorem lmul_aeval (x : PDT.L) (p : ℚ[X]) :
    aeval (Algebra.lmul ℚ PDT.L x) p = Algebra.lmul ℚ PDT.L (aeval x p) := by
  rw [aeval_def, aeval_def]
  simpa using
    (Polynomial.hom_eval₂ p (algebraMap ℚ PDT.L)
      (Algebra.lmul ℚ PDT.L).toRingHom x).symm

/-- The cubic factor tick is a rational polynomial in the joint ruler tick. -/
theorem recover_cubic_tick :
    aeval jointTick cubicRecovery = cubicFactorTick := by
  rw [jointTick, lmul_aeval, rho_from_joint]
  rfl

/-- The quartic factor tick is a rational polynomial in the joint ruler tick. -/
theorem recover_quartic_tick :
    aeval jointTick qOfRuler = quarticFactorTick := by
  rw [jointTick, lmul_aeval, q_from_joint]
  rfl

/-- The positive joint-space bridge: one ruler operator factors into two
commuting native factor actions and polynomially recovers both. -/
theorem joint_clock_decomposition :
    jointTick = cubicFactorTick * quarticFactorTick ∧
      cubicFactorTick * quarticFactorTick = quarticFactorTick * cubicFactorTick ∧
      aeval jointTick cubicRecovery = cubicFactorTick ∧
      aeval jointTick qOfRuler = quarticFactorTick :=
  ⟨joint_factorizes, factor_ticks_commute, recover_cubic_tick, recover_quartic_tick⟩

#print axioms rhoInclusion
#print axioms qInclusion
#print axioms rhoL
#print axioms qL
#print axioms uL
#print axioms rhoL_cubic
#print axioms qL_quartic
#print axioms rhoNumerator
#print axioms cubicRecovery
#print axioms rhoNumerator_joint
#print axioms rho_from_joint
#print axioms qOfRuler
#print axioms q_from_joint
#print axioms cubicFactorTick
#print axioms quarticFactorTick
#print axioms jointTick
#print axioms joint_factorizes
#print axioms factor_ticks_commute
#print axioms lmul_aeval
#print axioms recover_cubic_tick
#print axioms recover_quartic_tick
#print axioms joint_clock_decomposition

end

end PDT.JointClock
