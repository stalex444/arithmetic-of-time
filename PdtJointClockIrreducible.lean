module
public import PdtJointClock
public import Mathlib.Algebra.Module.Submodule.Invariant

@[expose] public section

/-!
# Irreducibility of the joint rho-Q clock

If an element `u` generates a field extension `K/F`, then left
multiplication by `u` has no nonzero proper `F`-invariant submodule.  The
proof packages the scalars preserving a candidate submodule as a subalgebra:
invariance under `u` then implies invariance under every element of `K`.

For the PDT compositum, the explicit recovery polynomials show that the joint
generator `rho*Q` contains both factor generators.  Hence its rational
left-multiplication clock is irreducible on the full degree-12 compositum.

This is an algebraic statement over `Q`.  It neither selects a real
four-dimensional subspace nor identifies a physical spacetime.
-/

namespace PDT.JointClock

open Module TensorProduct

noncomputable section

/-! ## A general primitive-element lemma -/

/-- The scalars whose left action preserves an `F`-submodule of `K`. -/
def preservingScalars {F K : Type*} [Field F] [Field K] [Algebra F K]
    (W : Submodule F K) : Subalgebra F K where
  carrier := {a | ∀ x, x ∈ W → a * x ∈ W}
  zero_mem' := by
    intro x hx
    simp
  one_mem' := by
    intro x hx
    simpa using hx
  add_mem' := by
    intro a b ha hb x hx
    simpa [add_mul] using W.add_mem (ha x hx) (hb x hx)
  mul_mem' := by
    intro a b ha hb x hx
    rw [mul_assoc]
    exact ha (b * x) (hb x hx)
  algebraMap_mem' := by
    intro r x hx
    rw [← Algebra.smul_def]
    exact W.smul_mem r hx

/-- A primitive left-multiplication operator has only the zero and full
invariant submodules over the base field. -/
theorem invariant_submodule_eq_bot_or_top
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (u : K) (hu : Algebra.adjoin F ({u} : Set K) = ⊤)
    (W : Submodule F K) (hW : ∀ x ∈ W, u * x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    have hu_preserves : u ∈ preservingScalars W := by
      exact hW
    have hpreserves : preservingScalars W = ⊤ := by
      apply le_antisymm le_top
      rw [← hu]
      apply Algebra.adjoin_le
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact hu_preserves
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W).mp hbot
    rw [Submodule.eq_top_iff']
    intro y
    have hyw : y * w⁻¹ ∈ preservingScalars W := by
      rw [hpreserves]
      trivial
    have hmem : (y * w⁻¹) * w ∈ W := hyw w hw
    simpa [mul_assoc, hw0] using hmem

/-! ## The concrete joint clock -/

/-- The ruler generator `rho*Q` generates the entire tensor compositum as a
rational algebra. -/
theorem joint_adjoin_eq_top :
    Algebra.adjoin ℚ ({uL} : Set PDT.L) = ⊤ := by
  let S : Subalgebra ℚ PDT.L := Algebra.adjoin ℚ ({uL} : Set PDT.L)
  have hrho : rhoL ∈ S := by
    rw [← rho_from_joint]
    simpa only [S] using
      (Polynomial.aeval_mem_adjoin_singleton (R := ℚ) (A := PDT.L)
        (x := uL) (p := cubicRecovery))
  have hq : qL ∈ S := by
    rw [← q_from_joint]
    simpa only [S] using
      (Polynomial.aeval_mem_adjoin_singleton (R := ℚ) (A := PDT.L)
        (x := uL) (p := qOfRuler))
  have hleft : ∀ a : AdjoinRoot PDT.fρ, rhoInclusion a ∈ S := by
    intro a
    have htop : Algebra.adjoin ℚ ({AdjoinRoot.root PDT.fρ} :
        Set (AdjoinRoot PDT.fρ)) = ⊤ := AdjoinRoot.adjoinRoot_eq_top
    have ha : a ∈ Algebra.adjoin ℚ ({AdjoinRoot.root PDT.fρ} :
        Set (AdjoinRoot PDT.fρ)) := by
      rw [htop]
      trivial
    have hle : Algebra.adjoin ℚ ({AdjoinRoot.root PDT.fρ} :
        Set (AdjoinRoot PDT.fρ)) ≤ S.comap rhoInclusion := by
      apply Algebra.adjoin_le
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact hrho
    exact hle ha
  have hright : ∀ b : AdjoinRoot PDT.fQ, qInclusion b ∈ S := by
    intro b
    have htop : Algebra.adjoin ℚ ({AdjoinRoot.root PDT.fQ} :
        Set (AdjoinRoot PDT.fQ)) = ⊤ := AdjoinRoot.adjoinRoot_eq_top
    have hb : b ∈ Algebra.adjoin ℚ ({AdjoinRoot.root PDT.fQ} :
        Set (AdjoinRoot PDT.fQ)) := by
      rw [htop]
      trivial
    have hle : Algebra.adjoin ℚ ({AdjoinRoot.root PDT.fQ} :
        Set (AdjoinRoot PDT.fQ)) ≤ S.comap qInclusion := by
      apply Algebra.adjoin_le
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact hq
    exact hle hb
  apply le_antisymm le_top
  rw [← Algebra.TensorProduct.adjoin_tmul_eq_top]
  apply Algebra.adjoin_le
  intro t ht
  rcases ht with ⟨a, b, rfl⟩
  have hab := S.mul_mem (hleft a) (hright b)
  have heq : rhoInclusion a * qInclusion b = a ⊗ₜ[ℚ] b := by
    change (a ⊗ₜ[ℚ] (1 : AdjoinRoot PDT.fQ)) *
      ((1 : AdjoinRoot PDT.fρ) ⊗ₜ[ℚ] b) = a ⊗ₜ[ℚ] b
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [← heq]
  exact hab

/-- Every rational submodule invariant under the joint ruler tick is either
zero or the entire degree-12 compositum. -/
theorem jointTick_invariant_submodule_eq_bot_or_top
    (W : Submodule ℚ PDT.L) (hW : W ∈ jointTick.invtSubmodule) :
    W = ⊥ ∨ W = ⊤ := by
  letI : Field PDT.L := PDT.fieldL
  apply invariant_submodule_eq_bot_or_top uL joint_adjoin_eq_top W
  intro x hx
  exact hW hx

/-- The joint clock has no nonzero proper rational invariant subsystem. -/
theorem no_proper_jointTick_invariant_submodule :
    ¬ ∃ W : Submodule ℚ PDT.L,
      W ≠ ⊥ ∧ W ≠ ⊤ ∧ W ∈ jointTick.invtSubmodule := by
  rintro ⟨W, hbot, htop, hW⟩
  rcases jointTick_invariant_submodule_eq_bot_or_top W hW with h | h
  · exact hbot h
  · exact htop h

#print axioms preservingScalars
#print axioms invariant_submodule_eq_bot_or_top
#print axioms joint_adjoin_eq_top
#print axioms jointTick_invariant_submodule_eq_bot_or_top
#print axioms no_proper_jointTick_invariant_submodule

end

end PDT.JointClock
