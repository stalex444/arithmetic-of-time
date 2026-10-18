module
public import PdtQuarticWindowDynamics

@[expose] public section

/-!
# The exact cubic-to-quartic tick-intertwiner obstruction

The cubic coordinate tick satisfies `A³ = A + I`, while the quartic coordinate
tick satisfies `B⁴ = B + I`.  Because the two recurrence polynomials are
coprime, an additive map intertwining the two ticks has zero image.  The proof
below uses the corresponding elementary Bezout cancellation directly.

The concrete conclusion is deliberately narrow: there is no nonzero,
time-independent additive map from the cubic coefficient lattice to the
quartic coefficient lattice that sends every native cubic tick to one native
quartic tick.  It says nothing against nonlinear, time-dependent,
compositum-based, or non-equivariant bridges.
-/

namespace PDT.CubicQuarticBridge

open PDT.RecordBoundary PDT.QuarticWindowDynamics

section Abstract

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

/-- An additive intertwiner between endomorphisms satisfying the cubic and
quartic PDT recurrences is necessarily zero. -/
theorem no_additive_intertwiner
    (A : V →+ V) (B : W →+ W) (L : V →+ W)
    (hA : ∀ x, A (A (A x)) = A x + x)
    (hB : ∀ y, B (B (B (B y))) = B y + y)
    (hL : ∀ x, L (A x) = B (L x)) :
    L = 0 := by
  ext x
  have h3 : B (B (B (L x))) = B (L x) + L x := by
    calc
      B (B (B (L x))) = B (B (L (A x))) := by
        rw [hL x]
      _ = B (L (A (A x))) := by
        rw [hL (A x)]
      _ = L (A (A (A x))) := by
        rw [hL (A (A x))]
      _ = L (A x + x) := by rw [hA x]
      _ = B (L x) + L x := by rw [map_add, hL x]
  have h4_from_cubic : B (B (B (B (L x)))) = B (B (L x)) + B (L x) := by
    simpa only [map_add] using congrArg B h3
  have h2 : B (B (L x)) = L x := by
    have hsum : B (B (L x)) + B (L x) = B (L x) + L x :=
      h4_from_cubic.symm.trans (hB (L x))
    rw [add_comm (B (B (L x))) (B (L x))] at hsum
    exact add_left_cancel hsum
  have h3_short : B (B (B (L x))) = B (L x) := by
    exact congrArg B h2
  have hzero : L x = 0 := by
    have hsum : B (L x) + L x = B (L x) := h3.symm.trans h3_short
    have hsum' : B (L x) + L x = B (L x) + 0 := by simpa using hsum
    exact add_left_cancel hsum'
  simpa using hzero

end Abstract

/-! ## The native coordinate ticks -/

abbrev Cubic := ℤ × ℤ × ℤ

/-- The cubic native tick as an additive endomorphism. -/
def cubicTickHom : Cubic →+ Cubic where
  toFun := PDT.tick
  map_zero' := by simp [PDT.tick]
  map_add' p q := by
    rcases p with ⟨a, b, c⟩
    rcases q with ⟨a', b', c'⟩
    ext <;> simp [PDT.tick, add_comm, add_left_comm]

/-- The quartic native tick as an additive endomorphism. -/
def quarticTickHom : Quad →+ Quad where
  toFun := tick4
  map_zero' := by simp [tick4]
  map_add' p q := by
    rcases p with ⟨a, b, c, d⟩
    rcases q with ⟨a', b', c', d'⟩
    ext <;> simp [tick4, add_comm, add_left_comm]

theorem cubic_tick_recurrence (p : Cubic) :
    cubicTickHom (cubicTickHom (cubicTickHom p)) = cubicTickHom p + p := by
  rcases p with ⟨a, b, c⟩
  ext <;> simp [cubicTickHom, PDT.tick] <;> omega

theorem quartic_tick_recurrence (p : Quad) :
    quarticTickHom (quarticTickHom (quarticTickHom (quarticTickHom p))) =
      quarticTickHom p + p := by
  rcases p with ⟨a, b, c, d⟩
  ext <;> simp [quarticTickHom, tick4] <;> omega

/-- No nonzero additive map carries every native cubic tick into one native
quartic tick. -/
theorem no_cubic_quartic_tick_intertwiner
    (L : Cubic →+ Quad)
    (hL : ∀ p, L (PDT.tick p) = tick4 (L p)) :
    L = 0 := by
  apply no_additive_intertwiner cubicTickHom quarticTickHom L
      cubic_tick_recurrence quartic_tick_recurrence
  intro p
  exact hL p

#print axioms no_additive_intertwiner
#print axioms Cubic
#print axioms cubicTickHom
#print axioms quarticTickHom
#print axioms cubic_tick_recurrence
#print axioms quartic_tick_recurrence
#print axioms no_cubic_quartic_tick_intertwiner

end PDT.CubicQuarticBridge
