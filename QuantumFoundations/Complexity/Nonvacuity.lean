import QuantumFoundations.Complexity.Defs

/-!
# C0 — Non-vacuity

The empty circuit exists for every finite site system.  In addition, the
identity is an exact gate with empty support, so the gate structure itself is
inhabited without any physical assumption.
-/

namespace QuantumFoundations.Complexity

open QuantumFoundations.BranchesRiedel

/-- The identity gate, declared local to the empty region. -/
noncomputable def identityGate (N d : ℕ) : TwoLocalGate N d where
  unitary := LinearIsometryEquiv.refl ℂ (Sites N d)
  support := ∅
  locality := Circuit.isLocalTo_id_empty
  support_card_le_two := by simp

/-- The empty circuit has length zero and evaluates to the identity. -/
example :
    Circuit.length ([] : Circuit N d) = 0 ∧
      Circuit.eval ([] : Circuit N d) = LinearMap.id := by
  simp

/-- A singleton identity circuit is a concrete nonempty circuit. -/
example : Circuit.eval [identityGate N d] = LinearMap.id := by
  ext x
  rfl

end QuantumFoundations.Complexity
