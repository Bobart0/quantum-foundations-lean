import QuantumFoundations.Complexity.MinComplexity

/-!
# C0 — Non-vacuity

The empty circuit exists for every finite site system.  In addition, the
identity is an exact gate with empty support, so the gate structure itself is
inhabited without any physical assumption.
-/

namespace QuantumFoundations.Complexity

open scoped InnerProductSpace

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

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

/-- Threshold-zero distinguishability is inhabited by the empty circuit. -/
example (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N)) :
    DistinguishesAt e a b 0 ([] : Circuit N d) := by
  unfold DistinguishesAt
  simp only [mul_zero]
  exact norm_nonneg
    (⟪a, Circuit.evalOnH ([] : Circuit N d) e a⟫_ℂ -
      ⟪b, Circuit.evalOnH ([] : Circuit N d) e b⟫_ℂ)

/-- Threshold-zero interference is inhabited by the empty circuit. -/
example (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N)) :
    InterferesAt e a b 0 ([] : Circuit N d) := by
  unfold InterferesAt
  simpa using add_nonneg
    (norm_nonneg ⟪a, Circuit.evalOnH ([] : Circuit N d) e b⟫_ℂ)
    (norm_nonneg ⟪b, Circuit.evalOnH ([] : Circuit N d) e a⟫_ℂ)

/-- An impossible circuit predicate has infinite minimum length. -/
example : minCircuitLength (fun _ : Circuit N d => False) = ⊤ := by
  apply minCircuitLength_eq_top_of_no_witness
  simp

/-- A predicate witnessed by the empty circuit has minimum length zero. -/
example : minCircuitLength (fun _ : Circuit N d => True) = 0 := by
  apply le_antisymm
  · simpa using minCircuitLength_le_of_witness
      ([] : Circuit N d) (show True from trivial)
  · exact bot_le

end

end QuantumFoundations.Complexity
