import QuantumFoundations.Complexity.ApproxRecordPersistence

/-!
# C0/C6/C7/C8 — Non-vacuity

The empty circuit exists for every finite site system.  In addition, the
identity is an exact gate with empty support, so the gate structure itself is
inhabited without any physical assumption.  C7's reversible-evolution
certificate is inhabited by the empty circuit in both directions.
Exact record and phase-flip hypotheses also inhabit their C8 approximate
counterparts at error zero, and monotonicity enlarges any such error budget.
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

/-- The empty forward/backward pair is a reversible evolution with zero
conjugation overhead. -/
example :
    (ReversibleCircuitEvolution.reversibleEmptyEvolution N d).overhead = 0 := by
  rfl

/-- Canonical inversion is non-vacuous already on the empty circuit. -/
example : Circuit.inverse ([] : Circuit N d) = [] := by
  rfl

/-- Unitary circuit evolution preserves a supplied unit-norm hypothesis, so
evolved normalized branches do not require renormalization. -/
example (E : Circuit N d) (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (a : H (d ^ N)) (ha : ‖a‖ = 1) :
    ‖Circuit.evalOnH E e a‖ = 1 := by
  exact Circuit.evalOnH_unit E e ha

/-- Exact fixing and rejection are an approximate record with zero error. -/
example (P : H n →ₗ[ℂ] H n) (target other : H n)
    (hfix : P target = target) (hreject : P other = 0) :
    ApproxRecordFor P target other 0 :=
  approxRecordFor_zero_of_fixes_rejects hfix hreject

/-- Any nonnegative budget weakens the preceding exact witness. -/
example (P : H n →ₗ[ℂ] H n) (target other : H n)
    (hfix : P target = target) (hreject : P other = 0)
    (η : ℝ) (hη : 0 ≤ η) : ApproxRecordFor P target other η := by
  exact (approxRecordFor_zero_of_fixes_rejects hfix hreject).mono hη

/-- An exact record phase flip is an approximate implementation at error
zero. -/
example (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (D : Circuit N d)
    (Λ : LabeledResolution (d ^ N) K) (j : Fin K)
    (a b : H (d ^ N)) (hD : ImplementsRecordPhaseFlip e D Λ j) :
    ApproximatesRecordPhaseFlipOn e D Λ j a b 0 :=
  implementsRecordPhaseFlip_gives_approximation_zero e D Λ j a b hD

end

end QuantumFoundations.Complexity
