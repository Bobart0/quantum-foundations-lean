import QuantumFoundations.Complexity.CircuitConjugation

/-!
# C7a — Canonical inverse circuits

The inverse of a local unitary gate is local to the same support.  At the
matrix-element level its kernel is the conjugate of the original kernel with
the two restricted configurations exchanged.  Reversing a circuit list and
inverting every gate therefore gives a canonical inverse circuit of the same
length and support.
-/

namespace QuantumFoundations.Complexity

open scoped InnerProductSpace ComplexConjugate

open QuantumFoundations.BranchesRiedel

noncomputable section

/-- Locality is preserved by taking the inverse of a unitary operator. -/
theorem isLocalTo_unitary_symm {A : Finset (Fin N)}
    (U : Sites N d ≃ₗᵢ[ℂ] Sites N d)
    (hU : IsLocalTo U.toLinearIsometry.toLinearMap A) :
    IsLocalTo U.symm.toLinearIsometry.toLinearMap A := by
  classical
  obtain ⟨s, hs⟩ := hU
  refine ⟨fun g k => star (s k g), ?_⟩
  intro g k
  have hinner :
      ⟪(EuclideanSpace.single g (1 : ℂ) : Sites N d),
        U.symm (EuclideanSpace.single k (1 : ℂ))⟫_ℂ =
        star ⟪(EuclideanSpace.single k (1 : ℂ) : Sites N d),
          U (EuclideanSpace.single g (1 : ℂ))⟫_ℂ := by
    calc
      _ = ⟪U (EuclideanSpace.single g (1 : ℂ)),
          U (U.symm (EuclideanSpace.single k (1 : ℂ)))⟫_ℂ :=
        (U.inner_map_map _ _).symm
      _ = ⟪U (EuclideanSpace.single g (1 : ℂ)),
          (EuclideanSpace.single k (1 : ℂ) : Sites N d)⟫_ℂ := by
        rw [U.apply_symm_apply]
      _ = _ := (inner_conj_symm _ _).symm
  change ⟪(EuclideanSpace.single g (1 : ℂ) : Sites N d),
    U.symm (EuclideanSpace.single k (1 : ℂ))⟫_ℂ = _
  have hs' :
      ⟪(EuclideanSpace.single k (1 : ℂ) : Sites N d),
        U (EuclideanSpace.single g (1 : ℂ))⟫_ℂ =
        if AgreesOff A k g then
          s (k ∘ Subtype.val) (g ∘ Subtype.val) else 0 := by
    simpa using hs k g
  rw [hinner, hs']
  by_cases h : AgreesOff A g k
  · have hk : AgreesOff A k g := fun x hx => (h x hx).symm
    simp [h, hk]
  · have hk : ¬ AgreesOff A k g := by
      intro hk
      exact h (fun x hx => (hk x hx).symm)
    simp [h, hk]

namespace TwoLocalGate

/-- The inverse gate, with exactly the same declared support. -/
def inverse (G : TwoLocalGate N d) : TwoLocalGate N d where
  unitary := G.unitary.symm
  support := G.support
  locality := isLocalTo_unitary_symm G.unitary G.locality
  support_card_le_two := G.support_card_le_two

@[simp] theorem inverse_unitary (G : TwoLocalGate N d) :
    G.inverse.unitary = G.unitary.symm := rfl

@[simp] theorem inverse_support (G : TwoLocalGate N d) :
    G.inverse.support = G.support := rfl

@[simp] theorem inverse_inverse (G : TwoLocalGate N d) :
    G.inverse.inverse = G := by
  cases G
  rfl

end TwoLocalGate

namespace Circuit

/-- Canonical inverse: reverse chronological order and invert every gate. -/
def inverse : Circuit N d → Circuit N d
  | [] => []
  | G :: C => inverse C ++ [G.inverse]

@[simp] theorem inverse_nil : inverse ([] : Circuit N d) = [] := rfl

@[simp] theorem inverse_cons (G : TwoLocalGate N d) (C : Circuit N d) :
    inverse (G :: C) = inverse C ++ [G.inverse] := rfl

theorem support_append (C D : Circuit N d) :
    support (C ++ D) = support C ∪ support D := by
  induction C with
  | nil => simp
  | cons G C ih =>
      simp [ih, Finset.union_assoc]

/-- Canonical inversion preserves circuit length. -/
@[simp] theorem inverse_length (C : Circuit N d) :
    length (inverse C) = length C := by
  induction C with
  | nil => rfl
  | cons G C ih =>
      change List.length (inverse C ++ [G.inverse]) = List.length (G :: C)
      simp only [List.length_append, List.length_cons, List.length_nil]
      change List.length (inverse C) = List.length C at ih
      omega

/-- Canonical inversion preserves the union support. -/
@[simp] theorem inverse_support (C : Circuit N d) :
    support (inverse C) = support C := by
  induction C with
  | nil => rfl
  | cons G C ih =>
      rw [inverse_cons, support_append, support_cons, ih]
      simp [Finset.union_comm]

theorem inverse_append (C D : Circuit N d) :
    inverse (C ++ D) = inverse D ++ inverse C := by
  induction C with
  | nil => simp
  | cons G C ih =>
      simp only [List.cons_append, inverse_cons, ih]
      simp [List.append_assoc]

/-- Canonical circuit inversion is involutive. -/
@[simp] theorem inverse_inverse (C : Circuit N d) :
    inverse (inverse C) = C := by
  induction C with
  | nil => rfl
  | cons G C ih =>
      rw [inverse_cons, inverse_append, inverse_cons, ih]
      simp

/-- The canonical inverse evaluates to a left inverse. -/
theorem eval_inverse_comp (C : Circuit N d) :
    eval (inverse C) ∘ₗ eval C = LinearMap.id := by
  induction C with
  | nil =>
      ext x
      rfl
  | cons G C ih =>
      apply LinearMap.ext
      intro x
      rw [inverse_cons, eval_append, eval_singleton, eval_cons]
      change G.unitary.symm (eval (inverse C) (eval C (G.unitary x))) = x
      have h := congrArg
        (fun T : Sites N d →ₗ[ℂ] Sites N d => T (G.unitary x)) ih
      change eval (inverse C) (eval C (G.unitary x)) = G.unitary x at h
      rw [h, G.unitary.symm_apply_apply]

/-- The canonical inverse evaluates to a right inverse. -/
theorem eval_comp_inverse (C : Circuit N d) :
    eval C ∘ₗ eval (inverse C) = LinearMap.id := by
  induction C with
  | nil =>
      ext x
      rfl
  | cons G C ih =>
      apply LinearMap.ext
      intro x
      rw [inverse_cons, eval_append, eval_singleton, eval_cons]
      change eval C (G.unitary (G.unitary.symm (eval (inverse C) x))) = x
      rw [G.unitary.apply_symm_apply]
      have h := congrArg (fun T : Sites N d →ₗ[ℂ] Sites N d => T x) ih
      exact h

/-- Combined semantic specification of the canonical inverse circuit. -/
theorem eval_inverse (C : Circuit N d) :
    eval (inverse C) ∘ₗ eval C = LinearMap.id ∧
      eval C ∘ₗ eval (inverse C) = LinearMap.id :=
  ⟨eval_inverse_comp C, eval_comp_inverse C⟩

end Circuit

namespace ReversibleCircuitEvolution

/-- Every finite circuit has a canonical reversible-evolution certificate. -/
def ofCircuit (E : Circuit N d) : ReversibleCircuitEvolution N d where
  forward := E
  backward := Circuit.inverse E
  backward_forward := Circuit.eval_inverse_comp E
  forward_backward := Circuit.eval_comp_inverse E

@[simp] theorem ofCircuit_forward (E : Circuit N d) :
    (ofCircuit E).forward = E := rfl

@[simp] theorem ofCircuit_backward (E : Circuit N d) :
    (ofCircuit E).backward = Circuit.inverse E := rfl

/-- A canonical inverse has equal length, so reversible overhead is twice the
evolution-circuit length. -/
theorem overhead_ofCircuit (E : Circuit N d) :
    (ofCircuit E).overhead = 2 * Circuit.length E := by
  change Circuit.length E + Circuit.length (Circuit.inverse E) =
    2 * Circuit.length E
  rw [Circuit.inverse_length]
  omega

end ReversibleCircuitEvolution

end

end QuantumFoundations.Complexity
