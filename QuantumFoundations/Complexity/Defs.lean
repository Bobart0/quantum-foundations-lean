import QuantumFoundations.BranchesRiedel.Local

/-!
# C0 — Finite 2-local circuits

This file defines exact finite circuits on `BranchesRiedel.Sites N d`.  Each gate
is a linear isometric equivalence supported on at most two sites in the
existing `BranchesRiedel.IsLocalTo` sense.

The evaluation convention is chronological from the head of the list: for
`C = [G₁, G₂, G₃]`, `C.eval x = G₃ (G₂ (G₁ x))`.
-/

namespace QuantumFoundations.Complexity

open QuantumFoundations.BranchesRiedel

noncomputable section

/-- An exact gate whose spatial support contains at most two sites. -/
structure TwoLocalGate (N d : ℕ) where
  unitary : Sites N d ≃ₗᵢ[ℂ] Sites N d
  support : Finset (Fin N)
  locality : IsLocalTo unitary.toLinearIsometry.toLinearMap support
  support_card_le_two : support.card ≤ 2

/-- A finite 2-local circuit, in chronological list order. -/
abbrev Circuit (N d : ℕ) := List (TwoLocalGate N d)

namespace Circuit

/-- The number of gates in a circuit. -/
def length (C : Circuit N d) : ℕ := List.length C

/--
The ordered product of the gates.  The head gate acts first, so
`[G₁, G₂, G₃].eval x = G₃ (G₂ (G₁ x))`.
-/
def eval : Circuit N d → Sites N d →ₗ[ℂ] Sites N d
  | [] => LinearMap.id
  | G :: C => eval C ∘ₗ G.unitary.toLinearIsometry.toLinearMap

/-- The union of the declared supports of all gates. -/
def support : Circuit N d → Finset (Fin N)
  | [] => ∅
  | G :: C => G.support ∪ support C

@[simp] theorem length_eq (C : Circuit N d) : C.length = List.length C := rfl

@[simp] theorem eval_nil : eval ([] : Circuit N d) = LinearMap.id := rfl

@[simp] theorem eval_cons (G : TwoLocalGate N d) (C : Circuit N d) :
    eval (G :: C) = eval C ∘ₗ G.unitary.toLinearIsometry.toLinearMap := rfl

@[simp] theorem eval_singleton (G : TwoLocalGate N d) :
    eval [G] = G.unitary.toLinearIsometry.toLinearMap := by
  ext x
  rfl

theorem eval_append (C D : Circuit N d) :
    eval (C ++ D) = eval D ∘ₗ eval C := by
  induction C with
  | nil =>
      ext x
      rfl
  | cons G C ih =>
      rw [List.cons_append, eval_cons, eval_cons, ih]
      ext x
      rfl

@[simp] theorem support_nil : support ([] : Circuit N d) = ∅ := rfl

@[simp] theorem support_cons (G : TwoLocalGate N d) (C : Circuit N d) :
    support (G :: C) = G.support ∪ support C := rfl

private theorem gate_support_subset_of_mem {G : TwoLocalGate N d} {C : Circuit N d}
    (hG : G ∈ C) : G.support ⊆ support C := by
  induction C with
  | nil => simp at hG
  | cons G' C ih =>
      simp only [List.mem_cons] at hG
      rw [support_cons]
      rcases hG with rfl | hG
      · exact Finset.subset_union_left
      · exact fun x hx => Finset.mem_union_right _ (ih hG hx)

/-- Every gate support is contained in the union support of its circuit. -/
theorem gate_support_subset_circuit_support (C : Circuit N d) (k : Fin C.length) :
    (C.get k).support ⊆ support C :=
  gate_support_subset_of_mem (List.get_mem C k)

/-- The union support of a 2-local circuit has at most twice as many sites as gates. -/
theorem circuit_support_card_le (C : Circuit N d) :
    (support C).card ≤ 2 * C.length := by
  induction C with
  | nil => simp
  | cons G C ih =>
      rw [support_cons, length_eq, List.length_cons]
      calc
        (G.support ∪ support C).card ≤ G.support.card + (support C).card :=
          Finset.card_union_le _ _
        _ ≤ 2 + 2 * C.length := Nat.add_le_add G.support_card_le_two ih
        _ = 2 * (C.length + 1) := by omega

/-- The identity operator is local to the empty region. -/
theorem isLocalTo_id_empty :
    IsLocalTo (LinearMap.id : Sites N d →ₗ[ℂ] Sites N d) ∅ := by
  classical
  refine ⟨fun _ _ => 1, ?_⟩
  intro g k
  by_cases h : g = k
  · subst k
    simp [AgreesOff]
  · have hpoint : ¬ ∀ s, g s = k s := fun hgk => h (funext hgk)
    rw [if_neg]
    · simp only [LinearMap.id_apply, PiLp.inner_apply, RCLike.inner_apply]
      apply Finset.sum_eq_zero
      intro x _
      by_cases hxg : x = g
      · subst x
        simp [h]
      · simp [hxg]
    · simpa [AgreesOff] using hpoint

end Circuit

end

end QuantumFoundations.Complexity
