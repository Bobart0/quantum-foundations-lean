import QuantumFoundations.Complexity.Defs

/-!
# C1 — Circuit locality

The operator-theoretic closure step is kept separate from record semantics:
a product of gates commutes with every operator localized in a region
disjoint from the circuit's union support.
-/

namespace QuantumFoundations.Complexity

open QuantumFoundations.Branches

noncomputable section

namespace Circuit

/--
A circuit commutes with an operator localized away from every site touched
by the circuit.  The proof applies `Branches.commute_of_disjoint` gate by
gate and closes commutation under composition explicitly.
-/
theorem circuit_commute_of_disjoint (C : Circuit N d) (F : Finset (Fin N))
    (A : Sites N d →ₗ[ℂ] Sites N d) (hA : IsLocalTo A F)
    (hdisj : Disjoint (support C) F) : Commute (eval C) A := by
  induction C with
  | nil =>
      show LinearMap.id ∘ₗ A = A ∘ₗ LinearMap.id
      ext x
      rfl
  | cons G C ih =>
      have hparts : Disjoint G.support F ∧ Disjoint (support C) F := by
        simpa [support] using hdisj
      have hG : Commute G.unitary.toLinearIsometry.toLinearMap A :=
        commute_of_disjoint hparts.1 G.locality hA
      have hC : Commute (eval C) A := ih hparts.2
      exact hC.mul_left hG

end Circuit

end


end QuantumFoundations.Complexity
