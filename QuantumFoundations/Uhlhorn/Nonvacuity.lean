import QuantumFoundations.Uhlhorn.Defs

/-!
# Nonvacuity — `Proj1`, `PreservesOrthogonality`, `IsWignerSymmetryProj` sont habités

Témoin : `φ := id` satisfait trivialement `PreservesOrthogonality` et habite la
branche unitaire de `IsWignerSymmetryProj` (`U := refl`). Témoin antiunitaire
(`conjCoords`, W0) NON immédiat : il faudrait transporter `Proj1 n` par
`conjCoordsEquiv n : H n ≃ₛₗᵢ[starRingEnd ℂ] H n` via `Submodule.map`, un point
d'API semilinéaire jamais exercé dans ce projet — écarté ici conformément à la
consigne (un seul témoin suffit, ne pas forcer un second témoin coûteux).
-/

namespace QuantumFoundations.Uhlhorn

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ}

theorem preservesOrthogonality_id : PreservesOrthogonality (id : Proj1 n → Proj1 n) :=
  fun _ _ h => h

theorem isWignerSymmetryProj_id : IsWignerSymmetryProj (id : Proj1 n → Proj1 n) :=
  Or.inl ⟨LinearIsometryEquiv.refl ℂ (H n), fun _ _ => rfl⟩

example : ∃ φ : Proj1 n → Proj1 n, PreservesOrthogonality φ ∧ IsWignerSymmetryProj φ :=
  ⟨id, preservesOrthogonality_id, isWignerSymmetryProj_id⟩

/-- `Proj1 3` (le seuil de dimension visé par le théorème final) n'est pas vide. -/
example : Nonempty (Proj1 3) :=
  ⟨Proj1.mk_unit (EuclideanSpace.single (0 : Fin 3) 1) (by simp)⟩

end
end QuantumFoundations.Uhlhorn
