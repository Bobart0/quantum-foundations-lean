import QuantumFoundations.Uhlhorn.Defs

/-!
**FR.** # Nonvacuity — `Proj1`, `PreservesOrthogonality`, `IsWignerSymmetryProj` sont habités

Témoin : `φ := id` satisfait trivialement `PreservesOrthogonality` et habite la
branche unitaire de `IsWignerSymmetryProj` (`U := refl`). Témoin antiunitaire
(`conjCoords`, W0) NON immédiat : il faudrait transporter `Proj1 n` par
`conjCoordsEquiv n : H n ≃ₛₗᵢ[starRingEnd ℂ] H n` via `Submodule.map`, un point
d'API semilinéaire jamais exercé dans ce projet — écarté ici conformément à la
consigne (un seul témoin suffit, ne pas forcer un second témoin coûteux).

**EN.** # Nonvacuity — Proj1, PreservesOrthogonality, and
IsWignerSymmetryProj are inhabited

Witness: φ := id trivially satisfies PreservesOrthogonality and inhabits
the unitary branch of IsWignerSymmetryProj (U := refl). An antiunitary
witness (conjCoords, W0) is NOT immediate: it would require transporting
Proj1 n through
conjCoordsEquiv n : H n ≃ₛₗᵢ[starRingEnd ℂ] H n using Submodule.map, a
semilinear API point never exercised in this project. It is omitted here in
accordance with the instruction that a single witness suffices and that an
expensive second witness should not be forced.
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

/--
**FR.** `Proj1 3` (le seuil de dimension visé par le théorème final) n'est pas vide.

**EN.** Proj1 3, the dimension threshold targeted by the final theorem, is nonempty.
-/
example : Nonempty (Proj1 3) :=
  ⟨Proj1.mk_unit (EuclideanSpace.single (0 : Fin 3) 1) (by simp)⟩

end
end QuantumFoundations.Uhlhorn
