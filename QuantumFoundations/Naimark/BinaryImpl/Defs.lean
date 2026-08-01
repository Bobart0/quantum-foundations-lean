import QuantumFoundations.Naimark.Unitary

/-!
**FR.** # Module C (Porte Ω) — implémentations binaires d'un effet

`BinaryImpl n E ι` formalise une "implémentation" concrète d'un effet fixé
`E : H n →ₗ[ℂ] H n` : un encodage isométrique de `H n` dans un espace
ambiant `EuclideanSpace ℂ ι`, muni d'une cellule de mesure (projection
symétrique) dont le tiré-en-arrière par l'encodage redonne exactement `E`
(`realizes`). C'est le cadre dans lequel `naimark` (`Naimark/Main.lean`)
fournit une implémentation CANONIQUE ; ce module classe TOUTES les
implémentations possibles, sans jamais reprouver `naimark`.

`StrictIso I J` est l'isomorphisme strict entre deux implémentations : une
isométrie de l'espace ambiant qui transporte l'encodage et entrelace les
cellules. C'est délibérément plus fort que la seule égalité des effets
induits ⟨I⟩=⟨J⟩=E (qui est automatique, par `realizes`) : `StrictIso`
exige de plus que l'encodage ET la cellule se correspondent exactement
sous l'isométrie.

**EN.** # Module C (Omega Gate) — binary implementations of an effect

`BinaryImpl n E ι` formalizes a concrete "implementation" of a fixed
effect `E : H n →ₗ[ℂ] H n`: an isometric encoding of `H n` into an ambient
space `EuclideanSpace ℂ ι`, equipped with a measurement cell (symmetric
projection) whose pullback along the encoding is exactly `E` (`realizes`).
This is the framework in which `naimark` (`Naimark/Main.lean`) supplies a
CANONICAL implementation; this module classifies ALL possible
implementations, never re-proving `naimark`.

`StrictIso I J` is the strict isomorphism between two implementations: an
isometry of the ambient space that transports the encoding and
intertwines the cells. This is deliberately stronger than mere equality
of the induced effects (which is automatic, by `realizes`): `StrictIso`
additionally requires the encoding AND the cell to match exactly under
the isometry.
-/

namespace QuantumFoundations.Naimark.BinaryImpl

open QuantumFoundations Gleason
open scoped InnerProductSpace

noncomputable section

variable {n : ℕ} {E : H n →ₗ[ℂ] H n} {ι : Type} [Fintype ι] [DecidableEq ι]

/--
**FR.** Une implémentation binaire de l'effet `E` sur `H n` : un encodage
isométrique dans `EuclideanSpace ℂ ι`, et une cellule (projection
symétrique de cet espace) dont le tiré-en-arrière est `E`.

**EN.** A binary implementation of the effect `E` on `H n`: an isometric
encoding into `EuclideanSpace ℂ ι`, and a cell (symmetric projection of
that space) whose pullback is `E`.
-/
structure BinaryImpl (n : ℕ) (E : H n →ₗ[ℂ] H n) (ι : Type) [Fintype ι] [DecidableEq ι] where
  /-- The isometric encoding of the physical system into the ambient space. -/
  encoding : H n →ₗ[ℂ] EuclideanSpace ℂ ι
  /-- The measurement cell: a symmetric projection of the ambient space. -/
  cell : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι
  encoding_isometry : LinearMap.adjoint encoding ∘ₗ encoding = LinearMap.id
  cell_isProjection : cell.IsSymmetricProjection
  /-- The pullback of `cell` along `encoding` realizes exactly `E`. -/
  realizes : LinearMap.adjoint encoding ∘ₗ cell ∘ₗ encoding = E

namespace BinaryImpl

/-- The dimension of the ambient space `EuclideanSpace ℂ ι`. -/
def ambientDim (_I : BinaryImpl n E ι) : ℕ := Fintype.card ι

/-- The event cell, i.e. `I.cell` itself, under an explicit name mirroring
`complementCell`. -/
def eventCell (I : BinaryImpl n E ι) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι := I.cell

/-- The complementary cell `1 - I.cell` (the "did not happen" outcome). -/
def complementCell (I : BinaryImpl n E ι) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι :=
  1 - I.cell

theorem cell_idempotent (I : BinaryImpl n E ι) : I.cell ∘ₗ I.cell = I.cell :=
  I.cell_isProjection.isIdempotentElem

theorem cell_symmetric (I : BinaryImpl n E ι) : LinearMap.IsSymmetric I.cell :=
  I.cell_isProjection.isSymmetric

theorem complementCell_isProjection (I : BinaryImpl n E ι) :
    I.complementCell.IsSymmetricProjection :=
  ⟨I.cell_isProjection.isIdempotentElem.one_sub,
    LinearMap.IsSymmetric.sub (fun _ => congrFun rfl) I.cell_symmetric⟩

theorem cell_comp_complement_eq_zero (I : BinaryImpl n E ι) :
    I.cell ∘ₗ I.complementCell = 0 := by
  show I.cell ∘ₗ (1 - I.cell) = 0
  rw [LinearMap.comp_sub]
  rw [show I.cell ∘ₗ (1 : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) = I.cell from mul_one I.cell]
  rw [I.cell_idempotent, sub_self]

theorem complement_comp_cell_eq_zero (I : BinaryImpl n E ι) :
    I.complementCell ∘ₗ I.cell = 0 := by
  show (1 - I.cell) ∘ₗ I.cell = 0
  rw [LinearMap.sub_comp]
  rw [show (1 : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) ∘ₗ I.cell = I.cell from one_mul I.cell]
  rw [I.cell_idempotent, sub_self]

theorem cell_add_complement_eq_one (I : BinaryImpl n E ι) :
    I.cell + I.complementCell = 1 := by
  show I.cell + (1 - I.cell) = 1
  abel

/--
**FR.** Isomorphisme strict entre deux implémentations d'un MÊME effet `E` :
une isométrie de l'espace ambiant qui transporte l'encodage et entrelace
les cellules. Volontairement PLUS FORT que la seule égalité des effets
induits.

**EN.** Strict isomorphism between two implementations of the SAME effect
`E`: an isometry of the ambient space that transports the encoding and
intertwines the cells. Deliberately STRONGER than mere equality of the
induced effects.
-/
def StrictIso {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (I : BinaryImpl n E ι) (J : BinaryImpl n E κ) : Prop :=
  ∃ U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ,
    U.toLinearMap ∘ₗ I.encoding = J.encoding ∧
    U.toLinearMap ∘ₗ I.cell = J.cell ∘ₗ U.toLinearMap

/-- Pointwise unfolding of the encoding-intertwining equation carried by a
`StrictIso` witness. -/
private theorem strictIso_encoding_apply {κ : Type} [Fintype κ] [DecidableEq κ]
    {I : BinaryImpl n E ι} {J : BinaryImpl n E κ}
    (U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (hU1 : U.toLinearMap ∘ₗ I.encoding = J.encoding) (x : H n) :
    U (I.encoding x) = J.encoding x := by
  have h := LinearMap.congr_fun hU1 x
  simpa using h

/-- Pointwise unfolding of the cell-intertwining equation carried by a
`StrictIso` witness. -/
private theorem strictIso_cell_apply {κ : Type} [Fintype κ] [DecidableEq κ]
    {I : BinaryImpl n E ι} {J : BinaryImpl n E κ}
    (U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (hU2 : U.toLinearMap ∘ₗ I.cell = J.cell ∘ₗ U.toLinearMap) (x : EuclideanSpace ℂ ι) :
    U (I.cell x) = J.cell (U x) := by
  have h := LinearMap.congr_fun hU2 x
  simpa using h

theorem StrictIso.refl (I : BinaryImpl n E ι) : StrictIso I I := by
  refine ⟨LinearIsometryEquiv.refl ℂ (EuclideanSpace ℂ ι), ?_, ?_⟩
  · apply LinearMap.ext; intro x; rfl
  · apply LinearMap.ext; intro x; rfl

theorem StrictIso.symm {κ : Type} [Fintype κ] [DecidableEq κ]
    {I : BinaryImpl n E ι} {J : BinaryImpl n E κ} (h : StrictIso I J) :
    StrictIso J I := by
  obtain ⟨U, hU1, hU2⟩ := h
  refine ⟨U.symm, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    show U.symm (J.encoding x) = I.encoding x
    rw [← strictIso_encoding_apply U hU1 x, U.symm_apply_apply]
  · apply LinearMap.ext
    intro x
    show U.symm (J.cell x) = I.cell (U.symm x)
    have hx : J.cell x = J.cell (U (U.symm x)) := by rw [U.apply_symm_apply]
    rw [hx, ← strictIso_cell_apply U hU2 (U.symm x), U.symm_apply_apply]

theorem StrictIso.trans {κ μ : Type} [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]
    {I : BinaryImpl n E ι} {J : BinaryImpl n E κ} {K : BinaryImpl n E μ}
    (h1 : StrictIso I J) (h2 : StrictIso J K) : StrictIso I K := by
  obtain ⟨U, hU1, hU2⟩ := h1
  obtain ⟨V, hV1, hV2⟩ := h2
  refine ⟨U.trans V, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    show V (U (I.encoding x)) = K.encoding x
    rw [strictIso_encoding_apply U hU1 x, strictIso_encoding_apply V hV1 x]
  · apply LinearMap.ext
    intro x
    show V (U (I.cell x)) = K.cell (V (U x))
    rw [strictIso_cell_apply U hU2 x, strictIso_cell_apply V hV2 (U x)]

theorem StrictIso.ambientDim_eq {κ : Type} [Fintype κ] [DecidableEq κ]
    {I : BinaryImpl n E ι} {J : BinaryImpl n E κ} (h : StrictIso I J) :
    I.ambientDim = J.ambientDim := by
  obtain ⟨U, -, -⟩ := h
  show Fintype.card ι = Fintype.card κ
  have h1 : Module.finrank ℂ (EuclideanSpace ℂ ι) = Fintype.card ι := finrank_euclideanSpace
  have h2 : Module.finrank ℂ (EuclideanSpace ℂ κ) = Fintype.card κ := finrank_euclideanSpace
  rw [← h1, ← h2]
  exact U.toLinearEquiv.finrank_eq

/-- Injective linear maps preserve the finrank of a submodule under
`Submodule.map`. A small reusable helper, used pervasively throughout
Module C whenever a strict isometry transports a submodule. -/
private theorem finrank_map_of_injective {V W : Type} [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ V] [InnerProductSpace ℂ W] [FiniteDimensional ℂ V]
    (f : V →ₗ[ℂ] W) (hf : Function.Injective f) (p : Submodule ℂ V) :
    Module.finrank ℂ (p.map f) = Module.finrank ℂ p :=
  (Submodule.equivMapOfInjective f hf p).finrank_eq.symm

theorem StrictIso.projectorRange_finrank_eq {κ : Type} [Fintype κ] [DecidableEq κ]
    {I : BinaryImpl n E ι} {J : BinaryImpl n E κ} (h : StrictIso I J) :
    Module.finrank ℂ (LinearMap.range I.cell) = Module.finrank ℂ (LinearMap.range J.cell) := by
  obtain ⟨U, -, hU2⟩ := h
  have hmap : (LinearMap.range I.cell).map U.toLinearMap = LinearMap.range J.cell := by
    rw [← LinearMap.range_comp, hU2, LinearMap.range_comp, LinearMap.range_eq_top.mpr U.surjective,
      Submodule.map_top]
  rw [← hmap]
  exact (finrank_map_of_injective U.toLinearMap U.injective (LinearMap.range I.cell)).symm

theorem StrictIso.projectorKernel_finrank_eq {κ : Type} [Fintype κ] [DecidableEq κ]
    {I : BinaryImpl n E ι} {J : BinaryImpl n E κ} (h : StrictIso I J) :
    Module.finrank ℂ (LinearMap.ker I.cell) = Module.finrank ℂ (LinearMap.ker J.cell) := by
  obtain ⟨U, -, hU2⟩ := h
  have hmap : (LinearMap.ker I.cell).map U.toLinearMap = LinearMap.ker J.cell := by
    apply Submodule.ext
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show J.cell (U x) = 0
      rw [← strictIso_cell_apply U hU2 x]
      show U (I.cell x) = 0
      rw [(LinearMap.mem_ker).mp hx, map_zero]
    · intro hy
      refine ⟨U.symm y, ?_, U.apply_symm_apply y⟩
      show I.cell (U.symm y) = 0
      apply U.injective
      rw [strictIso_cell_apply U hU2 (U.symm y), U.apply_symm_apply, map_zero]
      exact (LinearMap.mem_ker).mp hy
  rw [← hmap]
  exact (finrank_map_of_injective U.toLinearMap U.injective (LinearMap.ker I.cell)).symm

/-- The rank of the measurement cell: the dimension of the "event" side of
the ambient space. -/
def projectorRank (I : BinaryImpl n E ι) : ℕ :=
  Module.finrank ℂ (LinearMap.range I.cell)

/-- The nullity of the measurement cell: the dimension of the
"complement" side of the ambient space. -/
def projectorNullity (I : BinaryImpl n E ι) : ℕ :=
  Module.finrank ℂ (LinearMap.ker I.cell)

theorem projectorRank_add_nullity (I : BinaryImpl n E ι) :
    I.projectorRank + I.projectorNullity = I.ambientDim := by
  show Module.finrank ℂ (LinearMap.range I.cell) + Module.finrank ℂ (LinearMap.ker I.cell)
    = Fintype.card ι
  rw [LinearMap.finrank_range_add_finrank_ker]
  exact finrank_euclideanSpace

end BinaryImpl

end
end QuantumFoundations.Naimark.BinaryImpl
