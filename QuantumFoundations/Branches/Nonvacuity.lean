import QuantumFoundations.Branches.Defs

/-!
# R0 — Nonvacuity : témoin GHZ₃ (une observable, trois records redondants)

Habitant concret de `IsRecordedOn`/`LabeledResolution` (règle absolue 3 du
projet, dans le même commit que `Defs.lean`).

## Ambiante : `H 8`, PAS `Sites 3 2` (décision arbitrée en reconnaissance)

`LabeledResolution n K` est structurellement lié à `Gleason.H n` (il réutilise
`Gleason.projL`, lui-même typé sur `H n`). `Sites 3 2 := EuclideanSpace ℂ
((Fin 3) → Fin 2)` n'est PAS défeq à `H 8`, même si les deux ont la même
dimension complexe (8). Ce témoin n'ayant qu'UNE SEULE observable
(`CommuteWitness` y est vacuement vrai — aucune paire `a ≠ b` à vérifier), il
n'a structurellement besoin d'aucune machinerie de `Local.lean` : on construit
donc directement sur `H 8`, avec trois « sites virtuels » extraits par digit
binaire sur `Fin 8` (`digit s g := (g.val / 2 ^ s.val) % 2`), plutôt que
d'importer `Sites`. C'est une bijection d'indices pure (`Fin 8 ↔ Fin 3 → Fin 2`
par écriture binaire), zéro `LinearIsometryEquiv` de Hilbert.

**Ce témoin ne valide RIEN du pont général `Sites N d ↔ H n`** — c'est un
raccourci délibéré pour ce cas isolé à une seule observable (`CommuteWitness`
vacuité oblige), PAS un modèle réduit du travail que `Local.riedel_local`
devra faire en général. Ne pas réutiliser cette construction comme base pour
le pont général.

## Discipline du témoin (comme `Histories.Witness`, amplitudes d'abord)

`ψ₀ := e 0 + e 7` (les deux configurations « tous les sites égaux », NON
normalisé) — `0 = 000₂`, `7 = 111₂`. Ordre de dérivation : générateurs et
leurs produits scalaires (singles distincts → 0) ; `projL (cell s b) ψ₀`
[`projL` fixe le membre, tue l'orthogonal] ; `IsRecordedOn` immédiat (`digit s
0 = 0` et `digit s 7 = 1` pour LES TROIS sites `s`, donc les trois records
s'accordent toujours) ; orthogonalité par `Submodule.isOrtho_span` ; `covers`
via la base standard de `H 8` (`EuclideanSpace.basisFun`), scindée par
`digit s`.
-/

namespace QuantumFoundations.Branches

open scoped InnerProductSpace
open Gleason

noncomputable section

/-- Base canonique de `H 8`. -/
def e (g : Fin 8) : H 8 := EuclideanSpace.single g (1 : ℂ)

/-- Digit binaire `s` (site virtuel `s ∈ Fin 3`) de `g ∈ Fin 8`, vu comme
entier `0 ≤ g < 8` écrit en base 2 sur 3 bits. -/
def digit (s : Fin 3) (g : Fin 8) : Fin 2 := ⟨(g.val / 2 ^ s.val) % 2, by omega⟩

private theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

theorem digit_zero (s : Fin 3) : digit s 0 = 0 := by fin_cases s <;> decide

theorem digit_seven (s : Fin 3) : digit s 7 = 1 := by fin_cases s <;> decide

/-- Cellule du site `s`, valeur `b` : span des vecteurs de base dont le
digit `s` vaut `b`. -/
def cell (s : Fin 3) (b : Fin 2) : Submodule ℂ (H 8) :=
  Submodule.span ℂ (e '' {g | digit s g = b})

theorem cell_ortho (s : Fin 3) {b b' : Fin 2} (hbb : b ≠ b') : cell s b ⟂ cell s b' := by
  unfold cell
  rw [Submodule.isOrtho_span]
  rintro u ⟨g, hg, rfl⟩ v ⟨k, hk, rfl⟩
  have hgk : g ≠ k := fun h => hbb (by rw [← hg, h, hk])
  unfold e
  rw [EuclideanSpace.inner_single_left]
  simp [hgk.symm]

theorem cell_covers (s : Fin 3) : cell s 0 ⊔ cell s 1 = ⊤ := by
  unfold cell
  rw [← Submodule.span_union]
  have hunion : (e '' {g | digit s g = 0}) ∪ (e '' {g | digit s g = 1}) = Set.range e := by
    ext x
    simp only [Set.mem_union, Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro (⟨g, _, rfl⟩ | ⟨g, _, rfl⟩) <;> exact ⟨_, rfl⟩
    · rintro ⟨g, rfl⟩
      rcases fin2_cases (digit s g) with h | h
      · exact Or.inl ⟨g, h, rfl⟩
      · exact Or.inr ⟨g, h, rfl⟩
  rw [hunion]
  have heq : (fun g : Fin 8 => (EuclideanSpace.single g (1 : ℂ) : H 8))
      = ⇑(EuclideanSpace.basisFun (Fin 8) ℂ).toBasis := by
    funext g
    rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  show Submodule.span ℂ (Set.range e) = ⊤
  show Submodule.span ℂ (Set.range (fun g => (EuclideanSpace.single g (1 : ℂ) : H 8))) = ⊤
  rw [heq]
  exact (EuclideanSpace.basisFun (Fin 8) ℂ).toBasis.span_eq

/-- Le record du site `s` : cellules `cell s`, orthogonales et complètes. -/
def siteRec (s : Fin 3) : LabeledResolution 8 2 where
  cells := cell s
  ortho := fun i j hij => Submodule.isOrtho_iff_le.mp (cell_ortho s hij)
  covers := by
    have hsup : (⨆ i, cell s i) = cell s 0 ⊔ cell s 1 := by
      rw [← Finset.sup_univ_eq_iSup]
      show ({0, 1} : Finset (Fin 2)).sup (cell s) = cell s 0 ⊔ cell s 1
      rw [Finset.sup_insert, Finset.sup_singleton]
    rw [hsup]
    exact cell_covers s

/-- État GHZ₃ (non normalisé) : superposition des deux configurations
« tous les sites égaux ». -/
def ψ₀ : H 8 := e 0 + e 7

theorem e0_mem_cell (s : Fin 3) : e 0 ∈ cell s 0 :=
  Submodule.subset_span ⟨0, digit_zero s, rfl⟩

theorem e7_mem_cell (s : Fin 3) : e 7 ∈ cell s 1 :=
  Submodule.subset_span ⟨7, digit_seven s, rfl⟩

theorem proj_cell0_psi0 (s : Fin 3) : projL (cell s 0) ψ₀ = e 0 := by
  show (cell s 0).starProjection (e 0 + e 7) = e 0
  rw [map_add]
  have h1 : (cell s 0).starProjection (e 0) = e 0 :=
    Submodule.starProjection_eq_self_iff.mpr (e0_mem_cell s)
  have h2 : (cell s 0).starProjection (e 7) = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact (cell_ortho s (by decide : (0:Fin 2) ≠ 1)).symm (e7_mem_cell s)
  rw [h1, h2, add_zero]

theorem proj_cell1_psi0 (s : Fin 3) : projL (cell s 1) ψ₀ = e 7 := by
  show (cell s 1).starProjection (e 0 + e 7) = e 7
  rw [map_add]
  have h1 : (cell s 1).starProjection (e 7) = e 7 :=
    Submodule.starProjection_eq_self_iff.mpr (e7_mem_cell s)
  have h2 : (cell s 1).starProjection (e 0) = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact (cell_ortho s (by decide : (0:Fin 2) ≠ 1)) (e0_mem_cell s)
  rw [h1, h2, zero_add]

/-- **Témoin de Nonvacuity R0** : les trois records (un par site virtuel)
enregistrent tous la même branche de `ψ₀` — GHZ₃, redondance maximale. -/
theorem isRecordedOn_ψ₀ : IsRecordedOn ψ₀ siteRec := by
  intro r r' i
  show projL (cell r i) ψ₀ = projL (cell r' i) ψ₀
  rcases fin2_cases i with rfl | rfl
  · rw [proj_cell0_psi0, proj_cell0_psi0]
  · rw [proj_cell1_psi0, proj_cell1_psi0]

end
end QuantumFoundations.Branches
