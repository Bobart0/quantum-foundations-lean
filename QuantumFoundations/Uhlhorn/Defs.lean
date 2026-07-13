import QuantumFoundations.Wigner.Main
import Gleason.Main

/-!
# Définitions U0 — Uhlhorn / Corollaire 1.2 de Šemrl

Toutes les définitions réutilisent au maximum ce qui existe déjà : `H n`, `wigner`,
`IsWignerMap` (`QuantumFoundations.Wigner`) ; `Submodule ℂ (H n)`, `projL`,
`bornValue`, `ProjMeasure`, `Gleason.gleason` (`Gleason`, dépendance épinglée).
Aucun wrapper `rankOne`/structure bundlée n'existe côté `gleason` pour « projection
de rang 1 » — les projections y sont représentées par des `Submodule ℂ (H n)`
(cf. `ProjMeasure`/`bornValue`/`projL`), jamais par un type dédié. `Proj1` ci-dessous
suit cette convention plutôt que d'en introduire une nouvelle.

Convention retenue pour « symétrie de Wigner en langage de projections »
(`IsWignerSymmetryProj`, Option 1 validée) : égalité de DROITES
`φ(ℂ∙x) = ℂ∙(Ux)`, PAS l'égalité opératorielle littérale `φ(P) = U P U*`. Les deux
formulations sont mathématiquement équivalentes pour des projections de rang 1
(la droite détermine la projection) ; l'Option 1 évite d'avoir à définir
`LinearMap.adjoint` d'une équivalence semilinéaire (`≃ₛₗᵢ[starRingEnd ℂ]`), un point
d'API jamais rencontré dans ce projet. L'Option 2 (opératorielle) est laissée en
remarque pour une passe ultérieure si le papier final en a besoin explicitement.
-/

namespace QuantumFoundations.Uhlhorn

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ}

private theorem ne_zero_of_norm_eq_one {x : H n} (hx : ‖x‖ = 1) : x ≠ 0 := by
  intro h; rw [h, norm_zero] at hx; exact one_ne_zero hx.symm

/-- Une projection de rang 1, représentée comme sous-espace de dimension 1 — pas de
wrapper `rankOne` dédié, convention identique à `Gleason.ProjMeasure`/`bornValue`. -/
abbrev Proj1 (n : ℕ) := {A : Submodule ℂ (H n) // Module.finrank ℂ A = 1}

/-- La projection de rang 1 portée par un vecteur unitaire `x`. -/
def Proj1.mk_unit (x : H n) (hx : ‖x‖ = 1) : Proj1 n :=
  ⟨ℂ ∙ x, finrank_span_singleton (ne_zero_of_norm_eq_one hx)⟩

/-- Tout `P : Proj1 n` est porté par un vecteur unitaire canonique
(`eq_span_singleton_of_mem_of_finrank_eq_one`, pas de recours à
`stdOrthonormalBasis` — évite toute gymnastique d'index pour ce cas `finrank = 1`).
Public : partagé entre U1 (`WignerProjectionForm.lean`) et U3a
(`GleasonExtend.lean`) — évite la duplication et une dépendance de fichier
gênante de U1 (indépendant du reste) vers U3a. -/
theorem exists_unit_vector_of_proj1 (P : Proj1 n) :
    ∃ x : H n, ‖x‖ = 1 ∧ (P : Submodule ℂ (H n)) = ℂ ∙ x := by
  have hne : (P : Submodule ℂ (H n)) ≠ ⊥ := by
    intro hbot
    have h1 := P.2
    rw [hbot] at h1
    simp at h1
  obtain ⟨w, hwP, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨(‖w‖⁻¹ : ℂ) • w, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg w),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)]
  · rw [Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr
      (by exact_mod_cast norm_ne_zero_iff.mpr hw0 : (‖w‖ : ℂ) ≠ 0)).inv]
    exact eq_span_singleton_of_mem_of_finrank_eq_one P.2 hwP hw0

/-- `tr(PQ)`, exprimé via l'infrastructure Gleason existante (`projL`/`bornValue`) :
`bornValue (projL P) Q = Re tr(projL P ∘ₗ projL Q)`. -/
def TraceProd (P Q : Proj1 n) : ℝ :=
  bornValue (projL (P : Submodule ℂ (H n))) (Q : Submodule ℂ (H n))

/-- `φ` préserve l'orthogonalité DANS UN SEUL SENS : `PQ = 0 ⟹ φ(P)φ(Q) = 0`. Ni
injectivité ni surjectivité supposées sur `φ`. -/
def PreservesOrthogonality (φ : Proj1 n → Proj1 n) : Prop :=
  ∀ P Q : Proj1 n, (P : Submodule ℂ (H n)) ⟂ (Q : Submodule ℂ (H n)) →
    (φ P : Submodule ℂ (H n)) ⟂ (φ Q : Submodule ℂ (H n))

/-- **Symétrie de Wigner, en langage de projections** (Option 1 : égalité de
droites — voir note d'en-tête). -/
def IsWignerSymmetryProj (φ : Proj1 n → Proj1 n) : Prop :=
  (∃ U : H n ≃ₗᵢ[ℂ] H n, ∀ x : H n, ∀ hx : ‖x‖ = 1,
      (φ (Proj1.mk_unit x hx) : Submodule ℂ (H n)) = ℂ ∙ (U x))
∨ (∃ U : H n ≃ₛₗᵢ[starRingEnd ℂ] H n, ∀ x : H n, ∀ hx : ‖x‖ = 1,
      (φ (Proj1.mk_unit x hx) : Submodule ℂ (H n)) = ℂ ∙ (U x))

/-- Une fonction-cadre sur les droites : positive, et sommant à `1` sur TOUTE base
orthonormée de l'espace ambiant (analogue de `IsCFrameFunction`/`ProjMeasure`, mais
définie seulement sur `Proj1 n`, pas sur tous les sous-espaces — cf. U3a). -/
def IsFrameFunctionOnLines (g : Proj1 n → ℝ) : Prop :=
  (∀ P, 0 ≤ g P) ∧
  (∀ b : OrthonormalBasis (Fin n) ℂ (H n),
    ∑ i, g (Proj1.mk_unit (b i) (b.norm_eq_one i)) = 1)

/-- `φ` envoie tout système orthonormé complet (COSP — en dimension finie, toute
base orthonormée) sur un COSP. -/
def SendsONBToONB (φ : Proj1 n → Proj1 n) : Prop :=
  ∀ b : OrthonormalBasis (Fin n) ℂ (H n),
    ∃ b' : OrthonormalBasis (Fin n) ℂ (H n),
      ∀ i, (φ (Proj1.mk_unit (b i) (b.norm_eq_one i)) : Submodule ℂ (H n)) = ℂ ∙ (b' i)

end
end QuantumFoundations.Uhlhorn
