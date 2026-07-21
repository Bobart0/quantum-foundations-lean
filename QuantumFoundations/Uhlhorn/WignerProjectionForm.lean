import QuantumFoundations.Uhlhorn.Defs

/-!
**FR.** # U1 — Corollaire (B) de Wigner en langage de projections

Jamais construit jusqu'ici (mis de côté au tout début du projet Wigner, W0). Se
déduit de `QuantumFoundations.Wigner.wigner` en choisissant un représentant
unitaire par projection (`T`, Étape 2), après avoir établi que `T` satisfait
`IsWignerMap` (Étape 3, à partir de l'hypothèse de préservation de `TraceProd`).
Indépendant de U2/U3a/U3b — `exists_unit_vector_of_proj1` (utilisé ici) vit dans
`Defs.lean`, pas dans `GleasonExtend.lean` (U3a), précisément pour éviter cette
dépendance de fichier.

**EN.** # U1 — Wigner's Corollary (B) in projection language

This form had never previously been constructed, having been set aside at
the beginning of the Wigner project (W0). It follows from
QuantumFoundations.Wigner.wigner by choosing a unit representative for
each projection (T, Step 2), after establishing that T satisfies
IsWignerMap (Step 3, from the hypothesis that TraceProd is preserved).
It is independent of U2/U3a/U3b:
exists_unit_vector_of_proj1, used here, resides in Defs.lean rather than
in GleasonExtend.lean (U3a), precisely to avoid such a file dependency.
-/

namespace QuantumFoundations.Uhlhorn

open scoped InnerProductSpace
open Gleason
open QuantumFoundations.Wigner

noncomputable section

variable {n : ℕ}

/--
**FR.** **Étape 1** : `TraceProd` sur deux droites est le module au carré du produit
scalaire des représentants unitaires.

**EN.** Step 1: TraceProd for two lines is the squared modulus of the inner
product of their unit representatives.
-/
theorem traceProd_mk_unit_eq (x y : H n) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    TraceProd (Proj1.mk_unit x hx) (Proj1.mk_unit y hy) = ‖⟪x, y⟫_ℂ‖ ^ 2 := by
  show bornValue (projL (ℂ ∙ x)) (ℂ ∙ y) = ‖⟪x, y⟫_ℂ‖ ^ 2
  rw [bornValue_span_singleton (projL (ℂ ∙ x)) y hy, projL_singleton_unit x y hx,
    inner_smul_left, mul_comm, Complex.mul_conj]
  norm_cast
  rw [← Complex.sq_norm]

/--
**FR.** **Étape 2** : construction de `T` par choix d'un représentant unitaire de
`φ (mk_unit x hx)`, junk `0` hors de la sphère unité.

**EN.** Step 2: construction of T by choosing a unit representative of
φ (mk_unit x hx), with junk value 0 outside the unit sphere.
-/
private noncomputable def T (φ : Proj1 n → Proj1 n) (x : H n) : H n :=
  if hx : ‖x‖ = 1 then Classical.choose (exists_unit_vector_of_proj1 (φ (Proj1.mk_unit x hx)))
  else 0

private theorem T_unit (φ : Proj1 n → Proj1 n) {x : H n} (hx : ‖x‖ = 1) : ‖T φ x‖ = 1 := by
  unfold T
  rw [dif_pos hx]
  exact (Classical.choose_spec (exists_unit_vector_of_proj1 (φ (Proj1.mk_unit x hx)))).1

private theorem T_repr (φ : Proj1 n → Proj1 n) {x : H n} (hx : ‖x‖ = 1) :
    (φ (Proj1.mk_unit x hx) : Submodule ℂ (H n)) = ℂ ∙ (T φ x) := by
  unfold T
  rw [dif_pos hx]
  exact (Classical.choose_spec (exists_unit_vector_of_proj1 (φ (Proj1.mk_unit x hx)))).2

/--
**FR.** **Étape 3** : `T` satisfait `IsWignerMap`, à partir de l'hypothèse de
préservation de `TraceProd`.

**EN.** Step 3: T satisfies IsWignerMap, from the hypothesis that
TraceProd is preserved.
-/
private theorem isWignerMap_T {φ : Proj1 n → Proj1 n}
    (hφ : ∀ P Q : Proj1 n, TraceProd (φ P) (φ Q) = TraceProd P Q) :
    IsWignerMap (T φ) := by
  intro x y hx hy
  have h2 : Proj1.mk_unit (T φ x) (T_unit φ hx) = φ (Proj1.mk_unit x hx) :=
    Subtype.ext (T_repr φ hx).symm
  have h3 : Proj1.mk_unit (T φ y) (T_unit φ hy) = φ (Proj1.mk_unit y hy) :=
    Subtype.ext (T_repr φ hy).symm
  have h1 : ‖⟪T φ x, T φ y⟫_ℂ‖ ^ 2 = ‖⟪x, y⟫_ℂ‖ ^ 2 := by
    rw [← traceProd_mk_unit_eq (T φ x) (T φ y) (T_unit φ hx) (T_unit φ hy), h2, h3, hφ,
      traceProd_mk_unit_eq]
  nlinarith [sq_nonneg (‖⟪T φ x, T φ y⟫_ℂ‖ - ‖⟪x, y⟫_ℂ‖),
    sq_nonneg (‖⟪T φ x, T φ y⟫_ℂ‖ + ‖⟪x, y⟫_ℂ‖), h1,
    norm_nonneg (⟪T φ x, T φ y⟫_ℂ), norm_nonneg (⟪x, y⟫_ℂ)]

/--
**FR.** **U1** : une application `φ : Proj1 n → Proj1 n` (PAS supposée bijective)
préservant `tr(φ(P)φ(Q)) = tr(PQ)` pour TOUTE paire `P, Q` est une symétrie de
Wigner.

**EN.** U1: a map φ : Proj1 n → Proj1 n, NOT assumed bijective, that
preserves tr(φ(P)φ(Q)) = tr(PQ) for EVERY pair P, Q is a Wigner symmetry.
-/
theorem wigner_projection_form (n : ℕ) (φ : Proj1 n → Proj1 n)
    (hφ : ∀ P Q : Proj1 n, TraceProd (φ P) (φ Q) = TraceProd P Q) :
    IsWignerSymmetryProj φ := by
  rcases QuantumFoundations.Wigner.wigner n (T φ) (isWignerMap_T hφ) with ⟨U, hU⟩ | ⟨U, hU⟩
  · refine Or.inl ⟨U, fun x hx => ?_⟩
    obtain ⟨c, hc, hTc⟩ := hU x hx
    have hc0 : c ≠ 0 := by intro h; rw [h] at hc; simp at hc
    rw [T_repr φ hx, hTc, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc0)]
  · refine Or.inr ⟨U, fun x hx => ?_⟩
    obtain ⟨c, hc, hTc⟩ := hU x hx
    have hc0 : c ≠ 0 := by intro h; rw [h] at hc; simp at hc
    rw [T_repr φ hx, hTc, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc0)]

end
end QuantumFoundations.Uhlhorn
