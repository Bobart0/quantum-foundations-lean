import QuantumFoundations.Branches.Nonvacuity

/-!
**FR.** # R1 — Lemmes généraux courts sur `LabeledResolution`

Jalon de dé-risquage minimal, avant `TwoObs.lean`/`Induction.lean`.

**EN.** # R1 — Short general lemmas on LabeledResolution

Minimal risk-reduction milestone, preceding TwoObs.lean/Induction.lean.
-/

namespace QuantumFoundations.Branches

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n K R : ℕ}

/--
**FR.** **Résolution de l'identité.** Somme des projections d'un record sur `x` :
`x` lui-même (`projL_sup_of_pairwise_isOrtho` + `covers`, gère les cellules
`⊥` sans difficulté — aucun champ `nz` requis).

**EN.** Resolution of the identity. The sum of the projections of a record
applied to x is x itself (projL_sup_of_pairwise_isOrtho + covers;
cells equal to ⊥ cause no difficulty—no nz field is required).
-/
theorem resolution_apply (Λ : LabeledResolution n K) (x : H n) :
    ∑ i, rproj Λ i x = x := by
  have hortho' : ∀ i ∈ (Finset.univ : Finset (Fin K)), ∀ j ∈ (Finset.univ : Finset (Fin K)),
      i ≠ j → Λ.cells i ⟂ Λ.cells j := by
    intro i _ j _ hij
    exact Submodule.isOrtho_iff_le.mpr (Λ.ortho i j hij)
  have hsum : projL (Finset.univ.sup Λ.cells) = ∑ i, projL (Λ.cells i) :=
    projL_sup_of_pairwise_isOrtho Finset.univ Λ.cells hortho'
  rw [Finset.sup_univ_eq_iSup, Λ.covers] at hsum
  have hid : projL (⊤ : Submodule ℂ (H n)) = LinearMap.id := by
    unfold projL
    rw [Submodule.starProjection_top]
    rfl
  rw [hid] at hsum
  have := congrArg (fun f => f x) hsum
  simpa using this.symm

/--
**FR.** **Contraction opératorielle.** Le produit de deux projections du MÊME
record : idempotence si les étiquettes coïncident, `0` sinon (orthogonalité).
Énoncé AU NIVEAU OPÉRATEURS (pas seulement pointwise) — le lemme de diagonale
`E` (`Induction.diagonal`) en a besoin ainsi, au contact du dernier maillon de
la chaîne.

**EN.** Operator contraction. The product of two projections from the SAME
record is idempotent when the labels coincide and 0 otherwise
(orthogonality). Stated AT THE OPERATOR LEVEL, not merely pointwise—the
diagonal lemma E (Induction.diagonal) requires precisely this form at the
point of contact with the final link of the chain.
-/
theorem rproj_contract (Λ : LabeledResolution n K) (i i' : Fin K) :
    rproj Λ i ∘ₗ rproj Λ i' = if i = i' then rproj Λ i else 0 := by
  split_ifs with h
  · subst h
    apply LinearMap.ext; intro x
    show (Λ.cells i).starProjection ((Λ.cells i).starProjection x) = (Λ.cells i).starProjection x
    exact congrFun (congrArg DFunLike.coe (Λ.cells i).isIdempotentElem_starProjection.eq) x
  · apply LinearMap.ext; intro x
    show (Λ.cells i).starProjection ((Λ.cells i').starProjection x) = 0
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact (Λ.ortho i' i (Ne.symm h)) (Submodule.starProjection_apply_mem (Λ.cells i') x)

/--
**FR.** Application ponctuelle de `Commute` (`Commute S T` est défeq à
`S ∘ₗ T = T ∘ₗ S`) — utilitaire réutilisé par `TwoObs.lean` et
`Induction.lean` (relocalisé public dès le second usage).

**EN.** Pointwise application of Commute (Commute S T is definitionally equal
to S ∘ₗ T = T ∘ₗ S)—a utility reused by TwoObs.lean and
Induction.lean, and made public upon its second use.
-/
theorem commute_apply {S T : H n →ₗ[ℂ] H n} (h : Commute S T) (x : H n) :
    S (T x) = T (S x) := by
  have := congrArg (fun f => f x) h
  simpa using this

/--
**FR.** Forme ponctuelle de `rproj_contract`, sur un vecteur explicite plutôt
qu'au niveau opérateurs — plus directe à combiner avec les substitutions de
`TwoObs.lean`/`Induction.lean` (relocalisé public dès le second usage).

**EN.** Pointwise form of rproj_contract, on an explicit vector rather than at
the operator level—more convenient to combine with the substitutions in
TwoObs.lean/Induction.lean, and made public upon its second use.
-/
theorem rproj_contract_apply (Λ : LabeledResolution n K) (i i' : Fin K) (x : H n) :
    rproj Λ i (rproj Λ i' x) = (if i = i' then (1 : ℂ) else 0) • rproj Λ i' x := by
  have h := congrArg (fun T => T x) (rproj_contract Λ i i')
  split_ifs at h ⊢ with heq
  · subst heq; simpa using h
  · simpa using h

/--
**FR.** **`branch` est indépendant du record choisi**, sous redondance
(`IsRecordedOn`) — justifie a posteriori le choix arbitraire du record `0`
dans la définition de `branch`.

**EN.** branch is independent of the chosen record under redundancy
(IsRecordedOn)—this retrospectively justifies the arbitrary choice of
record 0 in the definition of branch.
-/
theorem branch_wellDefined [NeZero R] (ψ : H n) (recs : Fin R → LabeledResolution n K)
    (hrec : IsRecordedOn ψ recs) (r : Fin R) (i : Fin K) :
    branch recs ψ i = rproj (recs r) i ψ := by
  show rproj (recs 0) i ψ = rproj (recs r) i ψ
  exact hrec 0 r i

/--
**FR.** **Les branches d'un même record sont deux à deux orthogonales.**

**EN.** Branches of the same record are pairwise orthogonal.
-/
theorem branch_orthogonal [NeZero R] (ψ : H n) (recs : Fin R → LabeledResolution n K)
    {i i' : Fin K} (hii : i ≠ i') :
    ⟪branch recs ψ i, branch recs ψ i'⟫_ℂ = 0 := by
  show ⟪rproj (recs 0) i ψ, rproj (recs 0) i' ψ⟫_ℂ = 0
  have hmem : rproj (recs 0) i ψ ∈ (recs 0).cells i := Submodule.starProjection_apply_mem _ _
  have hmem' : rproj (recs 0) i' ψ ∈ (recs 0).cells i' := Submodule.starProjection_apply_mem _ _
  have hortho' : (recs 0).cells i' ≤ ((recs 0).cells i)ᗮ := (recs 0).ortho i' i hii.symm
  exact (Submodule.mem_orthogonal ((recs 0).cells i) _).mp (hortho' hmem') _ hmem

end
end QuantumFoundations.Branches
