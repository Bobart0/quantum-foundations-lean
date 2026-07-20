import QuantumFoundations.Branches.Induction

/-!
# R4 — Couche 2 : modèle multi-sites plat, localité, disjonction spatiale

Modèle CONCRET : `Sites N d := EuclideanSpace ℂ ((Fin N) → Fin d)` — route K₂
du TODO mémoire, JAMAIS le `TensorProduct` abstrait de Mathlib. Cette brique
servira aussi à Stinespring plus tard.

## `IsLocalTo` : noyau existentiel sur les éléments de matrice (décision F)

`IsLocalTo` est une `Prop` à NOYAU EXISTENTIEL sur les éléments de matrice
(pas un constructeur opératoriel `localLift` — celui-ci est relégué en outil
optionnel R5). Restriction d'une configuration `g : Fin N → Fin d` à un
sous-ensemble de sites `A : Finset (Fin N)` par simple COMPOSITION
`g ∘ Subtype.val : ({x // x ∈ A} → Fin d)` — confirmé en reconnaissance,
aucune plomberie supplémentaire nécessaire.

## Pont couche 2 ↔ couche 1 : PAS construit ici (avertissement)

`commuteWitness_of_not_pairCovers` et `riedel_local` ci-dessous ont besoin
d'identifier `Sites N d` à un `H n` (couche 1) — nécessairement, puisque
`LabeledResolution`/`CommuteWitness` sont typées sur `H n`
(`Module.finrank ℂ (Sites N d) = d ^ N`, donc `n := d ^ N`). Contrairement au
témoin de `Nonvacuity.lean` (une seule observable, pont évité par
construction), CE pont est le VRAI travail de ce jalon : les signatures
ci-dessous le rendent explicite via un paramètre `e : H (d ^ N) ≃ₗᵢ[ℂ]
Sites N d` plutôt que de le construire à la volée — **signature la MOINS
stabilisée de tout le squelette R0**, à raffiner en remplissant R4.
-/

namespace QuantumFoundations.Branches

open scoped InnerProductSpace Classical
open Gleason

noncomputable section

variable {N d : ℕ}

/-- Espace plat multi-sites : `N` sites, chacun de dimension `d`. -/
abbrev Sites (N d : ℕ) := EuclideanSpace ℂ ((Fin N) → Fin d)

/-- Deux configurations coïncident HORS de `A`. -/
def AgreesOff (A : Finset (Fin N)) (g k : Fin N → Fin d) : Prop := ∀ s ∉ A, g s = k s

/-- `T` est LOCAL à `A` : ses éléments de matrice, dans la base des
configurations, ne dépendent que des restrictions à `A` des deux
configurations, et s'annulent dès qu'elles diffèrent HORS de `A`. -/
def IsLocalTo (T : Sites N d →ₗ[ℂ] Sites N d) (A : Finset (Fin N)) : Prop :=
  ∃ s : ({x // x ∈ A} → Fin d) → ({x // x ∈ A} → Fin d) → ℂ, ∀ g k : Fin N → Fin d,
    ⟪(EuclideanSpace.single g (1 : ℂ) : Sites N d), T (EuclideanSpace.single k (1 : ℂ))⟫_ℂ =
      if AgreesOff A g k then s (g ∘ Subtype.val) (k ∘ Subtype.val) else 0

/-- **Pair-covering** (transcription de la définition de Riedel via
`Finset.Disjoint`) : `recA` pair-couvre `recB` s'il existe une paire de
records DISTINCTS de `recA` qu'AUCUN record de `recB` ne peut départager par
disjonction spatiale. La négation `¬ PairCovers recA recB` donne exactement
la forme requise par `CommuteWitness` (`∀ r r', ∃ ĝ, …`) une fois transportée
via `commute_of_disjoint`. -/
def PairCovers {R : ℕ} (recA recB : Fin R → Finset (Fin N)) : Prop :=
  ∃ r r' : Fin R, r ≠ r' ∧
    ∀ ĝ : Fin R, ¬ (Disjoint (recB ĝ) (recA r) ∧ Disjoint (recB ĝ) (recA r'))

/-- **LA brique neuve (R4).** Deux opérateurs locaux à des ensembles de sites
DISJOINTS commutent. Stratégie vérifiée à la main (voir prompt de conception) :
égalité des éléments de matrice — dans `(S ∘ T)_{g,h} = ∑ₖ S_{g,k} T_{k,h}`,
les deltas d'`AgreesOff` forcent un `k` unique cohérent (`k = g` hors `A`,
`k = h` hors `B`, compatible car `g = h` hors `A ∪ B` sinon les deux membres
sont nuls) ; les deux côtés valent alors `s(g|A,h|A) · t(g|B,h|B) · [g = h
hors A∪B]` — symétrique en `S,T`. Pure comptabilité de deltas sur des sommes
de base (calibration : `Naimark/SqrtOp.lean`, N2). -/
theorem commute_of_disjoint {A B : Finset (Fin N)} (hAB : Disjoint A B)
    {S T : Sites N d →ₗ[ℂ] Sites N d} (hS : IsLocalTo S A) (hT : IsLocalTo T B) :
    Commute S T := by
  sorry

/-- **Pont couche 2 → couche 1 (signature PROVISOIRE, voir avertissement
d'en-tête).** Si chaque record de chaque observable, transporté via `e` sur
`Sites N d`, est local à un ensemble de sites, et qu'aucune paire
d'observables ne se pair-couvre, alors la famille satisfait `CommuteWitness`
— assemblage direct de `commute_of_disjoint`. -/
theorem commuteWitness_of_not_pairCovers {A R K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (Obs : Fin A → Fin R → LabeledResolution (d ^ N) K)
    (supp : Fin A → Fin R → Finset (Fin N))
    (hlocal : ∀ a r i, IsLocalTo
      (e.toLinearIsometry.toLinearMap ∘ₗ rproj (Obs a r) i ∘ₗ e.symm.toLinearIsometry.toLinearMap)
      (supp a r))
    (hnpc : ∀ a b : Fin A, a ≠ b → ¬ PairCovers (supp a) (supp b)) :
    CommuteWitness Obs := by
  sorry

/-- **Corollaire local du théorème de Riedel (signature PROVISOIRE).**
`Induction.riedel`, combiné à `commuteWitness_of_not_pairCovers` : sous
redondance et non-pair-covering DEUX À DEUX, `ψ` (transporté sur `H (d ^ N)`
via `e`) se décompose en branches jointes uniques et orthogonales. -/
theorem riedel_local {A R K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (Obs : Fin A → Fin R → LabeledResolution (d ^ N) K)
    (supp : Fin A → Fin R → Finset (Fin N)) [NeZero R] (ψ : H (d ^ N))
    (hrec : ∀ a, IsRecordedOn ψ (Obs a))
    (hlocal : ∀ a r i, IsLocalTo
      (e.toLinearIsometry.toLinearMap ∘ₗ rproj (Obs a r) i ∘ₗ e.symm.toLinearIsometry.toLinearMap)
      (supp a r))
    (hnpc : ∀ a b : Fin A, a ≠ b → ¬ PairCovers (supp a) (supp b)) :
    (∑ f : Fin A → Fin K, jointBranch Obs ψ f = ψ) ∧
    (∀ f f' : Fin A → Fin K, f ≠ f' → ⟪jointBranch Obs ψ f, jointBranch Obs ψ f'⟫_ℂ = 0) := by
  sorry

/-- **Corollaire de comptage (Finset.card pur).** Si les records de `recA`
sont des singletons et que `recB` compte au moins trois records DEUX À DEUX
disjoints, `recA` ne peut pas pair-couvrir `recB` — pour toute paire `(r,r')`
de `recA`, au plus deux des records de `recB` peuvent chacun intersecter
`r ∪ r'` (`|r|,|r'| ≤ 1`), donc au moins un des trois est disjoint des deux.
**Énoncé PROVISOIRE, restreint aux records singletons** : l'instanciation
métrique générale (boules/distances, records de taille bornée quelconque) est
HORS SCOPE de ce bloc — extension future possible, voir `SORRIES.md`. -/
theorem pigeonhole_corollary {R : ℕ} (recA recB : Fin R → Finset (Fin N))
    (hR : 3 ≤ R) (hsingleton : ∀ r, (recA r).card ≤ 1)
    (hdisjB : ∀ r r' : Fin R, r ≠ r' → Disjoint (recB r) (recB r')) :
    ¬ PairCovers recA recB := by
  sorry

end
end QuantumFoundations.Branches
