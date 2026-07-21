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

/-- Toute `v : Sites N d` se développe dans la base canonique des
configurations (`Pi.single`/`EuclideanSpace.single`), coefficient = coordonnée. -/
private theorem euclid_expand (v : Sites N d) :
    v = ∑ k, v k • (EuclideanSpace.single k (1 : ℂ) : Sites N d) := by
  apply PiLp.ext
  intro j
  simp [Pi.single_apply, mul_ite, mul_one, mul_zero]

/-- Le produit scalaire avec un vecteur de base extrait la coordonnée. -/
private theorem euclid_coord (g : Fin N → Fin d) (x : Sites N d) :
    ⟪(EuclideanSpace.single g (1 : ℂ) : Sites N d), x⟫_ℂ = x g := by
  simp [PiLp.inner_apply]

/-- Élément de matrice d'une composée : `⟨g|S T|h⟩ = ∑ₖ ⟨k|T|h⟩ · ⟨g|S|k⟩`,
obtenu en développant `T (single h 1)` dans la base canonique. -/
private theorem matrixElem_comp (S T : Sites N d →ₗ[ℂ] Sites N d) (g h : Fin N → Fin d) :
    ⟪(EuclideanSpace.single g (1 : ℂ) : Sites N d), S (T (EuclideanSpace.single h 1))⟫_ℂ
      = ∑ k, ⟪(EuclideanSpace.single k (1 : ℂ) : Sites N d), T (EuclideanSpace.single h 1)⟫_ℂ
          * ⟪(EuclideanSpace.single g (1 : ℂ) : Sites N d), S (EuclideanSpace.single k 1)⟫_ℂ := by
  conv_lhs => rw [euclid_expand (T (EuclideanSpace.single h 1))]
  rw [map_sum, inner_sum]
  congr 1
  funext k
  rw [map_smul, inner_smul_right, ← euclid_coord k (T (EuclideanSpace.single h 1))]

/-- **Le témoin `k` unique** forcé par `AgreesOff A g k ∧ AgreesOff B k h` sous
`Disjoint A B` : `h` sur `A`, `g` sur `B` (et hors `A ∪ B`, cohérent ssi
`g = h` là-bas — voir `agreesOff_union_iff_kStar_B`). -/
private def kStar (A : Finset (Fin N)) (g h : Fin N → Fin d) : Fin N → Fin d :=
  fun x => if x ∈ A then h x else g x

private theorem kStar_agreesOff_left (A : Finset (Fin N)) (g h : Fin N → Fin d) :
    AgreesOff A g (kStar A g h) := by
  intro x hx
  simp [kStar, hx]

private theorem kStar_restrict_A (A : Finset (Fin N)) (g h : Fin N → Fin d) :
    (kStar A g h) ∘ (Subtype.val : {x // x ∈ A} → Fin N) = h ∘ Subtype.val := by
  funext x
  simp [kStar, x.2]

private theorem kStar_restrict_B {A B : Finset (Fin N)} (hAB : Disjoint A B)
    (g h : Fin N → Fin d) :
    (kStar A g h) ∘ (Subtype.val : {x // x ∈ B} → Fin N) = g ∘ Subtype.val := by
  funext x
  have hxA : (x : Fin N) ∉ A := fun hxA => (Finset.disjoint_left.mp hAB) hxA x.2
  simp [kStar, hxA]

private theorem kStar_unique {A B : Finset (Fin N)} (hAB : Disjoint A B) (g h k : Fin N → Fin d)
    (h1 : AgreesOff A g k) (h2 : AgreesOff B k h) : k = kStar A g h := by
  funext x
  by_cases hxA : x ∈ A
  · have hxB : x ∉ B := fun hxB => (Finset.disjoint_left.mp hAB) hxA hxB
    simp only [kStar, hxA, if_true]
    exact h2 x hxB
  · simp only [kStar, hxA, if_false]
    exact (h1 x hxA).symm

private theorem agreesOff_union_iff_kStar_B {A B : Finset (Fin N)} (g h : Fin N → Fin d) :
    AgreesOff B (kStar A g h) h ↔ AgreesOff (A ∪ B) g h := by
  constructor
  · intro hb x hx
    rw [Finset.mem_union, not_or] at hx
    obtain ⟨hxA, hxB⟩ := hx
    have := hb x hxB
    simpa [kStar, hxA] using this
  · intro hu x hxB
    by_cases hxA : x ∈ A
    · simp [kStar, hxA]
    · have := hu x (by rw [Finset.mem_union, not_or]; exact ⟨hxA, hxB⟩)
      simpa [kStar, hxA] using this

/-- Formule fermée pour l'élément de matrice d'une composée d'opérateurs
locaux à des ensembles disjoints : le seul témoin `k` qui contribue est
`kStar A g h`, ce qui collapse la somme sur `Fin N → Fin d` à un unique terme. -/
private theorem matrixElem_localComp {A B : Finset (Fin N)} (hAB : Disjoint A B)
    {S T : Sites N d →ₗ[ℂ] Sites N d}
    {s : ({x : Fin N // x ∈ A} → Fin d) → ({x : Fin N // x ∈ A} → Fin d) → ℂ}
    {t : ({x : Fin N // x ∈ B} → Fin d) → ({x : Fin N // x ∈ B} → Fin d) → ℂ}
    (hs : ∀ g k : Fin N → Fin d,
      ⟪(EuclideanSpace.single g (1 : ℂ) : Sites N d), S (EuclideanSpace.single k 1)⟫_ℂ
        = if AgreesOff A g k then s (g ∘ Subtype.val) (k ∘ Subtype.val) else 0)
    (ht : ∀ g k : Fin N → Fin d,
      ⟪(EuclideanSpace.single g (1 : ℂ) : Sites N d), T (EuclideanSpace.single k 1)⟫_ℂ
        = if AgreesOff B g k then t (g ∘ Subtype.val) (k ∘ Subtype.val) else 0)
    (g h : Fin N → Fin d) :
    ⟪(EuclideanSpace.single g (1 : ℂ) : Sites N d), S (T (EuclideanSpace.single h 1))⟫_ℂ
      = s (g ∘ Subtype.val) (h ∘ Subtype.val)
        * (if AgreesOff (A ∪ B) g h then t (g ∘ Subtype.val) (h ∘ Subtype.val) else 0) := by
  rw [matrixElem_comp]
  rw [Fintype.sum_eq_single (kStar A g h) ?_]
  · rw [ht, hs, if_pos (kStar_agreesOff_left A g h), kStar_restrict_A, mul_comm]
    simp only [agreesOff_union_iff_kStar_B, kStar_restrict_B hAB]
  · intro k hk
    by_cases hcond : AgreesOff A g k ∧ AgreesOff B k h
    · exact absurd (kStar_unique hAB g h k hcond.1 hcond.2) hk
    · rw [not_and_or] at hcond
      rcases hcond with hcond | hcond
      · simp [hs, hcond]
      · simp [ht, hcond]

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
  obtain ⟨s, hs⟩ := hS
  obtain ⟨t, ht⟩ := hT
  show S ∘ₗ T = T ∘ₗ S
  apply Module.Basis.ext (EuclideanSpace.basisFun (Fin N → Fin d) ℂ).toBasis
  intro h
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  apply PiLp.ext
  intro g
  rw [← euclid_coord g, ← euclid_coord g]
  show ⟪(EuclideanSpace.single g (1 : ℂ) : Sites N d), (S ∘ₗ T) (EuclideanSpace.single h 1)⟫_ℂ
      = ⟪(EuclideanSpace.single g (1 : ℂ) : Sites N d), (T ∘ₗ S) (EuclideanSpace.single h 1)⟫_ℂ
  show ⟪(EuclideanSpace.single g (1 : ℂ) : Sites N d), S (T (EuclideanSpace.single h 1))⟫_ℂ
      = ⟪(EuclideanSpace.single g (1 : ℂ) : Sites N d), T (S (EuclideanSpace.single h 1))⟫_ℂ
  rw [matrixElem_localComp hAB hs ht g h, matrixElem_localComp hAB.symm ht hs g h,
      Finset.union_comm B A]
  by_cases hP : AgreesOff (A ∪ B) g h
  · simp [hP, mul_comm]
  · simp [hP]

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
  rintro ⟨r, r', hrr', hcov⟩
  set BadA : Finset (Fin R) := Finset.univ.filter (fun ĝ => ¬ Disjoint (recB ĝ) (recA r))
    with hBadA_def
  set BadB : Finset (Fin R) := Finset.univ.filter (fun ĝ => ¬ Disjoint (recB ĝ) (recA r'))
    with hBadB_def
  have hBadA_le : BadA.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [hBadA_def, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_contra hab
    obtain ⟨x, hxa, hxr⟩ := Finset.not_disjoint_iff.mp ha
    obtain ⟨y, hyb, hyr⟩ := Finset.not_disjoint_iff.mp hb
    have hxy : x = y := Finset.card_le_one.mp (hsingleton r) x hxr y hyr
    subst hxy
    exact (Finset.disjoint_left.mp (hdisjB a b hab) hxa) hyb
  have hBadB_le : BadB.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [hBadB_def, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_contra hab
    obtain ⟨x, hxa, hxr⟩ := Finset.not_disjoint_iff.mp ha
    obtain ⟨y, hyb, hyr⟩ := Finset.not_disjoint_iff.mp hb
    have hxy : x = y := Finset.card_le_one.mp (hsingleton r') x hxr y hyr
    subst hxy
    exact (Finset.disjoint_left.mp (hdisjB a b hab) hxa) hyb
  have hsub : (Finset.univ : Finset (Fin R)) ⊆ BadA ∪ BadB := by
    intro ĝ _
    rw [Finset.mem_union, hBadA_def, hBadB_def, Finset.mem_filter, Finset.mem_filter]
    have := hcov ĝ
    rw [not_and_or] at this
    rcases this with h | h
    · left; exact ⟨Finset.mem_univ _, h⟩
    · right; exact ⟨Finset.mem_univ _, h⟩
  have hcard : R ≤ (BadA ∪ BadB).card := by
    have := Finset.card_le_card hsub
    simpa using this
  have hle2 : (BadA ∪ BadB).card ≤ 2 := by
    calc (BadA ∪ BadB).card ≤ BadA.card + BadB.card := Finset.card_union_le _ _
    _ ≤ 1 + 1 := by omega
    _ = 2 := by norm_num
  omega

end
end QuantumFoundations.Branches
