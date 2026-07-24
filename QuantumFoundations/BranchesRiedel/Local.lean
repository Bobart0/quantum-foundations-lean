import QuantumFoundations.BranchesRiedel.Induction

/-!
**FR.** # R4 — Couche 2 : modèle multi-sites plat, localité, disjonction spatiale

Modèle concret : `Sites N d := EuclideanSpace ℂ ((Fin N) → Fin d)` — le choix
K₂ (somme directe plate), jamais le `TensorProduct` abstrait de Mathlib, par
cohérence avec le choix K₂ déjà retenu côté Naimark (`DilSpace.lean`). Cette
brique servira aussi à Stinespring plus tard.

## `IsLocalTo` : noyau existentiel sur les éléments de matrice (décision F)

`IsLocalTo` est une `Prop` à noyau existentiel sur les éléments de matrice
(pas un constructeur opératoriel `localLift` — celui-ci est relégué en outil
optionnel R5). Restriction d'une configuration `g : Fin N → Fin d` à un
sous-ensemble de sites `A : Finset (Fin N)` par simple composition
`g ∘ Subtype.val : ({x // x ∈ A} → Fin d)` — confirmé en reconnaissance,
aucune plomberie supplémentaire nécessaire.

## Pont couche 2 ↔ couche 1 : non construit ici (avertissement)

`commuteWitness_of_not_pairCovers` et `riedel_local` ci-dessous ont besoin
d'identifier `Sites N d` à un `H n` (couche 1) — nécessairement, puisque
`LabeledResolution`/`CommuteWitness` sont typées sur `H n`
(`Module.finrank ℂ (Sites N d) = d ^ N`, donc `n := d ^ N`). Contrairement au
témoin de `Nonvacuity.lean` (une seule observable, pont évité par
construction), ce pont constitue le véritable travail de ce jalon : les
signatures ci-dessous le rendent explicite via un paramètre `e : H (d ^ N)
≃ₗᵢ[ℂ] Sites N d` plutôt que de le construire à la volée — la signature la
moins stabilisée de tout le squelette R0, à raffiner en remplissant R4.

**EN.** # R4 — Layer 2: flat multisite model, locality, and spatial disjointness

Concrete model: Sites N d := EuclideanSpace ℂ ((Fin N) → Fin d), the K₂
(flat direct-sum) choice, never Mathlib's abstract TensorProduct, for
consistency with the K₂ choice already made on the Naimark side
(DilSpace.lean). This component will also be used later for Stinespring.

## IsLocalTo: existential kernel on matrix elements (decision F)

IsLocalTo is a Prop with an existential kernel on matrix elements (not an
operator constructor localLift, which is relegated to the optional R5
tool). A configuration g : Fin N → Fin d is restricted to a subset of
sites A : Finset (Fin N) by simple composition:
g ∘ Subtype.val : ({x // x ∈ A} → Fin d). The scoping phase confirmed that
no additional plumbing is needed.

## Layer-2 ↔ layer-1 bridge: not constructed here (warning)

commuteWitness_of_not_pairCovers and riedel_local below require an
identification of Sites N d with some H n (layer 1), necessarily so
because LabeledResolution/CommuteWitness are typed over H n
(Module.finrank ℂ (Sites N d) = d ^ N, hence n := d ^ N). Unlike the
witness in Nonvacuity.lean (a single observable, with the bridge avoided by
construction), this bridge constitutes the actual work of this milestone.
The signatures below make it explicit through a parameter
e : H (d ^ N) ≃ₗᵢ[ℂ]
Sites N d rather than constructing it on the fly,
the least stable signature in the entire R0 skeleton, to be refined while
completing R4.
-/

namespace QuantumFoundations.BranchesRiedel

open scoped InnerProductSpace Classical
open Gleason

noncomputable section

variable {N d : ℕ}

/-- Espace plat multi-sites : `N` sites, chacun de dimension `d`. -/
abbrev Sites (N d : ℕ) := EuclideanSpace ℂ ((Fin N) → Fin d)

/--
**FR.** Deux configurations coïncident HORS de `A`.

**EN.** Two configurations agree OUTSIDE A.
-/
def AgreesOff (A : Finset (Fin N)) (g k : Fin N → Fin d) : Prop := ∀ s ∉ A, g s = k s

/--
**FR.** `T` est LOCAL à `A` : ses éléments de matrice, dans la base des
configurations, ne dépendent que des restrictions à `A` des deux
configurations, et s'annulent dès qu'elles diffèrent HORS de `A`.

**EN.** T is LOCAL to A: in the configuration basis, its matrix elements
depend only on the restrictions of the two configurations to A, and vanish
whenever the configurations differ OUTSIDE A.
-/
def IsLocalTo (T : Sites N d →ₗ[ℂ] Sites N d) (A : Finset (Fin N)) : Prop :=
  ∃ s : ({x // x ∈ A} → Fin d) → ({x // x ∈ A} → Fin d) → ℂ, ∀ g k : Fin N → Fin d,
    ⟪(EuclideanSpace.single g (1 : ℂ) : Sites N d), T (EuclideanSpace.single k (1 : ℂ))⟫_ℂ =
      if AgreesOff A g k then s (g ∘ Subtype.val) (k ∘ Subtype.val) else 0

/--
**FR.** **Pair-covering** (transcription de la définition de Riedel via
`Finset.Disjoint`) : `recA` pair-couvre `recB` s'il existe une paire de
records DISTINCTS de `recA` qu'AUCUN record de `recB` ne peut départager par
disjonction spatiale. La négation `¬ PairCovers recA recB` donne exactement
la forme requise par `CommuteWitness` (`∀ r r', ∃ ĝ, …`) une fois transportée
via `commute_of_disjoint`.

**EN.** Pair-covering (a transcription of Riedel's definition using
Finset.Disjoint): recA pair-covers recB if there is a pair of DISTINCT
records of recA that NO record of recB can separate by spatial
disjointness. Once transported through commute_of_disjoint, the negation
¬ PairCovers recA recB has exactly the form required by CommuteWitness
(∀ r r', ∃ ĝ, …).
-/
def PairCovers {R : ℕ} (recA recB : Fin R → Finset (Fin N)) : Prop :=
  ∃ r r' : Fin R, r ≠ r' ∧
    ∀ ĝ : Fin R, ¬ (Disjoint (recB ĝ) (recA r) ∧ Disjoint (recB ĝ) (recA r'))

/--
**FR.** Toute `v : Sites N d` se développe dans la base canonique des
configurations (`Pi.single`/`EuclideanSpace.single`), coefficient = coordonnée.

**EN.** Every v : Sites N d expands in the canonical configuration basis
(Pi.single/EuclideanSpace.single), with coefficient = coordinate.
-/
private theorem euclid_expand (v : Sites N d) :
    v = ∑ k, v k • (EuclideanSpace.single k (1 : ℂ) : Sites N d) := by
  apply PiLp.ext
  intro j
  simp [Pi.single_apply, mul_ite, mul_one, mul_zero]

/--
**FR.** Le produit scalaire avec un vecteur de base extrait la coordonnée.

**EN.** The inner product with a basis vector extracts the corresponding coordinate.
-/
private theorem euclid_coord (g : Fin N → Fin d) (x : Sites N d) :
    ⟪(EuclideanSpace.single g (1 : ℂ) : Sites N d), x⟫_ℂ = x g := by
  simp [PiLp.inner_apply]

/--
**FR.** Élément de matrice d'une composée : `⟨g|S T|h⟩ = ∑ₖ ⟨k|T|h⟩ · ⟨g|S|k⟩`,
obtenu en développant `T (single h 1)` dans la base canonique.

**EN.** Matrix element of a composition:
⟨g|S T|h⟩ = ∑ₖ ⟨k|T|h⟩ · ⟨g|S|k⟩, obtained by expanding
T (single h 1) in the canonical basis.
-/
private theorem matrixElem_comp (S T : Sites N d →ₗ[ℂ] Sites N d) (g h : Fin N → Fin d) :
    ⟪(EuclideanSpace.single g (1 : ℂ) : Sites N d), S (T (EuclideanSpace.single h 1))⟫_ℂ
      = ∑ k, ⟪(EuclideanSpace.single k (1 : ℂ) : Sites N d), T (EuclideanSpace.single h 1)⟫_ℂ
          * ⟪(EuclideanSpace.single g (1 : ℂ) : Sites N d), S (EuclideanSpace.single k 1)⟫_ℂ := by
  conv_lhs => rw [euclid_expand (T (EuclideanSpace.single h 1))]
  rw [map_sum, inner_sum]
  congr 1
  funext k
  rw [map_smul, inner_smul_right, ← euclid_coord k (T (EuclideanSpace.single h 1))]

/--
**FR.** **Le témoin `k` unique** forcé par `AgreesOff A g k ∧ AgreesOff B k h` sous
`Disjoint A B` : `h` sur `A`, `g` sur `B` (et hors `A ∪ B`, cohérent ssi
`g = h` là-bas — voir `agreesOff_union_iff_kStar_B`).

**EN.** The unique witness k forced by
AgreesOff A g k ∧ AgreesOff B k h under Disjoint A B: it equals h on
A and g on B (and outside A ∪ B this is consistent iff g = h
there; see agreesOff_union_iff_kStar_B).
-/
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

/--
**FR.** Formule fermée pour l'élément de matrice d'une composée d'opérateurs
locaux à des ensembles disjoints : le seul témoin `k` qui contribue est
`kStar A g h`, ce qui collapse la somme sur `Fin N → Fin d` à un unique terme.

**EN.** Closed formula for the matrix element of a composition of operators
local to disjoint sets: the only contributing witness k is
kStar A g h, which collapses the sum over Fin N → Fin d to a single term.
-/
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

/--
**FR.** **LA brique neuve (R4).** Deux opérateurs locaux à des ensembles de sites
DISJOINTS commutent. Stratégie vérifiée à la main (voir prompt de conception) :
égalité des éléments de matrice — dans `(S ∘ T)_{g,h} = ∑ₖ S_{g,k} T_{k,h}`,
les deltas d'`AgreesOff` forcent un `k` unique cohérent (`k = g` hors `A`,
`k = h` hors `B`, compatible car `g = h` hors `A ∪ B` sinon les deux membres
sont nuls) ; les deux côtés valent alors `s(g|A,h|A) · t(g|B,h|B) · [g = h
hors A∪B]` — symétrique en `S,T`. Pure comptabilité de deltas sur des sommes
de base (calibration : `Naimark/SqrtOp.lean`, N2).

**EN.** THE new component (R4). Two operators local to DISJOINT sets of
sites commute. The strategy was checked by hand (see the design prompt):
equality of matrix elements. In
(S ∘ T)_{g,h} = ∑ₖ S_{g,k} T_{k,h}, the AgreesOff deltas force a unique
consistent k (k = g outside A, k = h outside B; these conditions
are compatible because g = h outside A ∪ B, and otherwise both sides
vanish). Both sides therefore equal
s(g|A,h|A) · t(g|B,h|B) · [g = h
hors A∪B], which is symmetric in
S,T. This is pure delta bookkeeping over basis sums (calibration:
Naimark/SqrtOp.lean, N2).
-/
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

/--
**FR.** **Dé-conjugaison.** Si les formes conjuguées par une isométrie linéaire
`e` de deux opérateurs commutent, les opérateurs eux-mêmes commutent —
`e.toLinearEquiv.conj` est l'équivalence de conjugaison sur les endomorphismes
(`LinearEquiv.conj`), multiplicative (`conj_comp`) et bijective, donc injective.

**EN.** Deconjugation. If the forms of two operators conjugated by a linear
isometry e commute, then the operators themselves commute:
e.toLinearEquiv.conj is the conjugation equivalence on endomorphisms
(LinearEquiv.conj), is multiplicative (conj_comp) and bijective, and is
therefore injective.
-/
private theorem commute_of_conj_commute {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ E] [InnerProductSpace ℂ F] (e : E ≃ₗᵢ[ℂ] F) (S T : E →ₗ[ℂ] E)
    (h : Commute (e.toLinearIsometry.toLinearMap ∘ₗ S ∘ₗ e.symm.toLinearIsometry.toLinearMap)
                  (e.toLinearIsometry.toLinearMap ∘ₗ T ∘ₗ e.symm.toLinearIsometry.toLinearMap)) :
    Commute S T := by
  have hconjS : e.toLinearEquiv.conj S
      = e.toLinearIsometry.toLinearMap ∘ₗ S ∘ₗ e.symm.toLinearIsometry.toLinearMap := rfl
  have hconjT : e.toLinearEquiv.conj T
      = e.toLinearIsometry.toLinearMap ∘ₗ T ∘ₗ e.symm.toLinearIsometry.toLinearMap := rfl
  rw [← hconjS, ← hconjT] at h
  show S ∘ₗ T = T ∘ₗ S
  apply e.toLinearEquiv.conj.injective
  rw [LinearEquiv.conj_comp, LinearEquiv.conj_comp]
  exact h

/--
**FR.** **Pont couche 2 → couche 1.** Si chaque record de chaque observable,
transporté via `e` sur `Sites N d`, est local à un ensemble de sites, et
qu'aucune paire d'observables ne se pair-couvre, alors la famille satisfait
`CommuteWitness` — assemblage de `commute_of_disjoint` (sur `Sites N d`) et
`commute_of_conj_commute` (rapatrie la commutation sur `H (d ^ N)`).
**`hR2 : 2 ≤ R`** : hypothèse nécessaire pour le cas `r = r'` de
`CommuteWitness` (qui quantifie sur TOUS les couples de records d'une même
observable, y compris confondus), alors que `¬ PairCovers` — issu de
`PairCovers` qui exige `r ≠ r'` dans sa définition — ne fournit un témoin
QUE pour les couples distincts. Cas `r = r'` traité en réutilisant le témoin
d'un couple `(r, r'')` quelconque, `r'' ≠ r` (existe par `hR2`) : ce témoin
est disjoint de `supp a r`, ce qui suffit puisque les deux conjoncts requis
coïncident. Coût nul : la redondance de records n'a de sens physique que
pour `R ≥ 2`.

**EN.** Layer-2 → layer-1 bridge. Suppose every record of every observable,
transported through e to Sites N d, is local to a set of sites, and no
pair of observables pair-covers the other. Then the family satisfies
CommuteWitness, by combining commute_of_disjoint on Sites N d with
commute_of_conj_commute, which transports commutation back to
H (d ^ N).
**hR2 : 2 ≤ R** is required for the case r = r' of CommuteWitness
(which quantifies over ALL pairs of records of the same observable, including
equal ones), whereas ¬ PairCovers—arising from PairCovers, whose definition
requires r ≠ r'—provides a witness ONLY for distinct pairs. The case
r = r' is handled by reusing the witness for an arbitrary pair
(r, r'') with r'' ≠ r (which exists by hR2): that witness is disjoint
from supp a r, which suffices because the two required conjuncts then
coincide. This has no physical cost, since record redundancy is meaningful
only for R ≥ 2.
-/
theorem commuteWitness_of_not_pairCovers {A R K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (Obs : Fin A → Fin R → LabeledResolution (d ^ N) K)
    (supp : Fin A → Fin R → Finset (Fin N)) (hR2 : 2 ≤ R)
    (hlocal : ∀ a r i, IsLocalTo
      (e.toLinearIsometry.toLinearMap ∘ₗ rproj (Obs a r) i ∘ₗ e.symm.toLinearIsometry.toLinearMap)
      (supp a r))
    (hnpc : ∀ a b : Fin A, a ≠ b → ¬ PairCovers (supp a) (supp b)) :
    CommuteWitness Obs := by
  haveI : Nontrivial (Fin R) := Fin.nontrivial_iff_two_le.mpr hR2
  intro a b hab r r'
  have hnpc' := hnpc a b hab
  unfold PairCovers at hnpc'
  push Not at hnpc'
  rcases eq_or_ne r r' with hrr' | hrr'
  · obtain ⟨r'', hr''⟩ := exists_ne r
    obtain ⟨ĝ, hĝ⟩ := hnpc' r r'' (Ne.symm hr'')
    subst hrr'
    refine ⟨ĝ, fun i j => ?_⟩
    have hcommute := commute_of_conj_commute e _ _
      (commute_of_disjoint hĝ.1.symm (hlocal a r i) (hlocal b ĝ j))
    exact ⟨hcommute, hcommute⟩
  · obtain ⟨ĝ, hĝ⟩ := hnpc' r r' hrr'
    exact ⟨ĝ, fun i j =>
      ⟨commute_of_conj_commute e _ _ (commute_of_disjoint hĝ.1.symm (hlocal a r i) (hlocal b ĝ j)),
       commute_of_conj_commute e _ _
         (commute_of_disjoint hĝ.2.symm (hlocal a r' i) (hlocal b ĝ j))⟩⟩

/--
**FR.** **Corollaire local du théorème de Riedel.** Sous redondance
(`IsRecordedOn`) et non-pair-covering deux à deux, `ψ` se décompose en
branches jointes uniques et orthogonales. `e`/`hlocal` ne servent qu'à établir
`CommuteWitness` (via `commuteWitness_of_not_pairCovers`) — `Induction.riedel`
s'applique ensuite DIRECTEMENT sur `H (d ^ N)`, sans transport de conclusion
(les `Obs`/`ψ` y vivent depuis le début).

**EN.** Local corollary of Riedel's theorem. Under redundancy
(IsRecordedOn) and pairwise non-pair-covering, ψ decomposes into unique
orthogonal joint branches. e/hlocal are used only to establish
CommuteWitness (via commuteWitness_of_not_pairCovers); Induction.riedel
then applies DIRECTLY on H (d ^ N), without transporting the conclusion,
since Obs/ψ live there from the outset.
-/
theorem riedel_local {A R K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (Obs : Fin A → Fin R → LabeledResolution (d ^ N) K)
    (supp : Fin A → Fin R → Finset (Fin N)) [NeZero R] [NeZero K] (hR2 : 2 ≤ R) (ψ : H (d ^ N))
    (hrec : ∀ a, IsRecordedOn ψ (Obs a))
    (hlocal : ∀ a r i, IsLocalTo
      (e.toLinearIsometry.toLinearMap ∘ₗ rproj (Obs a r) i ∘ₗ e.symm.toLinearIsometry.toLinearMap)
      (supp a r))
    (hnpc : ∀ a b : Fin A, a ≠ b → ¬ PairCovers (supp a) (supp b)) :
    (∑ f : Fin A → Fin K, jointBranch Obs ψ f = ψ) ∧
    (∀ f f' : Fin A → Fin K, f ≠ f' → ⟪jointBranch Obs ψ f, jointBranch Obs ψ f'⟫_ℂ = 0) :=
  let hcw := commuteWitness_of_not_pairCovers e Obs supp hR2 hlocal hnpc
  ⟨riedel Obs ψ hrec hcw |>.1, riedel Obs ψ hrec hcw |>.2.1⟩

/--
**FR.** **Corollaire de comptage (Finset.card pur).** Si les records de `recA`
sont des singletons et que `recB` compte au moins trois records DEUX À DEUX
disjoints, `recA` ne peut pas pair-couvrir `recB` — pour toute paire `(r,r')`
de `recA`, au plus deux des records de `recB` peuvent chacun intersecter
`r ∪ r'` (`|r|,|r'| ≤ 1`), donc au moins un des trois est disjoint des deux.
**Énoncé PROVISOIRE, restreint aux records singletons** : l'instanciation
métrique générale (boules/distances, records de taille bornée quelconque) est
HORS SCOPE de ce bloc — extension future possible, voir `SORRIES.md`.

**EN.** Counting corollary (pure Finset.card). If the records of recA
are singletons and recB has at least three PAIRWISE disjoint records, then
recA cannot pair-cover recB: for any pair (r,r') of records of recA,
at most two records of recB can each intersect r ∪ r'
(|r|,|r'| ≤ 1), so at least one of the three is disjoint from both.
PROVISIONAL statement, restricted to singleton records: the general
metric instantiation (balls/distances, records of arbitrary bounded size) is
OUT OF SCOPE for this block; a future extension is possible, as noted in
SORRIES.md.
-/
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
end QuantumFoundations.BranchesRiedel
