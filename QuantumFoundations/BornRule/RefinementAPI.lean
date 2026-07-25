import QuantumFoundations.BornRule.Perspective

/-!
**FR.** # API de raffinement pour les développements aval

Ce module est une **API destinée aux développements aval** (théorie de la
décision bornienne, `everettian-probability-lean`) : il n'a **aucun rôle dans
l'argument du manuscrit** *One State, Many Perspectives*. Il est **strictement
additif** : il ne contient aucun résultat mathématique nouveau, seulement des
reformulations et des conséquences immédiates de `BornRule.Perspective.lean`
(réflexivité et transitivité de `Refines`, une carte parent totale construite
par choix classique sur le témoin d'existence déjà fourni par `Refines`, et une
présentation stabilisée du filtre utilisé par `AxGrain`).

Aucun énoncé existant de `Perspective.lean` n'est modifié, renommé, affaibli ou
renforcé.

**EN.** # Refinement API for downstream developments

This module is a **downstream-facing API** (Born-weight decision theory,
`everettian-probability-lean`): it has **no role in the manuscript's
argument** *One State, Many Perspectives*. It is **strictly additive**: it
contains no new mathematical result, only reformulations and immediate
consequences of `BornRule.Perspective.lean` (reflexivity and transitivity of
`Refines`, a total parent map built by classical choice on the existence
witness `Refines` already supplies, and a stabilized presentation of the
filter used by `AxGrain`).

No existing declaration in `Perspective.lean` is modified, renamed, weakened,
or strengthened.
-/

namespace QuantumFoundations.BornRule

open scoped InnerProductSpace
open scoped Classical
open Gleason

noncomputable section

variable {n : ℕ}

/-! ## Reflexivity and transitivity of `Refines` -/

/--
**FR.** Toute perspective se raffine elle-même, via l'inclusion réflexive de
chaque cellule dans elle-même.

**EN.** Every perspective refines itself, via the reflexive inclusion of each
cell in itself.
-/
theorem Refines.refl (D : Perspective n) : Refines D D :=
  fun c' hc' => ⟨c', hc', le_refl c'⟩

/--
**FR.** `Refines` est transitive : si `D''` raffine `D'` et `D'` raffine `D`,
alors `D''` raffine `D`, par transport de l'inclusion `≤` le long de la
chaîne des deux témoins d'existence.

**EN.** `Refines` is transitive: if `D''` refines `D'` and `D'` refines `D`,
then `D''` refines `D`, by transporting the `≤` inclusion along the chain of
the two existence witnesses.
-/
theorem Refines.trans {D'' D' D : Perspective n} (r1 : Refines D'' D') (r2 : Refines D' D) :
    Refines D'' D := by
  intro c'' hc''
  obtain ⟨c', hc', hle1⟩ := r1 c'' hc''
  obtain ⟨c, hc, hle2⟩ := r2 c' hc'
  exact ⟨c, hc, hle1.trans hle2⟩

/-! ## A total parent map on refinement -/

/--
**FR.** La cellule grossière associée à une cellule fine `c'` sous un
raffinement `r`, construite par choix classique sur le témoin d'existence de
`Refines`. **Définition totale** (patron maison « définition totale + valeur
poubelle ») : hors de `D'.cells`, la valeur de repli est `c'` lui-même ; `r`
n'est jamais forcé à produire une preuve pour un argument hors domaine.

**EN.** The coarse cell associated with a fine cell `c'` under a refinement
`r`, built by classical choice on the existence witness supplied by
`Refines`. **Total definition** (the repository's "total definition + junk
value" pattern): outside `D'.cells`, the fallback value is `c'` itself; `r`
is never forced to produce a proof for an out-of-domain argument.
-/
noncomputable def parentOf {D' D : Perspective n} (r : Refines D' D) (c' : Submodule ℂ (H n)) :
    Submodule ℂ (H n) :=
  if h : c' ∈ D'.cells then (r c' h).choose else c'

/-- **FR.** Le parent choisi appartient bien à la perspective grossière.
**EN.** The chosen parent does belong to the coarse perspective. -/
theorem parentOf_mem {D' D : Perspective n} (r : Refines D' D) {c' : Submodule ℂ (H n)}
    (hc' : c' ∈ D'.cells) : parentOf r c' ∈ D.cells := by
  unfold parentOf
  rw [dif_pos hc']
  exact (r c' hc').choose_spec.1

/-- **FR.** La cellule fine est bien incluse dans son parent choisi.
**EN.** The fine cell is indeed contained in its chosen parent. -/
theorem parentOf_le {D' D : Perspective n} (r : Refines D' D) {c' : Submodule ℂ (H n)}
    (hc' : c' ∈ D'.cells) : c' ≤ parentOf r c' := by
  unfold parentOf
  rw [dif_pos hc']
  exact (r c' hc').choose_spec.2

/--
**FR.** Unicité du parent, **dérivée de `Perspective.unique_parent`** (et de
la non-nullité `D'.nz`) plutôt que reprouvée : tout `c` de la perspective
grossière contenant `c'` doit coïncider avec le parent choisi.

**EN.** Uniqueness of the parent, **derived from `Perspective.unique_parent`**
(and from the nonzero hypothesis `D'.nz`) rather than reproved: any `c` in
the coarse perspective containing `c'` must coincide with the chosen parent.
-/
theorem parentOf_eq_of_le {D' D : Perspective n} (r : Refines D' D) {c' c : Submodule ℂ (H n)}
    (hc' : c' ∈ D'.cells) (hc : c ∈ D.cells) (h : c' ≤ c) : parentOf r c' = c :=
  D.unique_parent (parentOf_mem r hc') hc (D'.nz c' hc') (parentOf_le r hc') h

/-! ## A stabilized presentation of `AxGrain`'s filter -/

/--
**FR.** Instance de décidabilité **nommée et fixée** pour `· ≤ c` sur les
sous-espaces : neutralise le piège classique où une instance `DecidablePred`
différente (mais propositionnellement équivalente) produirait des échecs
d'unification opaques sur un `Finset.filter` par ailleurs identique.

**EN.** A **named and fixed** decidability instance for `· ≤ c` on
subspaces: neutralizes the classic pitfall where a different (but
propositionally equivalent) `DecidablePred` instance would produce opaque
unification failures on an otherwise identical `Finset.filter`.
-/
noncomputable instance leDecidablePred (c : Submodule ℂ (H n)) :
    DecidablePred (· ≤ c : Submodule ℂ (H n) → Prop) :=
  fun c' => Classical.propDecidable (c' ≤ c)

/--
**FR.** Les cellules fines d'un raffinement `D'` contenues dans une cellule
grossière `c` : exactement le `D'.cells.filter (· ≤ c)` de `AxGrain`, sous
l'instance de décidabilité fixée ci-dessus.

**EN.** The fine cells of a refinement `D'` contained in a coarse cell `c`:
exactly `AxGrain`'s `D'.cells.filter (· ≤ c)`, under the fixed decidability
instance above.
-/
noncomputable def coarseCells (D' : Perspective n) (c : Submodule ℂ (H n)) :
    Finset (Submodule ℂ (H n)) :=
  @Finset.filter _ (· ≤ c) (leDecidablePred c) D'.cells

@[simp] theorem mem_coarseCells_iff (D' : Perspective n) (c c' : Submodule ℂ (H n)) :
    c' ∈ coarseCells D' c ↔ c' ∈ D'.cells ∧ c' ≤ c := by
  unfold coarseCells
  rw [Finset.mem_filter]

variable (Est : Perspective n → Submodule ℂ (H n) → ℝ)

/--
**FR.** Reformulation de `AxGrain` via `coarseCells`, pour que l'aval n'ait
jamais à écrire `Finset.filter` à la main. Les deux membres coïncident déjà
définitionnellement (les deux formulations résolvent à la même instance
classique) ; l'énoncé est fourni explicitement car c'est là tout l'intérêt de
cette API de stabilisation.

**EN.** Restatement of `AxGrain` via `coarseCells`, so that downstream code
never needs to write `Finset.filter` by hand. Both sides already coincide
definitionally (both formulations resolve to the same classical instance);
the statement is supplied explicitly because that coincidence is the entire
point of this stabilizing API.
-/
theorem axGrain_iff_coarseCells :
    AxGrain Est ↔ ∀ D' D : Perspective n, Refines D' D → ∀ c ∈ D.cells,
      Est D c = ∑ c' ∈ coarseCells D' c, Est D' c' := by
  unfold AxGrain coarseCells
  constructor
  · intro h D' D hr c hc
    exact h D' D hr c hc
  · intro h D' D hr c hc
    exact h D' D hr c hc

/--
**FR.** **Le pont central** entre la présentation par `≤` de `coarseCells` et
la présentation par fibre de la carte parent : `coarseCells D' c` est
exactement la fibre de `parentOf r` au-dessus de `c`. C'est ce lemme qui
permet à l'aval de définir `pullbackAct r a := a ∘ parentOf r` et de
retomber sur `AxGrain` via `axGrain_iff_coarseCells`.

**EN.** **The central bridge** between the `≤`-presentation of `coarseCells`
and the fiber presentation of the parent map: `coarseCells D' c` is exactly
the fiber of `parentOf r` over `c`. This is the lemma that lets downstream
code define `pullbackAct r a := a ∘ parentOf r` and fall back on `AxGrain`
via `axGrain_iff_coarseCells`.
-/
theorem coarseCells_eq_fiber_parentOf {D' D : Perspective n} (r : Refines D' D)
    {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
    coarseCells D' c = D'.cells.filter (fun c' => parentOf r c' = c) := by
  unfold coarseCells
  apply Finset.filter_congr
  intro c' hc'
  constructor
  · intro hle
    exact parentOf_eq_of_le r hc' hc hle
  · intro heq
    rw [← heq]
    exact parentOf_le r hc'

end

end QuantumFoundations.BornRule
