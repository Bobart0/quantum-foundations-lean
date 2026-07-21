import QuantumFoundations.Branches.TwoObs

/-!
# R3 — Induction générale : tunneling (T), action diagonale (E), théorème de Riedel

**Architecture de preuve (décision ferme, remplace toute tentation d'induction
sur `List.Perm`, INTERDITE ici car la commutation n'est vraie qu'APPLIQUÉE À
`ψ`, pas au niveau opérateurs nu) :**

* **T (tunneling)** : pour toute liste `L` d'indices d'observables toutes
  `≠ a`, sans doublon, substituer le record de `a` (`r` en `r'`) ne change pas
  le résultat de la projection de `a` appliquée APRÈS la chaîne sur `L` —
  chaîne à cinq étapes (éq. (14)) : identité de record cible `b` via IH sur le
  reste, commutation avec le témoin `ĝ`, IH cible `a` sur le reste,
  commutation, IH cible `b` (restauration). Trois appels à l'hypothèse
  d'induction en longueur `k−1`, à des cibles DIFFÉRENTES — d'où la
  ∀-généralisation de la cible `a` (et de ses records `r`, `r'`) dans
  l'énoncé, seule façon de rendre la récurrence forte possible.
* **E (action diagonale)** : la projection, à l'étiquette `k`, du record `c`
  d'une observable déjà présente dans `L`, appliquée à la chaîne, est
  diagonale — `1` si `k` coïncide avec l'étiquette cible `f c` déjà choisie
  dans la chaîne, `0` sinon. Récurrence sur le PRÉFIXE de `L` avant `c` ;
  chaque pas utilise le témoin de la paire `(c, c)` (trivial, couvert par
  `CommuteWitness` avec `r = r'`) puis **T** ; au contact (l'observable `c`
  elle-même), **T** (cible `c`, records `ρ c → k` puis restauration) suivi de
  la contraction opératorielle `Basic.rproj_contract`.

**PUIS** : la somme-à-`ψ` par résolutions itérées, l'invariance d'ordre de
`chainProj`, l'invariance du choix de records, et l'unicité de la
décomposition deviennent des COROLLAIRES D'UNE LIGNE de **E** (appliqué à
`ψ = ∑ g, v_g` — seul le terme `g = f` survit à la projection diagonale).
AUCUNE manipulation de permutations nulle part dans ce fichier.
-/

namespace QuantumFoundations.Branches

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n K R A : ℕ}

/-- **T — Tunneling (éqs. (13)-(14)).** Hypothèses : `L` sans doublon, la
cible `a` n'apparaît pas dans `L`, chaque observable de la famille est
redondamment enregistrée sur `ψ`, et `CommuteWitness` fournit les témoins de
commutation nécessaires. Conclusion : la projection de `a`, à l'étiquette `i`,
appliquée APRÈS la chaîne sur `L`, ne dépend PAS du record `r` choisi pour
`a` — substituer `r` par `r'` laisse le résultat inchangé. La ∀-généralisation
de `a` (et de `r`, `r'`) est ESSENTIELLE : la récurrence forte sur
`L.length` invoque cette même propriété à une cible DIFFÉRENTE sur le
préfixe `L.tail` (trois appels, cibles différentes — voir note d'en-tête). -/
theorem tunneling (Obs : Fin A → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs) :
    ∀ (L : List (Fin A)), L.Nodup → ∀ (ρ : Fin A → Fin R) (f : Fin A → Fin K)
      (a : Fin A), a ∉ L → ∀ (r r' : Fin R) (i : Fin K),
      rproj (Obs a r) i (chainProj Obs L ρ f ψ) = rproj (Obs a r') i (chainProj Obs L ρ f ψ) := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro _ ρ f a _ r r' i; exact hrec a r r' i
  | append_singleton L' b ih =>
    intro hnodup ρ f a ha r r' i
    have hab : a ≠ b := by intro h; apply ha; rw [h]; simp
    have haL' : a ∉ L' := by intro h; apply ha; simp [h]
    have hbL' : b ∉ L' := by
      intro hb
      exact (List.nodup_append.mp hnodup).2.2 b hb b (List.mem_singleton_self b) rfl
    have hL'nodup : L'.Nodup := (List.nodup_append.mp hnodup).1
    show rproj (Obs a r) i (chainProj Obs (L' ++ [b]) ρ f ψ)
        = rproj (Obs a r') i (chainProj Obs (L' ++ [b]) ρ f ψ)
    have hunfold : chainProj Obs (L' ++ [b]) ρ f ψ
        = rproj (Obs b (ρ b)) (f b) (chainProj Obs L' ρ f ψ) :=
      List.foldl_concat _ ψ b L'
    rw [hunfold]
    set X := chainProj Obs L' ρ f ψ with hX
    obtain ⟨ĝ, hcomm⟩ := hcw a b hab r r'
    calc rproj (Obs a r) i (rproj (Obs b (ρ b)) (f b) X)
        = rproj (Obs a r) i (rproj (Obs b ĝ) (f b) X) := by
          rw [ih hL'nodup ρ f b hbL' (ρ b) ĝ (f b)]
      _ = rproj (Obs b ĝ) (f b) (rproj (Obs a r) i X) := commute_apply (hcomm i (f b)).1 X
      _ = rproj (Obs b ĝ) (f b) (rproj (Obs a r') i X) := by
          rw [ih hL'nodup ρ f a haL' r r' i]
      _ = rproj (Obs a r') i (rproj (Obs b ĝ) (f b) X) := (commute_apply (hcomm i (f b)).2 X).symm
      _ = rproj (Obs a r') i (rproj (Obs b (ρ b)) (f b) X) := by
          rw [ih hL'nodup ρ f b hbL' ĝ (ρ b) (f b)]

/-- **E — Action diagonale.** Pour toute observable `c` déjà présente dans la
chaîne `L`, la projection de son record `ρ c`, à l'étiquette `k`, agit comme
`1` si `k` coïncide avec l'étiquette cible `f c` déjà appliquée dans la
chaîne, `0` sinon. Récurrence sur le préfixe de `L` avant `c` ; au contact,
**T** puis contraction opératorielle (`Basic.rproj_contract`). -/
theorem diagonal (Obs : Fin A → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs) :
    ∀ (L : List (Fin A)), L.Nodup → ∀ (ρ : Fin A → Fin R) (f : Fin A → Fin K)
      (c : Fin A), c ∈ L → ∀ (k : Fin K),
      rproj (Obs c (ρ c)) k (chainProj Obs L ρ f ψ)
        = (if k = f c then (1 : ℂ) else 0) • chainProj Obs L ρ f ψ := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro _ ρ f c hc; exact absurd hc List.not_mem_nil
  | append_singleton L' b ih =>
    intro hnodup ρ f c hc k
    have hL'nodup : L'.Nodup := (List.nodup_append.mp hnodup).1
    have hbL' : b ∉ L' := by
      intro hb
      exact (List.nodup_append.mp hnodup).2.2 b hb b (List.mem_singleton_self b) rfl
    have hunfold : chainProj Obs (L' ++ [b]) ρ f ψ
        = rproj (Obs b (ρ b)) (f b) (chainProj Obs L' ρ f ψ) :=
      List.foldl_concat _ ψ b L'
    rw [hunfold]
    set X := chainProj Obs L' ρ f ψ with hX
    rcases List.mem_append.mp hc with hcL' | hcb
    · -- c ∈ L' : tunnel through b's layer, then use ih
      have hcb' : c ≠ b := fun h => hbL' (h ▸ hcL')
      obtain ⟨ĝ, hcomm⟩ := hcw c b hcb' (ρ c) (ρ c)
      calc rproj (Obs c (ρ c)) k (rproj (Obs b (ρ b)) (f b) X)
          = rproj (Obs c (ρ c)) k (rproj (Obs b ĝ) (f b) X) := by
            rw [tunneling Obs ψ hrec hcw L' hL'nodup ρ f b hbL' (ρ b) ĝ (f b)]
        _ = rproj (Obs b ĝ) (f b) (rproj (Obs c (ρ c)) k X) := commute_apply (hcomm k (f b)).1 X
        _ = rproj (Obs b ĝ) (f b) ((if k = f c then (1 : ℂ) else 0) • X) := by
            rw [ih hL'nodup ρ f c hcL' k]
        _ = (if k = f c then (1 : ℂ) else 0) • rproj (Obs b ĝ) (f b) X := map_smul _ _ _
        _ = (if k = f c then (1 : ℂ) else 0) • rproj (Obs b (ρ b)) (f b) X := by
            rw [tunneling Obs ψ hrec hcw L' hL'nodup ρ f b hbL' ĝ (ρ b) (f b)]
    · -- c = b : direct contact
      rw [List.mem_singleton] at hcb
      subst hcb
      exact rproj_contract_apply (Obs c (ρ c)) k (f c) X

/-- **Somme-à-`ψ` par résolutions itérées.** Corollaire d'une ligne de `E`
(résolution de l'identité, `Basic.resolution_apply`, itérée `A` fois via le
split tête/reste `Fin.consEquiv`/`Fintype.sum_prod_type`) — PAS de
manipulation de permutations. -/
theorem jointBranch_sum [NeZero R] (Obs : Fin A → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs) :
    ∑ f : Fin A → Fin K, jointBranch Obs ψ f = ψ := by
  sorry

/-- **Orthogonalité des branches jointes.** Corollaire de `E` appliqué deux
fois (aux deux branches `f ≠ f'`, sur l'étiquette où elles diffèrent) et de
la contraction opératorielle. -/
theorem jointBranch_orthogonal [NeZero R] (Obs : Fin A → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs)
    {f f' : Fin A → Fin K} (hff : f ≠ f') :
    ⟪jointBranch Obs ψ f, jointBranch Obs ψ f'⟫_ℂ = 0 := by
  sorry

/-- **Théorème de Riedel (Main Result, PRL 118, 120402 (2017)).** Sous
redondance (`IsRecordedOn` de chaque observable) et témoin de commutation
(`CommuteWitness`, issu en pratique de la disjonction spatiale des supports —
`Local.commute_of_disjoint`), `ψ` se décompose de façon UNIQUE en branches
jointes orthogonales, chacune état propre SIMULTANÉ de tous les records de
toutes les observables. **Contrepoint POSITIF de
`Histories.contrary_inferences`** : la cohérence seule (Kent) autorise les
inférences contraires ; les records redondants (Riedel) forcent au contraire
l'unicité de la décomposition — deux mécanismes structurellement distincts
gouvernant la même notion d'« histoire »/« branche ».

L'invariance de `chainProj`/`jointBranch` par rapport à l'ordre de la liste
`L` et au choix des records `ρ` (au-delà du corollaire `branch_wellDefined`)
n'est PAS énoncée séparément ici : une fois ce théorème et `diagonal` clos,
elle s'obtient en une ligne (deux branches jointes construites par des
`chainProj` différant seulement par l'ordre/le choix de records satisfont
toutes deux la propriété d'état propre ci-dessous pour le MÊME `f`, donc
coïncident par le volet unicité) — à ajouter comme corollaire sans but
ouvert supplémentaire une fois ce jalon fermé, pas comme but ouvert séparé
du squelette. -/
theorem riedel [NeZero R] (Obs : Fin A → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs) :
    (∑ f : Fin A → Fin K, jointBranch Obs ψ f = ψ) ∧
    (∀ f f' : Fin A → Fin K, f ≠ f' → ⟪jointBranch Obs ψ f, jointBranch Obs ψ f'⟫_ℂ = 0) ∧
    (∀ (f : Fin A → Fin K) (a : Fin A) (r : Fin R) (k : Fin K),
      rproj (Obs a r) k (jointBranch Obs ψ f)
        = (if k = f a then (1 : ℂ) else 0) • jointBranch Obs ψ f) ∧
    (∀ w : (Fin A → Fin K) → H n, (∑ f : Fin A → Fin K, w f = ψ) →
      (∀ (f : Fin A → Fin K) (a : Fin A) (r : Fin R) (k : Fin K),
        rproj (Obs a r) k (w f) = (if k = f a then (1 : ℂ) else 0) • w f) →
      ∀ f : Fin A → Fin K, w f = jointBranch Obs ψ f) := by
  sorry

end
end QuantumFoundations.Branches
