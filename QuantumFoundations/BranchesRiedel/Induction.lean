import QuantumFoundations.BranchesRiedel.TwoObs

/-!
**FR.** # R3 — Induction générale : tunneling (T), action diagonale (E), théorème de Riedel

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

**EN.** # R3 — General induction: tunneling (T), diagonal action (E), and Riedel's theorem

Proof architecture (fixed decision, replacing any attempt to induct on
List.Perm, which is FORBIDDEN here because commutation holds only AFTER
APPLICATION TO ψ, not at the level of bare operators):

* T (tunneling): for every list L of observable indices all
 ≠ a, with no duplicates, replacing the record of a (r by r') does not
 change the result of applying the projection of a AFTER the chain on L.
 The five-step chain (Eq. (14)) is: target-record identity for b via the IH
 on the remainder, commutation with witness ĝ, IH with target a on the
 remainder, commutation, and IH with target b (restoration). This requires
 three applications of the induction hypothesis at length k−1, with
 DIFFERENT targets—hence the ∀-generalization over the target a
 (and its records r, r') in the statement, which is the only way to make
 strong induction possible.
* E (diagonal action): for an observable c already present in L, the
 projection at label k of its record, applied to the chain, acts
 diagonally—1 if k agrees with the target label f c already selected
 in the chain, and 0 otherwise. The proof proceeds by induction on the
 PREFIX of L preceding c; each step uses the witness for the pair
 (c, c) (the trivial case covered by CommuteWitness with r = r') and
 then T. At the point of contact (the observable c itself), it uses
 T (target c, replacing records ρ c → k and then restoring them),
 followed by the operator contraction Basic.rproj_contract.

THEN: summation to ψ by iterated resolutions, order invariance of
chainProj, invariance under the choice of records, and uniqueness of the
decomposition become ONE-LINE COROLLARIES of E (applied to
ψ = ∑ g, v_g: only the term g = f survives the diagonal projection).
There is NO permutation manipulation anywhere in this file.
-/

namespace QuantumFoundations.BranchesRiedel

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n K R A : ℕ}

/--
**FR.** **T — Tunneling (éqs. (13)-(14)).** Hypothèses : `L` sans doublon, la
cible `a` n'apparaît pas dans `L`, chaque observable de la famille est
redondamment enregistrée sur `ψ`, et `CommuteWitness` fournit les témoins de
commutation nécessaires. Conclusion : la projection de `a`, à l'étiquette `i`,
appliquée APRÈS la chaîne sur `L`, ne dépend PAS du record `r` choisi pour
`a` — substituer `r` par `r'` laisse le résultat inchangé. La ∀-généralisation
de `a` (et de `r`, `r'`) est ESSENTIELLE : la récurrence forte sur
`L.length` invoque cette même propriété à une cible DIFFÉRENTE sur le
préfixe `L.tail` (trois appels, cibles différentes — voir note d'en-tête).

**EN.** T — Tunneling (Eqs. (13)–(14)). Hypotheses: L has no duplicates,
the target a does not occur in L, each observable in the family is
redundantly recorded on ψ, and CommuteWitness supplies the required
commutation witnesses. Conclusion: the projection of a at label i,
applied AFTER the chain on L, does NOT depend on the record r chosen for
a; replacing r by r' leaves the result unchanged. The ∀-generalization over a (and over r, r') is ESSENTIAL: strong induction
on L.length invokes the same property with a DIFFERENT target on the prefix
L.tail (three invocations with different targets; see the header note).
-/
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

/--
**FR.** **E — Action diagonale.** Pour toute observable `c` déjà présente dans la
chaîne `L`, la projection de son record `ρ c`, à l'étiquette `k`, agit comme
`1` si `k` coïncide avec l'étiquette cible `f c` déjà appliquée dans la
chaîne, `0` sinon. Récurrence sur le préfixe de `L` avant `c` ; au contact,
**T** puis contraction opératorielle (`Basic.rproj_contract`).

**EN.** E — Diagonal action. For every observable c already present in the
chain L, the projection of its record ρ c at label k acts as 1 when
k coincides with the target label f c already applied in the chain, and
as 0 otherwise. The proof proceeds by induction on the prefix of L
preceding c; at the point of contact, it uses T followed by operator
contraction (Basic.rproj_contract).
-/
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

/--
**FR.** `chainProj` ne dépend de `f` que via sa restriction à `L` — direct par
récurrence structurelle sur `L` (le fold ne lit `f a` que pour `a ∈ L`).

**EN.** chainProj depends on f only through its restriction to L—this
follows directly by structural induction on L (the fold reads f a only
for a ∈ L).
-/
private theorem foldl_congr {α β : Type*} (L : List α) (F G : α → β → β) (init : β)
    (h : ∀ a ∈ L, F a = G a) :
    L.foldl (fun acc a => F a acc) init = L.foldl (fun acc a => G a acc) init := by
  induction L generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [h hd List.mem_cons_self]
    exact ih (G hd init) (fun a ha => h a (List.mem_cons_of_mem hd ha))

private theorem chainProj_indep_outside (Obs : Fin A → Fin R → LabeledResolution n K) (ψ : H n)
    (L : List (Fin A)) (ρ : Fin A → Fin R) (f g : Fin A → Fin K) (h : ∀ a ∈ L, f a = g a) :
    chainProj Obs L ρ f ψ = chainProj Obs L ρ g ψ := by
  show L.foldl (fun acc a => rproj (Obs a (ρ a)) (f a) acc) ψ
      = L.foldl (fun acc a => rproj (Obs a (ρ a)) (g a) acc) ψ
  exact foldl_congr L _ _ ψ (fun a ha => by rw [h a ha])

/--
**FR.** **Relation à un pas, sans division** (spécification exacte de l'utilisateur) :
`K • (∑ f, chainProj (L++[a])) = ∑ f, chainProj L`. Preuve : `Equiv.piSplitAt a`
scinde la somme sur `f : Fin A → Fin K` en `(v : Fin K) × (f' : {j // j ≠ a} →
Fin K)` ; côté gauche, `resolution_apply` élimine directement la somme sur `v`
(la partie `chainProj Obs L ρ (…, f')` ne dépend PAS de `v` car `a ∉ L`,
`chainProj_indep_outside`) ; côté droit, la même scission donne `K` copies
identiques du même terme. Cas `K = 0` trivial (domaine `Fin A → Fin K` vide
dès que `A ≥ 1`, ce qui est le cas puisque `a : Fin A` existe).

**EN.** One-step relation, without division (the user's exact specification):
K • (∑ f, chainProj (L++[a])) = ∑ f, chainProj L. Proof:
Equiv.piSplitAt a splits the sum over f : Fin A → Fin K into
(v : Fin K) × (f' : {j // j ≠ a} →
Fin K). On the left-hand side,
resolution_apply directly eliminates the sum over v (the component
chainProj Obs L ρ (…, f') does NOT depend on v, because a ∉ L, by
chainProj_indep_outside); on the right-hand side, the same splitting yields
K identical copies of the same term. The case K = 0 is trivial (the
domain Fin A → Fin K is empty as soon as A ≥ 1, which holds because
a : Fin A exists).
-/
private theorem chainProj_onestep (Obs : Fin A → Fin R → LabeledResolution n K) (ψ : H n)
    (L : List (Fin A)) (ρ : Fin A → Fin R) (a : Fin A) (ha : a ∉ L) :
    (K : ℂ) • (∑ f : Fin A → Fin K, chainProj Obs (L ++ [a]) ρ f ψ)
      = ∑ f : Fin A → Fin K, chainProj Obs L ρ f ψ := by
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · subst hK0
    have : IsEmpty (Fin A → Fin 0) := by
      have : Nonempty (Fin A) := ⟨a⟩
      infer_instance
    rw [Fintype.sum_empty, Fintype.sum_empty, smul_zero]
  · set v0 : Fin K := ⟨0, hKpos⟩
    set e := Equiv.piSplitAt a (fun _ : Fin A => Fin K) with he
    have hZ : ∀ (v v' : Fin K) (f' : {j : Fin A // j ≠ a} → Fin K),
        chainProj Obs L ρ (e.symm (v, f')) ψ = chainProj Obs L ρ (e.symm (v', f')) ψ := by
      intro v v' f'
      apply chainProj_indep_outside
      intro x hx
      have hxa : x ≠ a := fun h => ha (h ▸ hx)
      show e.symm (v, f') x = e.symm (v', f') x
      simp [he, Equiv.piSplitAt, hxa]
    have hLHS : ∑ f : Fin A → Fin K, chainProj Obs (L ++ [a]) ρ f ψ
        = ∑ f' : {j : Fin A // j ≠ a} → Fin K, chainProj Obs L ρ (e.symm (v0, f')) ψ := by
      have step1 : ∑ f : Fin A → Fin K, chainProj Obs (L ++ [a]) ρ f ψ
          = ∑ v : Fin K, ∑ f' : {j : Fin A // j ≠ a} → Fin K,
              chainProj Obs (L ++ [a]) ρ (e.symm (v, f')) ψ := by
        have hcomp := Equiv.sum_comp e.symm (fun f => chainProj Obs (L ++ [a]) ρ f ψ)
        rw [← hcomp, Fintype.sum_prod_type]
      rw [step1]
      have step2 : ∀ v : Fin K, ∀ f' : {j : Fin A // j ≠ a} → Fin K,
          chainProj Obs (L ++ [a]) ρ (e.symm (v, f')) ψ
            = rproj (Obs a (ρ a)) v (chainProj Obs L ρ (e.symm (v, f')) ψ) := by
        intro v f'
        have hav : e.symm (v, f') a = v := by simp [he, Equiv.piSplitAt]
        rw [show chainProj Obs (L ++ [a]) ρ (e.symm (v, f')) ψ
            = rproj (Obs a (ρ a)) (e.symm (v,f') a) (chainProj Obs L ρ (e.symm (v, f')) ψ) from
            List.foldl_concat _ ψ a L, hav]
      simp_rw [step2]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro f' _
      rw [Finset.sum_congr rfl (fun v (_ : v ∈ (Finset.univ : Finset (Fin K))) => by
        rw [hZ v v0] : ∀ v ∈ (Finset.univ : Finset (Fin K)),
          rproj (Obs a (ρ a)) v (chainProj Obs L ρ (e.symm (v, f')) ψ)
            = rproj (Obs a (ρ a)) v (chainProj Obs L ρ (e.symm (v0, f')) ψ))]
      exact resolution_apply (Obs a (ρ a)) (chainProj Obs L ρ (e.symm (v0, f')) ψ)
    have hRHS : ∑ f : Fin A → Fin K, chainProj Obs L ρ f ψ
        = (K : ℂ) • ∑ f' : {j : Fin A // j ≠ a} → Fin K, chainProj Obs L ρ (e.symm (v0, f')) ψ := by
      have step1 : ∑ f : Fin A → Fin K, chainProj Obs L ρ f ψ
          = ∑ v : Fin K, ∑ f' : {j : Fin A // j ≠ a} → Fin K,
              chainProj Obs L ρ (e.symm (v, f')) ψ := by
        have hcomp := Equiv.sum_comp e.symm (fun f => chainProj Obs L ρ f ψ)
        rw [← hcomp, Fintype.sum_prod_type]
      rw [step1]
      rw [Finset.sum_congr rfl (fun v (_ : v ∈ (Finset.univ : Finset (Fin K))) =>
        Finset.sum_congr rfl (fun f' _ => hZ v v0 f'))]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
    rw [hLHS, hRHS]

/--
**FR.** Chaîne la relation à un pas sur toute la longueur de `L`, sans jamais
diviser : `K^(L.length) • (∑ f, chainProj L) = K^A • ψ`.

**EN.** Iterates the one-step relation over the entire length of L, without
ever dividing: K^(L.length) • (∑ f, chainProj L) = K^A • ψ.
-/
private theorem sum_pow_relation (Obs : Fin A → Fin R → LabeledResolution n K) (ψ : H n) :
    ∀ (L : List (Fin A)), L.Nodup → ∀ (ρ : Fin A → Fin R),
      (K : ℂ) ^ L.length • (∑ f : Fin A → Fin K, chainProj Obs L ρ f ψ)
        = (K : ℂ) ^ A • ψ := by
  intro L
  induction L using List.reverseRecOn with
  | nil =>
    intro _ ρ
    simp only [List.length_nil, pow_zero, one_smul]
    have hval : ∑ f : Fin A → Fin K, chainProj Obs ([] : List (Fin A)) ρ f ψ
        = ∑ _f : Fin A → Fin K, ψ := rfl
    rw [hval, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_pow]
  | append_singleton L' b ih =>
    intro hnodup ρ
    have hL'nodup : L'.Nodup := (List.nodup_append.mp hnodup).1
    have hbL' : b ∉ L' := by
      intro hb
      exact (List.nodup_append.mp hnodup).2.2 b hb b (List.mem_singleton_self b) rfl
    have honestep := chainProj_onestep Obs ψ L' ρ b hbL'
    have hlen : (L' ++ [b]).length = L'.length + 1 := by simp
    rw [hlen, pow_succ, mul_smul, honestep]
    exact ih hL'nodup ρ

/--
**FR.** **Somme-à-`ψ` par résolutions itérées.** ÉCART vs le squelette R0 : ni
`IsRecordedOn` ni `CommuteWitness` ne sont nécessaires — c'est un fait de
résolution de l'identité PUR (`sum_pow_relation` + annulation de `K^A`),
indépendant de la redondance ou de la commutation. Hypothèses superflues
retirées de la signature (découvert en écrivant la preuve, comme
`BornRule.hker_derivation` en son temps). `[NeZero K]` est nécessaire UNE
SEULE FOIS, ici, pour l'annulation finale de `K^A` — cas dégénéré `K = 0`
sans usage réel dans le projet, coût minimal, non filé dans `Defs.lean`.

**EN.** Summation to ψ by iterated resolutions. Deviation from the R0
skeleton: neither IsRecordedOn nor CommuteWitness is needed, since this is
a resolution-of-the-identity fact in its own right (sum_pow_relation +
cancellation of K^A), independent of redundancy or commutation. Superfluous
hypotheses were removed from the signature (a fact discovered while writing
the proof, as previously occurred with BornRule.hker_derivation). [NeZero K]
is needed exactly once, here, for the final cancellation of K^A; the
degenerate case K = 0 has no genuine use in the project, so this is a
minimal cost and the assumption is not threaded through Defs.lean.
-/
theorem jointBranch_sum [NeZero R] [NeZero K] (Obs : Fin A → Fin R → LabeledResolution n K)
    (ψ : H n) : ∑ f : Fin A → Fin K, jointBranch Obs ψ f = ψ := by
  have hrel := sum_pow_relation Obs ψ (List.finRange A) (List.nodup_finRange A) 0
  rw [List.length_finRange] at hrel
  have hcast : ∀ f, chainProj Obs (List.finRange A) 0 f ψ = jointBranch Obs ψ f := fun f => rfl
  simp_rw [hcast] at hrel
  have hKA : ((K : ℂ) ^ A) ≠ 0 := pow_ne_zero A (Nat.cast_ne_zero.mpr (NeZero.ne K))
  exact smul_right_injective (H n) hKA hrel

/--
**FR.** **Orthogonalité des branches jointes.** Corollaire de `E` appliqué deux
fois (aux deux branches `f ≠ f'`, sur l'étiquette où elles diffèrent) et de
la contraction opératorielle.

**EN.** Orthogonality of joint branches. A corollary of applying E twice
(to the two branches f ≠ f', at a label on which they differ) together
with operator contraction.
-/
theorem jointBranch_orthogonal [NeZero R] (Obs : Fin A → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs)
    {f f' : Fin A → Fin K} (hff : f ≠ f') :
    ⟪jointBranch Obs ψ f, jointBranch Obs ψ f'⟫_ℂ = 0 := by
  obtain ⟨a₀, ha₀⟩ := Function.ne_iff.mp hff
  have hE1 := diagonal Obs ψ hrec hcw (List.finRange A) (List.nodup_finRange A) 0 f a₀
    (List.mem_finRange a₀) (f' a₀)
  rw [if_neg (Ne.symm ha₀), zero_smul] at hE1
  have hE2 := diagonal Obs ψ hrec hcw (List.finRange A) (List.nodup_finRange A) 0 f' a₀
    (List.mem_finRange a₀) (f' a₀)
  rw [if_pos rfl, one_smul] at hE2
  set Λ := Obs a₀ ((0 : Fin A → Fin R) a₀)
  have hmem2 : jointBranch Obs ψ f' ∈ Λ.cells (f' a₀) := by
    show chainProj Obs (List.finRange A) 0 f' ψ ∈ Λ.cells (f' a₀)
    rw [← hE2]; exact Submodule.starProjection_apply_mem _ _
  have hzero1 : jointBranch Obs ψ f ∈ (Λ.cells (f' a₀))ᗮ := by
    show chainProj Obs (List.finRange A) 0 f ψ ∈ (Λ.cells (f' a₀))ᗮ
    exact (Submodule.starProjection_apply_eq_zero_iff (Λ.cells (f' a₀))).mp hE1
  have hswapped := (Submodule.mem_orthogonal (Λ.cells (f' a₀)) _).mp hzero1 _ hmem2
  rw [← inner_conj_symm (jointBranch Obs ψ f) (jointBranch Obs ψ f'), hswapped]
  simp

/--
**FR.** Pour tout `w` satisfaisant la propriété d'état propre de `heig`,
`chainProj Obs L 0 f (w g)` isole `w g` si `f` et `g` coïncident sur `L`,
et l'annule sinon — récurrence structurelle simple sur `L` (PAS
`List.reverseRecOn` : un seul pas de `List.foldl`, pas besoin de tunneling
ici puisque `heig` porte directement sur `w`, pas sur une chaîne à
reconstruire). Ingrédient clé de l'unicité.

**EN.** For every w satisfying the eigenstate property heig,
chainProj Obs L 0 f (w g) isolates w g when f and g agree on L,
and annihilates it otherwise—a straightforward structural induction on L
(NOT List.reverseRecOn: only one step of List.foldl is involved, and no
tunneling is needed because heig applies directly to w, not to a chain
that must be reconstructed). This is the key ingredient for uniqueness.
-/
private theorem chainProj_apply_w [NeZero R] (Obs : Fin A → Fin R → LabeledResolution n K)
    (w : (Fin A → Fin K) → H n)
    (heig : ∀ (f : Fin A → Fin K) (a : Fin A) (k : Fin K),
      rproj (Obs a 0) k (w f) = (if k = f a then (1 : ℂ) else 0) • w f) :
    ∀ (L : List (Fin A)) (f g : Fin A → Fin K),
      chainProj Obs L 0 f (w g) = (if ∀ a ∈ L, f a = g a then w g else 0) := by
  intro L
  induction L with
  | nil => intro f g; simp [chainProj]
  | cons hd tl ih =>
    intro f g
    show chainProj Obs tl 0 f (rproj (Obs hd 0) (f hd) (w g)) = _
    rw [heig g hd (f hd)]
    by_cases hfg : f hd = g hd
    · rw [if_pos hfg, one_smul, ih f g]
      have hcond : (∀ a ∈ hd :: tl, f a = g a) ↔ (∀ a ∈ tl, f a = g a) := by
        constructor
        · intro h a ha; exact h a (List.mem_cons_of_mem hd ha)
        · intro h a ha
          rcases List.mem_cons.mp ha with rfl | ha'
          · exact hfg
          · exact h a ha'
      simp only [hcond]
    · rw [if_neg hfg, zero_smul]
      have hcondfalse : ¬ (∀ a ∈ hd :: tl, f a = g a) := fun h => hfg (h hd List.mem_cons_self)
      rw [if_neg hcondfalse]
      have hzero : ∀ (L' : List (Fin A)) (x : H n), x = 0 → chainProj Obs L' 0 f x = 0 := by
        intro L' x hx
        subst hx
        induction L' with
        | nil => simp [chainProj]
        | cons hd' tl' ih' =>
          show chainProj Obs tl' 0 f (rproj (Obs hd' 0) (f hd') 0) = 0
          rw [map_zero]
          exact ih'
      exact hzero tl 0 rfl

/--
**FR.** `chainProj` distribue sur les sommes finies — récurrence structurelle
directe (chaque étape est un `LinearMap`, `map_sum`).

**EN.** chainProj distributes over finite sums—a direct structural induction
(each stage is a LinearMap, using map_sum).
-/
private theorem chainProj_sum {ι : Type*} (s : Finset ι)
    (Obs : Fin A → Fin R → LabeledResolution n K)
    (L : List (Fin A)) (ρ : Fin A → Fin R) (f : Fin A → Fin K) (v : ι → H n) :
    chainProj Obs L ρ f (∑ i ∈ s, v i) = ∑ i ∈ s, chainProj Obs L ρ f (v i) := by
  show L.foldl (fun acc a => rproj (Obs a (ρ a)) (f a) acc) (∑ i ∈ s, v i)
      = ∑ i ∈ s, L.foldl (fun acc a => rproj (Obs a (ρ a)) (f a) acc) (v i)
  induction L generalizing s v with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [show (rproj (Obs hd (ρ hd)) (f hd)) (∑ i ∈ s, v i)
        = ∑ i ∈ s, rproj (Obs hd (ρ hd)) (f hd) (v i) from map_sum _ _ _]
    exact ih s (fun i => rproj (Obs hd (ρ hd)) (f hd) (v i))

/--
**FR.** **Théorème de Riedel (Main Result, PRL 118, 120402 (2017)).** Sous
redondance (`IsRecordedOn` de chaque observable) et témoin de commutation
(`CommuteWitness`, issu en pratique de la disjonction spatiale des supports —
`Local.commute_of_disjoint`), `ψ` se décompose de façon UNIQUE en branches
jointes orthogonales, chacune état propre SIMULTANÉ de tous les records de
toutes les observables. **Contrepoint POSITIF de
`HistoriesKent.contrary_inferences`** : la cohérence seule (Kent) autorise les
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
du squelette.

## Écart vs le squelette R0 : état propre et unicité restreints au record `0`

Testé explicitement avant de choisir : l'invariance par choix de record
arbitraire `r` (au lieu du seul `0` utilisé par `chainProj`/`jointBranch`)
n'est PAS immédiate depuis `E`/`T` seuls — `T` ne s'applique qu'à une
observable ABSENTE de la liste, et ici l'observable cible `a` est déjà
présente dans `List.finRange A` ; substituer son propre record demanderait
de composer deux projections de records DIFFÉRENTS de la MÊME observable en
un point de contact interne à la chaîne, ce que `rproj_contract` ne couvre
pas (il ne couvre que deux étiquettes du MÊME record). Restreint au record
`0`, comme `TwoObs.twoObs_eigen`. La version forte (`∀ r`) est une extension
séparée, à tenter une fois l'invariance de choix de record établie pour
elle-même — non bloquante ici.

**EN.** Riedel's theorem (Main Result, PRL 118, 120402 (2017)). Under
redundancy (IsRecordedOn for each observable) and the commutation-witness
hypothesis (CommuteWitness, arising in practice from spatial disjointness
of the supports through Local.commute_of_disjoint), ψ admits a UNIQUE
decomposition into orthogonal joint branches, each of which is a
SIMULTANEOUS eigenstate of every record of every observable. The POSITIVE
counterpart of HistoriesKent.contrary_inferences: consistency alone (Kent)
permits contrary inferences, whereas redundant records (Riedel) enforce
uniqueness of the decomposition—two structurally distinct mechanisms
governing the same notion of “history”/“branch.”

Invariance of chainProj/jointBranch under the ordering of the list L and
under the choice of records ρ (beyond the corollary
branch_wellDefined) is NOT stated separately here: once this theorem and
diagonal are established, it follows in one line (two joint branches built
from chainProj expressions differing only in ordering or record choice
both satisfy the eigenstate property below for the SAME f, and hence agree
by uniqueness). It should be added as a corollary once this milestone is
closed, without introducing an additional open goal, rather than as a
separate open goal in the skeleton.

## Deviation from the R0 skeleton: eigenstate property and uniqueness restricted to record 0

This choice was tested explicitly beforehand: invariance under an arbitrary
record choice r (rather than only 0, as used by
chainProj/jointBranch) does NOT follow immediately from E/T alone.
T applies only to an observable ABSENT from the list, whereas the target
observable a is already present in List.finRange A; replacing its own
record would require composing two projections from DIFFERENT records of the
SAME observable at an internal point of contact in the chain, which
rproj_contract does not cover (it covers only two labels of the SAME
record). The statement is therefore restricted to record 0, as in
TwoObs.twoObs_eigen. The stronger version (∀ r) is a separate extension
to be attempted once invariance under record choice has itself been proved;
it is not blocking here.
-/
theorem riedel [NeZero R] [NeZero K] (Obs : Fin A → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs) :
    (∑ f : Fin A → Fin K, jointBranch Obs ψ f = ψ) ∧
    (∀ f f' : Fin A → Fin K, f ≠ f' → ⟪jointBranch Obs ψ f, jointBranch Obs ψ f'⟫_ℂ = 0) ∧
    (∀ (f : Fin A → Fin K) (k : Fin K) (a : Fin A),
      rproj (Obs a 0) k (jointBranch Obs ψ f)
        = (if k = f a then (1 : ℂ) else 0) • jointBranch Obs ψ f) ∧
    (∀ w : (Fin A → Fin K) → H n, (∑ f : Fin A → Fin K, w f = ψ) →
      (∀ (f : Fin A → Fin K) (a : Fin A) (k : Fin K),
        rproj (Obs a 0) k (w f) = (if k = f a then (1 : ℂ) else 0) • w f) →
      ∀ f : Fin A → Fin K, w f = jointBranch Obs ψ f) := by
  refine ⟨jointBranch_sum Obs ψ, fun f f' => jointBranch_orthogonal Obs ψ hrec hcw, ?_, ?_⟩
  · intro f k a
    exact diagonal Obs ψ hrec hcw (List.finRange A) (List.nodup_finRange A) 0 f a
      (List.mem_finRange a) k
  · intro w hsum heig f
    have hkey := chainProj_apply_w Obs w heig (List.finRange A) f f
    have hcond : ∀ a ∈ List.finRange A, f a = f a := fun a _ => rfl
    rw [if_pos hcond] at hkey
    have hlin : chainProj Obs (List.finRange A) 0 f (∑ g : Fin A → Fin K, w g) = w f := by
      rw [chainProj_sum]
      have hcongr : ∀ g : Fin A → Fin K,
          chainProj Obs (List.finRange A) 0 f (w g) = (if g = f then w g else 0) := by
        intro g
        rw [chainProj_apply_w Obs w heig (List.finRange A) f g]
        have hiff : (∀ a ∈ List.finRange A, f a = g a) ↔ g = f := by
          constructor
          · intro h; funext a; exact (h a (List.mem_finRange a)).symm
          · intro h a _; rw [h]
        simp only [hiff]
      simp_rw [hcongr]
      exact (Finset.sum_ite_eq' (Finset.univ : Finset (Fin A → Fin K)) f w).trans (by simp)
    rw [hsum] at hlin
    exact hlin.symm

end
end QuantumFoundations.BranchesRiedel
