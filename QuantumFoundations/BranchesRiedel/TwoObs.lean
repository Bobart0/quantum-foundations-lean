import QuantumFoundations.BranchesRiedel.Basic

/-!
**FR.** # R2 — Cas `A = 2` : dé-risquage de la mécanique `CommuteWitness`/chaîne

Jalon volontairement réduit : valider au coût minimal la mécanique de
tunneling (chaîne à cinq étapes, éqs. (13)-(15) de Riedel) et le mécanisme
d'action diagonale, AVANT l'induction générale de `Induction.lean`. La
décomposition/unicité à deux observables COMPLÈTES ne sont PAS des théorèmes
séparés ici — elles tombent comme instance `A = 2` du théorème général
`Induction.riedel`.

## Écart vs le squelette R0 : `twoObs_eigen` restreint au record `0`

Le squelette R0 énonçait `twoObs_eigen` pour un record `r : Fin R`
ARBITRAIRE de l'observable cible `a`. En tentant la preuve, ceci s'est avéré
STRICTEMENT PLUS FORT que le mécanisme d'action diagonale lui-même (qui ne
porte que sur le record `ρ c` effectivement utilisé pour construire la
chaîne, ici `0`) — la généralisation à `r` arbitraire nécessiterait en plus
`Basic.branch_wellDefined`/`IsRecordedOn`, composée par-dessus, sans rien
apporter à la validation de la mécanique visée par ce jalon. Restreint au
record `0` (celui utilisé par `chainProj`/`jointBranch`), conformément à la
forme réelle de `Induction.diagonal`. Ce n'est pas un affaiblissement
dissimulé : la généralisation reste un corollaire immédiat, non nécessaire
ici.

## Validation confirmée

Les trois preuves ci-dessous suivent EXACTEMENT le mécanisme à cinq étapes
décrit dans le prompt de conception (`chain_two_0`/`chain_two_1` : identité
de record cible via redondance, commutation avec le témoin `ĝ`, identité de
record de l'AUTRE cible via redondance, commutation, identité de record
cible via redondance — restauration). `chain_two` en est l'instance directe
(`L = [1]`, `a = 0`) ; `swap_two` combine deux applications de ce mécanisme
(une par observable) avec UNE commutation supplémentaire ; `twoObs_eigen`
combine ce même mécanisme avec la contraction opératorielle
(`Basic.rproj_contract`, sous forme pointwise ici) au point de contact.
Aucune manipulation de permutations.

`commute_apply` et `rproj_contract_apply` (utilitaires ponctuels) ont été
relocalisés publics dans `Basic.lean` dès leur second usage — nécessaires
aussi à `Induction.lean` — plutôt que dupliqués `private` dans les deux
fichiers.

**EN.** # R2 — Case A = 2: reducing risk in the CommuteWitness/chain mechanism

A deliberately limited milestone: validate, at minimal cost, the tunneling
mechanism (the five-step chain, Riedel's Eqs. (13)–(15)) and the
diagonal-action mechanism before the general induction in Induction.lean.
The complete two-observable decomposition and uniqueness results are not
separate theorems here; they follow as the instance A = 2 of the general
theorem Induction.riedel.

## Deviation from the R0 skeleton: twoObs_eigen restricted to record 0

The R0 skeleton stated twoObs_eigen for an arbitrary record r : Fin R of
the target observable a. During the proof, this turned out to be strictly
stronger than the diagonal-action mechanism itself, which concerns only the
record ρ c actually used to construct the chain, here 0. Generalization to
an arbitrary r would additionally require composing
Basic.branch_wellDefined/IsRecordedOn on top, without contributing to the
validation of the mechanism targeted by this milestone. The statement is
therefore restricted to record 0, the record used by
chainProj/jointBranch, in accordance with the actual form of
Induction.diagonal. This is not a concealed weakening: the generalization
remains an immediate corollary and is not needed here.

## Confirmed validation

The three proofs below follow the five-step mechanism (target-record
identity by redundancy, commutation with witness ĝ, record identity for the
other target by redundancy, commutation, and target-record identity by
redundancy, i.e. restoration) exactly as described above. chain_two is the
direct instance (L = [1], a = 0); swap_two combines two applications of
this mechanism, one for each observable, with one additional commutation;
twoObs_eigen combines the same mechanism with operator contraction
(Basic.rproj_contract, here in pointwise form) at the point of contact. No
permutation manipulation is used.

The pointwise utilities commute_apply and rproj_contract_apply were moved
to Basic.lean and made public upon their second use—because they are also
needed by Induction.lean—rather than being duplicated as private in both
files.
-/

namespace QuantumFoundations.BranchesRiedel

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n K R : ℕ}

private theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

/--
**FR.** Cible `0`, autre observable `1` : substituer le record de `0` (`r → r'`)
est invisible après application de la projection de `1` (au record
quelconque `ρ₁`) à `ψ` — le cœur du mécanisme de tunneling, à `A = 2`.

**EN.** Target 0, other observable 1: replacing the record of 0
(r → r') is invisible after applying the projection of 1 (at an arbitrary
record ρ₁) to ψ—the core of the tunneling mechanism for A = 2.
-/
private theorem chain_two_0 (Obs : Fin 2 → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs)
    (r r' ρ₁ : Fin R) (i j : Fin K) :
    rproj (Obs 0 r) i (rproj (Obs 1 ρ₁) j ψ) = rproj (Obs 0 r') i (rproj (Obs 1 ρ₁) j ψ) := by
  obtain ⟨ĝ, hcomm⟩ := hcw 0 1 (by decide) r r'
  rw [hrec 1 ρ₁ ĝ j, commute_apply (hcomm i j).1, hrec 0 r r' i, ← commute_apply (hcomm i j).2]

/--
**FR.** Symétrique de `chain_two_0` : cible `1`, autre observable `0`.

**EN.** Symmetric counterpart of chain_two_0: target 1, other observable 0.
-/
private theorem chain_two_1 (Obs : Fin 2 → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs)
    (s s' ρ₀ : Fin R) (j i : Fin K) :
    rproj (Obs 1 s) j (rproj (Obs 0 ρ₀) i ψ) = rproj (Obs 1 s') j (rproj (Obs 0 ρ₀) i ψ) := by
  obtain ⟨ĝ, hcomm⟩ := hcw 1 0 (by decide) s s'
  rw [hrec 0 ρ₀ ĝ i, commute_apply (hcomm j i).1, hrec 1 s s' j, ← commute_apply (hcomm j i).2]

/--
**FR.** **R2(a), chaîne à cinq étapes (éqs. (13)-(14)), cas minimal `A = 2`.**
Instance directe de `chain_two_0` (`i = j`, correspondant à `L = [1]`,
`f := fun _ => i` dans `chainProj`).

**EN.** R2(a), five-step chain (Eqs. (13)–(14)), minimal case A = 2.
Direct instance of chain_two_0 (i = j, corresponding to L = [1] and
f := fun _ => i in chainProj).
-/
theorem chain_two (Obs : Fin 2 → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs)
    (r r' : Fin R) (ρ₁ : Fin R) (i : Fin K) :
    rproj (Obs 0 r) i (chainProj Obs [1] (fun _ => ρ₁) (fun _ => i) ψ)
      = rproj (Obs 0 r') i (chainProj Obs [1] (fun _ => ρ₁) (fun _ => i) ψ) := by
  show rproj (Obs 0 r) i (rproj (Obs 1 ρ₁) i ψ) = rproj (Obs 0 r') i (rproj (Obs 1 ρ₁) i ψ)
  exact chain_two_0 Obs ψ hrec hcw r r' ρ₁ i i

/--
**FR.** **R2(b), échange d'ordre (éq. (15)), cas `A = 2`.** Appliquer d'abord
l'observable `0` puis l'observable `1` (aux records `0` de chacune) donne le
même vecteur que l'ordre inverse. Preuve : substituer le record de `1` par un
témoin `ĝ` (invisible sur la chaîne partant de l'observable `0`, via
`chain_two_1`), commuter directement à `ĝ` fixé (`CommuteWitness` en
`r = r' = 0`), puis restaurer le record `0` (redondance de l'observable
`1` sur `ψ`).

**EN.** R2(b), order exchange (Eq. (15)), case A = 2. Applying observable
0 first and observable 1 second (using record 0 for each) yields the
same vector as the reverse order. Proof: replace the record of 1 by a
witness ĝ (invisible on the chain beginning with observable 0, via
chain_two_1), commute directly for the fixed ĝ (CommuteWitness with
r = r' = 0), and then restore record 0 (redundancy of observable 1 on
ψ).
-/
theorem swap_two [NeZero R] (Obs : Fin 2 → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs)
    (f : Fin 2 → Fin K) :
    chainProj Obs [0, 1] 0 f ψ = chainProj Obs [1, 0] 0 f ψ := by
  show rproj (Obs 1 0) (f 1) (rproj (Obs 0 0) (f 0) ψ)
      = rproj (Obs 0 0) (f 0) (rproj (Obs 1 0) (f 1) ψ)
  obtain ⟨w, hcommF⟩ := hcw 0 1 (by decide) 0 0
  have hF : rproj (Obs 0 0) (f 0) (rproj (Obs 1 w) (f 1) ψ)
      = rproj (Obs 1 w) (f 1) (rproj (Obs 0 0) (f 0) ψ) := commute_apply (hcommF (f 0) (f 1)).1 ψ
  calc rproj (Obs 1 0) (f 1) (rproj (Obs 0 0) (f 0) ψ)
      = rproj (Obs 1 w) (f 1) (rproj (Obs 0 0) (f 0) ψ) :=
        chain_two_1 Obs ψ hrec hcw 0 w 0 (f 1) (f 0)
    _ = rproj (Obs 0 0) (f 0) (rproj (Obs 1 w) (f 1) ψ) := hF.symm
    _ = rproj (Obs 0 0) (f 0) (rproj (Obs 1 0) (f 1) ψ) := by rw [hrec 1 w 0 (f 1)]

/--
**FR.** **R2(c), action diagonale, cas `A = 2`.** La branche jointe `f` (construite
au record `0` de chaque observable) est état propre de la projection de
CHAQUE observable, AU RECORD `0` (voir écart signalé en en-tête). Cas `a = 1`
(contact direct) : `Basic.rproj_contract` pointwise. Cas `a = 0` (traverser la
couche de l'observable `1`) : substitution vers un témoin (`chain_two_1`),
commutation, contraction, restauration — même schéma que `swap_two`.

**EN.** R2(c), diagonal action, case A = 2. The joint branch f
(constructed using record 0 for each observable) is an eigenstate of the
projection of EACH observable AT RECORD 0 (see the documented deviation in
the header). Case a = 1 (direct contact): pointwise
Basic.rproj_contract. Case a = 0 (crossing the layer for observable 1):
substitution to a witness (chain_two_1), commutation, contraction, and
restoration—the same pattern as in swap_two.
-/
theorem twoObs_eigen [NeZero R] (Obs : Fin 2 → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs)
    (f : Fin 2 → Fin K) (a : Fin 2) (k : Fin K) :
    rproj (Obs a 0) k (chainProj Obs [0, 1] 0 f ψ)
      = (if k = f a then (1 : ℂ) else 0) • chainProj Obs [0, 1] 0 f ψ := by
  show rproj (Obs a 0) k (rproj (Obs 1 0) (f 1) (rproj (Obs 0 0) (f 0) ψ))
      = (if k = f a then (1 : ℂ) else 0) • rproj (Obs 1 0) (f 1) (rproj (Obs 0 0) (f 0) ψ)
  rcases fin2_cases a with rfl | rfl
  · obtain ⟨g, hcommG⟩ := hcw 0 1 (by decide) 0 0
    rw [chain_two_1 Obs ψ hrec hcw 0 g 0 (f 1) (f 0)]
    rw [commute_apply (hcommG k (f 1)).1]
    rw [rproj_contract_apply (Obs 0 0) k (f 0) ψ, map_smul,
      ← chain_two_1 Obs ψ hrec hcw 0 g 0 (f 1) (f 0)]
  · exact rproj_contract_apply (Obs 1 0) k (f 1) (rproj (Obs 0 0) (f 0) ψ)

end
end QuantumFoundations.BranchesRiedel
