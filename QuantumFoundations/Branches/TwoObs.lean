import QuantumFoundations.Branches.Basic

/-!
# R2 — Cas `A = 2` : dé-risquage de la mécanique `CommuteWitness`/chaîne

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
-/

namespace QuantumFoundations.Branches

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n K R : ℕ}

private theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

/-- Cible `0`, autre observable `1` : substituer le record de `0` (`r → r'`)
est invisible après application de la projection de `1` (au record
quelconque `ρ₁`) à `ψ` — le cœur du mécanisme de tunneling, à `A = 2`. -/
private theorem chain_two_0 (Obs : Fin 2 → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs)
    (r r' ρ₁ : Fin R) (i j : Fin K) :
    rproj (Obs 0 r) i (rproj (Obs 1 ρ₁) j ψ) = rproj (Obs 0 r') i (rproj (Obs 1 ρ₁) j ψ) := by
  obtain ⟨ĝ, hcomm⟩ := hcw 0 1 (by decide) r r'
  rw [hrec 1 ρ₁ ĝ j, commute_apply (hcomm i j).1, hrec 0 r r' i, ← commute_apply (hcomm i j).2]

/-- Symétrique de `chain_two_0` : cible `1`, autre observable `0`. -/
private theorem chain_two_1 (Obs : Fin 2 → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs)
    (s s' ρ₀ : Fin R) (j i : Fin K) :
    rproj (Obs 1 s) j (rproj (Obs 0 ρ₀) i ψ) = rproj (Obs 1 s') j (rproj (Obs 0 ρ₀) i ψ) := by
  obtain ⟨ĝ, hcomm⟩ := hcw 1 0 (by decide) s s'
  rw [hrec 0 ρ₀ ĝ i, commute_apply (hcomm j i).1, hrec 1 s s' j, ← commute_apply (hcomm j i).2]

/-- **R2(a), chaîne à cinq étapes (éqs. (13)-(14)), cas minimal `A = 2`.**
Instance directe de `chain_two_0` (`i = j`, correspondant à `L = [1]`,
`f := fun _ => i` dans `chainProj`). -/
theorem chain_two (Obs : Fin 2 → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs)
    (r r' : Fin R) (ρ₁ : Fin R) (i : Fin K) :
    rproj (Obs 0 r) i (chainProj Obs [1] (fun _ => ρ₁) (fun _ => i) ψ)
      = rproj (Obs 0 r') i (chainProj Obs [1] (fun _ => ρ₁) (fun _ => i) ψ) := by
  show rproj (Obs 0 r) i (rproj (Obs 1 ρ₁) i ψ) = rproj (Obs 0 r') i (rproj (Obs 1 ρ₁) i ψ)
  exact chain_two_0 Obs ψ hrec hcw r r' ρ₁ i i

/-- **R2(b), échange d'ordre (éq. (15)), cas `A = 2`.** Appliquer d'abord
l'observable `0` puis l'observable `1` (aux records `0` de chacune) donne le
même vecteur que l'ordre inverse. Preuve : substituer le record de `1` par un
témoin `ĝ` (invisible sur la chaîne partant de l'observable `0`, via
`chain_two_1`), commuter directement à `ĝ` fixé (`CommuteWitness` en
`r = r' = 0`), puis restaurer le record `0` (redondance de l'observable
`1` sur `ψ`). -/
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

/-- **R2(c), action diagonale, cas `A = 2`.** La branche jointe `f` (construite
au record `0` de chaque observable) est état propre de la projection de
CHAQUE observable, AU RECORD `0` (voir écart signalé en en-tête). Cas `a = 1`
(contact direct) : `Basic.rproj_contract` pointwise. Cas `a = 0` (traverser la
couche de l'observable `1`) : substitution vers un témoin (`chain_two_1`),
commutation, contraction, restauration — même schéma que `swap_two`. -/
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
end QuantumFoundations.Branches
