import QuantumFoundations.Branches.Basic

/-!
# R2 — Cas `A = 2` : dé-risquage de la mécanique `CommuteWitness`/chaîne

Jalon volontairement réduit : valider au coût minimal la mécanique de
tunneling (chaîne à cinq étapes, éqs. (13)-(15) de Riedel) et le mécanisme
d'action diagonale, AVANT l'induction générale de `Induction.lean`. La
décomposition/unicité à deux observables COMPLÈTES ne sont PAS des sorries
séparés ici — elles tomberont comme instance `A = 2` du théorème général
`Induction.riedel`.

**Statut des énoncés ci-dessous : PROVISOIRE.** Contrairement à `Basic.lean`
(lemmes de plomberie autonomes) et à `Induction.tunneling`/`Induction.diagonal`
(forme dictée précisément par le prompt de conception), la forme EXACTE des
trois énoncés suivants n'est pas entièrement fixée par les équations (13)-(15)
telles que résumées dans ce projet — ils sont écrits comme instances directes,
à `A = 2`, du couple T/E de `Induction.lean` (avec `L` réduit à un singleton),
et pourront être reformulés sans que ce soit une violation de la règle 2 (rien
n'en dépend encore) lors du remplissage effectif de ce jalon.
-/

namespace QuantumFoundations.Branches

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n K R : ℕ}

/-- **R2(a), chaîne à cinq étapes (éqs. (13)-(14)), cas minimal `A = 2`.**
Le résultat d'appliquer la projection de l'observable `0` au record `r`, puis
une projection quelconque de `1` compatible (`CommuteWitness`), puis la
projection de `0` au record `r'`, ne dépend pas de `r` — seul le résultat
final compte, grâce à la redondance (`IsRecordedOn`). Instance de
`Induction.tunneling` à `L = [1]`, `a = 0`. -/
theorem chain_two (Obs : Fin 2 → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs)
    (r r' : Fin R) (ρ₁ : Fin R) (i : Fin K) :
    rproj (Obs 0 r) i (chainProj Obs [1] (fun _ => ρ₁) (fun _ => i) ψ)
      = rproj (Obs 0 r') i (chainProj Obs [1] (fun _ => ρ₁) (fun _ => i) ψ) := by
  sorry

/-- **R2(b), échange d'ordre (éq. (15)), cas `A = 2`.** Appliquer d'abord
l'observable `0` puis l'observable `1` donne le même vecteur que l'ordre
inverse, sur la branche jointe (`f 0`, `f 1`) — conséquence de
`CommuteWitness` et de la redondance des deux observables. -/
theorem swap_two [NeZero R] (Obs : Fin 2 → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs)
    (f : Fin 2 → Fin K) :
    chainProj Obs [0, 1] 0 f ψ = chainProj Obs [1, 0] 0 f ψ := by
  sorry

/-- **R2(c), action diagonale, cas `A = 2`.** La branche jointe `f` est
état propre de la projection de CHAQUE observable, à l'étiquette `f a` —
instance de `Induction.diagonal` à `A = 2`. -/
theorem twoObs_eigen [NeZero R] (Obs : Fin 2 → Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs)
    (f : Fin 2 → Fin K) (a : Fin 2) (r : Fin R) (k : Fin K) :
    rproj (Obs a r) k (chainProj Obs [0, 1] 0 f ψ)
      = (if k = f a then (1 : ℂ) else 0) • chainProj Obs [0, 1] 0 f ψ := by
  sorry

end
end QuantumFoundations.Branches
