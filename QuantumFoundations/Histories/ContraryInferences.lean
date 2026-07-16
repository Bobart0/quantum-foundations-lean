import QuantumFoundations.Histories.Witness

/-!
# K3 — ContraryInferences : le théorème des inférences contraires de Kent

Référence : Kent, *Quasiclassical Dynamics in a Closed Quantum System*,
Phys. Rev. Lett. 78, 2874 (1997), arXiv:gr-qc/9604012. Le théorème de
profusion générique de Dowker–Kent (J. Stat. Phys. 82, 1575 (1996)) est
explicitement hors scope de ce bloc.

Note de neutralité : le contenu mathématique ci-dessous (deux ensembles
cohérents partageant préparation et post-sélection, impliquant chacun avec
certitude une proposition, ces deux propositions étant orthogonales) est un
fait incontesté. Son interprétation comme objection à la prédictibilité des
histoires cohérentes est débattue — la réponse usuelle (Griffiths) invoque la
« single-framework rule » : les deux inférences ne sont valides que CHACUNE
DANS SON PROPRE CADRE (`S 0` ou `S 1`), jamais combinées dans un même
raisonnement. Le rôle de ce fichier est de fixer l'énoncé mathématique, pas
de trancher le débat interprétatif.

## Écart vs la feuille de route : `inference` parameteré, `contrary_inferences`
mécanique une fois `inference` disponible

Même logique de factorisation qu'en K2 (`Witness.S_consistent`) : `inference`
est paramétré par `i ∈ Fin 3` (utilisé en `i = 0, 1`) plutôt que dupliqué en
`inference_S₁`/`inference_S₂`. Conséquence vérifiée (reconnaissance avant
écriture du squelette) : une fois `inference` rempli, `contrary_inferences`
s'assemble par un simple terme anonyme
`⟨S 0, S 1, ψ₀, P_ortho ‹0 ≠ 1›, S_consistent 0, S_consistent 1, inference 0,
inference 1⟩`, sans tactique ni mathématiques nouvelles. Le but ouvert de
`contrary_inferences` ci-dessous est donc gardé pour respecter la discipline
« squelette d'abord » (tout reste ouvert avant remplissage jalon par jalon),
mais sa fermeture, une fois `inference` close, ne constituera pas un jalon
mathématique à part entière — seulement la cérémonie d'assemblage finale.
-/

namespace QuantumFoundations.Histories

open scoped InnerProductSpace
open Gleason QuantumFoundations.BornRule

noncomputable section

/-- **K3(a).** Certitude conditionnelle, formulée sans quotient (discipline du
projet) : la branche `(P i)ᗮ` puis `F` a probabilité NULLE, tandis que la
branche `P i` puis `F` a probabilité NON NULLE — i.e., conditionné sur la
post-sélection `F`, `P i` est certain. Paramétré par `i ∈ Fin 3` (utilisé en
`i = 0` pour `S 0`, `i = 1` pour `S 1` — voir écart ci-dessus). -/
theorem inference (i : Fin 3) :
    histProb ψ₀ (![(P i)ᗮ, F] : History 3 2) = 0 ∧
    histProb ψ₀ (![P i, F] : History 3 2) ≠ 0 := by
  sorry

/-- **Théorème des inférences contraires de Kent.** Il existe deux familles
cohérentes d'histoires sur `H 3`, partageant la même préparation `ψ₀` et le
même étage final de post-sélection `F`, telles que la première implique avec
certitude `P 0`, la seconde implique avec certitude `P 1`, et `P 0 ⟂ P 1`. -/
theorem contrary_inferences :
    ∃ (Ps Ps' : Fin 2 → Perspective 3) (ψ : H 3),
      P 0 ⟂ P 1 ∧
      IsConsistent ψ Ps ∧ IsConsistent ψ Ps' ∧
      (histProb ψ (![(P 0)ᗮ, F] : History 3 2) = 0 ∧ histProb ψ (![P 0, F] : History 3 2) ≠ 0) ∧
      (histProb ψ (![(P 1)ᗮ, F] : History 3 2) = 0 ∧ histProb ψ (![P 1, F] : History 3 2) ≠ 0) := by
  sorry

end
end QuantumFoundations.Histories
