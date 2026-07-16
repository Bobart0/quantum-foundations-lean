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
écriture du squelette, puis confirmée à la fermeture) : une fois `inference`
rempli, `contrary_inferences` s'assemble par un simple terme anonyme
`⟨S 0, S 1, ψ₀, P_ortho ‹0 ≠ 1›, S_consistent 0 …, S_consistent 1 …,
inference 0 …, inference 1 …⟩`, sans tactique ni mathématiques nouvelles.

## Correction de l'énoncé (règle 2 du projet) : même hypothèse `i = 0 ∨ i = 1`
qu'en K2

Comme pour `S_consistent` (voir `Witness.lean`), le squelette K0 énonçait
`inference (i : Fin 3)` sans restriction. Faux pour `i = 2` par la même
annulation qui échoue (`⟪φ₀, e 2⟫ = -1 ≠ 1`). Ajout de l'hypothèse
`i = 0 ∨ i = 1`.
-/

namespace QuantumFoundations.Histories

open scoped InnerProductSpace
open Gleason QuantumFoundations.BornRule

noncomputable section

/-- **K3(a).** Certitude conditionnelle, formulée sans quotient (discipline du
projet) : la branche `(P i)ᗮ` puis `F` a probabilité NULLE, tandis que la
branche `P i` puis `F` a probabilité NON NULLE — i.e., conditionné sur la
post-sélection `F`, `P i` est certain. Paramétré par `i ∈ Fin 3` avec
`i = 0 ∨ i = 1` (utilisé en `i = 0` pour `S 0`, `i = 1` pour `S 1` — voir
écart ci-dessus).

Preuve : `chainOp_two_stage` réduit chaque branche à `projL F (projL c₀ ψ₀)`.
Branche `(P i)ᗮ` : `projL (P i)ᗮ ψ₀ = ψ₀ - e i` (`projL_compl` +
`P_proj_psi0`), et `⟪φ₀, ψ₀ - e i⟫ = 0` (`w_ortho`, l'annulation clé) annule
`projL F` dessus. Branche `P i` : `projL (P i) ψ₀ = e i`, et
`projL F (e i) = (1/‖φ₀‖²) • φ₀ ≠ 0` puisque `φ₀ ≠ 0` et `1/‖φ₀‖² ≠ 0`
(`φ₀_norm_sq`, `φ₀_ne_zero`). -/
theorem inference (i : Fin 3) (hi : i = 0 ∨ i = 1) :
    histProb ψ₀ (![(P i)ᗮ, F] : History 3 2) = 0 ∧
    histProb ψ₀ (![P i, F] : History 3 2) ≠ 0 := by
  constructor
  · show ‖chainOp (![(P i)ᗮ, F] : History 3 2) ψ₀‖ ^ 2 = 0
    rw [chainOp_two_stage]
    show ‖projL F (projL (P i)ᗮ ψ₀)‖ ^ 2 = 0
    rw [projL_compl, P_proj_psi0, projL_F_eq, (w_ortho i hi).2.2]
    norm_num
  · show ‖chainOp (![P i, F] : History 3 2) ψ₀‖ ^ 2 ≠ 0
    rw [chainOp_two_stage]
    show ‖projL F (projL (P i) ψ₀)‖ ^ 2 ≠ 0
    rw [P_proj_psi0, projL_F_eq, phi0_inner_e01 i hi, φ₀_norm_sq]
    simp only [ne_eq, sq_eq_zero_iff, norm_eq_zero, smul_eq_zero]
    push Not
    refine ⟨?_, φ₀_ne_zero⟩
    norm_num

/-- **Théorème des inférences contraires de Kent.** Il existe deux familles
cohérentes d'histoires sur `H 3`, partageant la même préparation `ψ₀` et le
même étage final de post-sélection `F`, telles que la première implique avec
certitude `P 0`, la seconde implique avec certitude `P 1`, et `P 0 ⟂ P 1`.

Assemblage mécanique (voir écart en en-tête) à partir de K2
(`S_consistent`, `P_ortho`) et K3(a) (`inference`) — aucune mathématique
nouvelle. -/
theorem contrary_inferences :
    ∃ (Ps Ps' : Fin 2 → Perspective 3) (ψ : H 3),
      P 0 ⟂ P 1 ∧
      IsConsistent ψ Ps ∧ IsConsistent ψ Ps' ∧
      (histProb ψ (![(P 0)ᗮ, F] : History 3 2) = 0 ∧ histProb ψ (![P 0, F] : History 3 2) ≠ 0) ∧
      (histProb ψ (![(P 1)ᗮ, F] : History 3 2) = 0 ∧ histProb ψ (![P 1, F] : History 3 2) ≠ 0) :=
  ⟨S 0, S 1, ψ₀, P_ortho (by decide), S_consistent 0 (Or.inl rfl), S_consistent 1 (Or.inr rfl),
    inference 0 (Or.inl rfl), inference 1 (Or.inr rfl)⟩

end
end QuantumFoundations.Histories
