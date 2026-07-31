import QuantumFoundations.Selectors.Defs

/-!
**FR.** # Selectors — boîte à outils unitaire (support de S3)

Réservé aux lemmes `private` de construction d'unitaires fixant un vecteur
donné (réflexions de signe, transpositions de base) et à la transitivité
unitaire sur la sphère unité, utilisés par la preuve de
`covariant_iff_tSelector` dans `Classification.lean`. Aucun énoncé public de
ce module ne figure dans la liste des jalons S1–S5 : son contenu est un détail
d'implémentation de S3, rempli à cette étape (squelette S0 vide, par
construction).

**EN.** # Selectors — unitary toolbox (support for S3)

Reserved for `private` lemmas constructing unitaries that fix a given vector
(sign reflections, basis transpositions) and for unitary transitivity on the
unit sphere, used by the proof of `covariant_iff_tSelector` in
`Classification.lean`. No public statement of this module appears in the
S1–S5 milestone list: its content is an S3 implementation detail, filled in
at that stage (empty S0 skeleton, by construction).
-/

namespace QuantumFoundations.Selector

noncomputable section

variable {n : ℕ}

end
end QuantumFoundations.Selector
