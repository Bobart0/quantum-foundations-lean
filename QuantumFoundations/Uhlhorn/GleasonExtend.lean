import QuantumFoundations.Uhlhorn.Defs

/-!
# U3a — Extension d'une fonction-cadre sur les droites en `ProjMeasure` complet

Pièce à part entière, PAS un détail interne de U3b (`GleasonTwice.lean`) : pour
appliquer `Gleason.gleason`, qui prend un `ProjMeasure` complet (défini et additif
sur TOUT sous-espace, cf. `Gleason.Defs`), à la fonction-cadre
`φ_D(P) := tr(D · φ(P))` de la preuve de Šemrl (qui n'est a priori définie que sur
les droites `Proj1 n`), il faut d'abord l'étendre.

**Confirmé par audit du dépôt `gleason` (Étape 0 de U0)** : aucun lemme de ce type
n'existe dans `gleason-theorem-lean`. Les deux seuls sites de construction d'un
`ProjMeasure` du dépôt (`EffectMeasure.toProjMeasure`, `pureState`) donnent tous
deux une formule FERMÉE valable directement sur tout sous-espace, sans jamais
étendre une donnée partielle définie seulement sur les droites. Décision : ce
lemme reste dans `quantum-foundations-lean` (namespace `Uhlhorn`), pas dans
`gleason-theorem-lean` — même s'il s'agit d'un fait Gleason générique, on ne
rouvre pas le dépôt public tagué pour ce besoin.

Stratégie de preuve (détaillée dans un prompt dédié à l'exécution de U3a, pas ici) :
étendre chaque sous-espace `A` en une base orthonormée (`stdOrthonormalBasis`/
`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`), sommer `g` sur cette
base. Le point délicat : montrer que cette somme ne dépend PAS du choix de la base
orthonormée de `A` (en complétant deux bases candidates de `A` par la MÊME base de
`Aᗮ`, et en comparant les deux sommes totales, toutes deux égales à `1` par
hypothèse). Taille estimée : ~100-150 lignes, 4 à 6 sous-buts intermédiaires.
-/

namespace QuantumFoundations.Uhlhorn

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ}

/-- **U3a** : une fonction-cadre définie seulement sur les droites, additive sur
toute base orthonormée, s'étend en un `ProjMeasure n` complet qui coïncide avec
elle sur chaque droite. -/
theorem exists_projMeasure_of_frameFunctionOnLines (n : ℕ) (g : Proj1 n → ℝ)
    (hg : IsFrameFunctionOnLines g) :
    ∃ m : ProjMeasure n, ∀ P : Proj1 n, m.μ (P : Submodule ℂ (H n)) = g P := by
  sorry

end
end QuantumFoundations.Uhlhorn
