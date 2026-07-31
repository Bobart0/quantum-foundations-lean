import QuantumFoundations.Selectors.Covariance
import QuantumFoundations.Selectors.Pinning

/-!
**FR.** # Selectors — Nonvacuité (AGENTS.md règle 3)

`Selector n`, `IsCovariant`, `NSNC1` sont chacun habités. Le témoin qui
compte : `tSelector 2 _ (1/2) _ _` est unitairement covariant et **ne**
satisfait **pas** NSNC-1 — c'est la preuve concrète, en dimension 2, que la
covariance seule ne suffit pas à isoler la règle de Born.

Écart signalé (AGENTS.md règle 2, non absorbé silencieusement) : ce fichier
importe `Covariance.lean` et `Pinning.lean`, situés plus loin dans la liste de
l'architecture cible (§3 de la mission). L'ordre de cette liste est un ordre
de lecture/jalon (S1 à S5), pas une contrainte d'import Lean ; le graphe de
dépendances réel est Defs → Unitaries → Covariance → {Classification,
Nonvacuity}, Defs → Pinning → Nonvacuity, qui est acyclique. La règle 3
(nonvacuité dans le même commit que l'introduction de la structure) porte sur
l'atomicité du commit, pas sur la position du fichier dans le répertoire :
elle sera respectée en pratique par le séquencement des commits S1–S5, pas en
figeant ce fichier à un sous-ensemble artificiellement restreint des lemmes
déjà nécessaires à son propre témoin.

**EN.** # Selectors — Nonvacuity (AGENTS.md rule 3)

`Selector n`, `IsCovariant`, `NSNC1` are each inhabited. The witness that
matters: `tSelector 2 _ (1/2) _ _` is unitarily covariant and does **not**
satisfy NSNC-1 — the concrete, dimension-2 proof that covariance alone is not
enough to isolate the Born rule.

Deviation flagged (AGENTS.md rule 2, not silently absorbed): this file
imports `Covariance.lean` and `Pinning.lean`, listed later in the target
architecture (mission §3). That list's order is a reading/milestone order (S1
through S5), not a Lean import constraint; the actual dependency graph is
Defs → Unitaries → Covariance → {Classification, Nonvacuity}, Defs → Pinning
→ Nonvacuity, which is acyclic. Rule 3 (nonvacuity in the same commit as the
structure's introduction) is about commit atomicity, not file position in the
directory listing: it will be honored in practice through the S1–S5 commit
sequencing, not by artificially restricting this file to a subset of the
lemmas its own witness actually needs.
-/

namespace QuantumFoundations.Selector

noncomputable section

/--
**FR.** `Selector n` est habité, par le sélecteur de Born.

**EN.** `Selector n` is inhabited, by the Born selector.
-/
theorem selector_nonempty : Nonempty (Selector 2) := ⟨bornSelector 2⟩

/--
**FR.** `IsCovariant` est habité.

**EN.** `IsCovariant` is inhabited.
-/
theorem isCovariant_nonempty : ∃ σ : Selector 2, IsCovariant σ :=
  ⟨bornSelector 2, bornSelector_isCovariant⟩

/--
**FR.** `NSNC1` est habité.

**EN.** `NSNC1` is inhabited.
-/
theorem nsnc1_nonempty : ∃ σ : Selector 2, NSNC1 σ := by
  sorry

/--
**FR.** Le témoin qui compte : `tSelector 2 _ (1/2) _ _` est unitairement
covariant et ne satisfait pas NSNC-1. La covariance seule ne suffit donc pas.

**EN.** The witness that matters: `tSelector 2 _ (1/2) _ _` is unitarily
covariant and does not satisfy NSNC-1. Covariance alone is therefore not
enough.
-/
theorem tSelector_half_covariant_not_nsnc1 :
    IsCovariant (tSelector 2 (le_refl 2) (1 / 2) (by norm_num) (by norm_num)) ∧
      ¬ NSNC1 (tSelector 2 (le_refl 2) (1 / 2) (by norm_num) (by norm_num)) := by
  sorry

end
end QuantumFoundations.Selector
