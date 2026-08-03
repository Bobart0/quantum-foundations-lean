import QuantumFoundations.BornRule.Perspective
import QuantumFoundations.BornRule.Nonvacuity
import QuantumFoundations.BornRule.Assembly

/-!
# Journal audit: proper-cell vs. full non-contextuality

**EN.** This publication-facing module is a focused corrective audit for the
coordinated journal-audit release. It checks, independently of the rest of
the repository's audit surface, the exact public-contract shape and trust
base of the corrected non-contextuality scope:

- `lemma4_noncontextual_of_ne_top` — context independence of a **proper**
  cell (`c ≠ ⊤`), derived from `(Grain)` **alone**, without `AxNorm`;
- `lemma4_noncontextual` — **full** context independence, including the
  degenerate whole-space cell `⊤`, derived from `(Grain)` together with
  `(Norm)`;
- `E₀_satisfies_axioms` — the nonvacuity witness showing the Born rule for a
  fixed unit vector simultaneously satisfies all four coherence axioms;
- `grainCoherenceTheorem` / `grainCoherenceTheorem_projector` — the Grain
  Coherence Theorem assembling the Born-rule weight representation from the
  four axioms.

See `docs/FOP_THEOREM_MAP.md` for the corrected scope statement of each
declaration. This module does not modify any theorem body; it only checks
public signatures (`#check`) and invokes `#print axioms` on already-proved
declarations. Every declaration below is expected to depend only on the
standard Lean/Mathlib kernel trio `[propext, Classical.choice, Quot.sound]`.

**FR.** Ce module, destiné à la publication, est un audit correctif ciblé
pour la release coordonnée d'audit pré-journal. Il vérifie, indépendamment du
reste de la surface d'audit du dépôt, la forme exacte du contrat public et la
base de confiance de la portée corrigée de la non-contextualité :

- `lemma4_noncontextual_of_ne_top` — indépendance de contexte d'une cellule
  **propre** (`c ≠ ⊤`), dérivée de `(Grain)` **seul**, sans `AxNorm` ;
- `lemma4_noncontextual` — indépendance de contexte **complète**, y compris
  la cellule dégénérée `⊤`, dérivée de `(Grain)` conjointe à `(Norm)` ;
- `E₀_satisfies_axioms` — le témoin de non-vacuité montrant que la règle de
  Born pour un vecteur unitaire fixé satisfait simultanément les quatre
  axiomes de cohérence ;
- `grainCoherenceTheorem` / `grainCoherenceTheorem_projector` — le Théorème
  de Cohérence de Grain assemblant la représentation en poids de la règle de
  Born à partir des quatre axiomes.

Voir `docs/FOP_THEOREM_MAP.md` pour l'énoncé de portée corrigé de chaque
déclaration. Ce module ne modifie aucun corps de preuve ; il ne fait que
vérifier des signatures publiques (`#check`) et invoquer `#print axioms` sur
des déclarations déjà démontrées.
-/

open QuantumFoundations.BornRule

-- ── Public-contract visibility ──────────────────────────────────────

#check @lemma4_noncontextual_of_ne_top
#check @lemma4_noncontextual
#check @E₀_satisfies_axioms
#check @grainCoherenceTheorem
#check @grainCoherenceTheorem_projector

-- ── Trust-base audit ─────────────────────────────────────────────────

#print axioms QuantumFoundations.BornRule.lemma4_noncontextual_of_ne_top
#print axioms QuantumFoundations.BornRule.lemma4_noncontextual
#print axioms QuantumFoundations.BornRule.E₀_satisfies_axioms
#print axioms QuantumFoundations.BornRule.grainCoherenceTheorem
#print axioms QuantumFoundations.BornRule.grainCoherenceTheorem_projector
