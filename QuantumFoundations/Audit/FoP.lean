import QuantumFoundations

/-!
# Consolidated Foundations of Physics trust-base audit

**EN.** This publication-facing module runs `#print axioms` on the
principal declarations used substantively in the manuscript *One State,
Many Perspectives: Branch Structure and Born Weights in Everettian
Quantum Mechanics*. Every declaration below is expected to depend only on
the standard Lean/Mathlib kernel trio `[propext, Classical.choice,
Quot.sound]`; this repository's source guard separately confirms, on the
source text itself, the absence of any project-specific trust-widening
declaration or escape hatch (see `docs/REPRODUCIBILITY.md` for the exact
commands and expected tokens). See
`docs/FOP_THEOREM_MAP.md` for the mathematical status, dependencies, and
scope of each declaration audited here. This module does not modify any
theorem body; it only invokes `#print axioms` on already-proved
declarations.

**FR.** Ce module, destiné à la publication, exécute `#print axioms` sur
les principales déclarations utilisées de façon substantielle dans le
manuscrit *One State, Many Perspectives: Branch Structure and Born
Weights in Everettian Quantum Mechanics*. Chaque déclaration ci-dessous ne
doit dépendre que du trio standard du noyau Lean/Mathlib
`[propext, Classical.choice, Quot.sound]` ; la garde source de ce dépôt
confirme séparément, sur le texte source lui-même, l'absence de toute
déclaration élargissant la base de confiance ou d'échappatoire propre au
projet (voir `docs/REPRODUCIBILITY.md` pour les commandes exactes et les
motifs recherchés). Voir `docs/FOP_THEOREM_MAP.md`
pour le statut mathématique, les dépendances et la portée de chaque
déclaration auditée ici. Ce module ne modifie aucun corps de preuve ; il ne
fait qu'invoquer `#print axioms` sur des déclarations déjà démontrées.
-/

-- Grain coherence / Born representation (BornRule)
#print axioms QuantumFoundations.BornRule.grainCoherenceTheorem

-- Riedel branch-decomposition theorem
#print axioms QuantumFoundations.BranchesRiedel.riedel

-- Main record-complexity interference lower bound
#print axioms QuantumFoundations.Complexity.redundant_records_give_interference_lower_bound

-- Simulated-evolution persistence theorem
#print axioms QuantumFoundations.Complexity.SimulatedEvolution.margin_gap_persists_under_simulated_evolution

-- C14 record-induced branch-weight theorem
#print axioms QuantumFoundations.BranchesRiedel.BornBridge.record_induced_Born_decomposition

-- Final qubit/Busch Born-weight theorem
#print axioms QuantumFoundations.BornRule.EffectPerspectives.qubit_projectionEffect_weight_eq_born

-- Effect-perspective / Naimark bridge (QB11)
#print axioms QuantumFoundations.BornRule.EffectPerspectives.effectPerspective_naimark_realization
#print axioms QuantumFoundations.BornRule.EffectPerspectives.effectPerspective_born_preserved_under_dilation
#print axioms QuantumFoundations.BornRule.EffectPerspectives.effectPerspective_projective_ancilla_realization

-- C15 restricted-sector uniqueness (Lela)
#print axioms QuantumFoundations.BornRule.RestrictedRecordSectors.restricted_record_sector_born

-- C17 quantitative weight stability
#print axioms QuantumFoundations.BornRule.RestrictedRecordSectors.restricted_record_sector_weight_uniform_stability

-- C17b simulated-evolution stability bridge
#print axioms QuantumFoundations.BornRule.RestrictedRecordSectors.sector_weight_stability_under_circuit_simulation

-- C17b record-induced branch pointwise stability bridge
#print axioms QuantumFoundations.BranchesRiedel.BornBridge.recordBranch_weight_pointwise_stability

-- Kent's contrary-inferences theorem (conceptual contrast)
#print axioms QuantumFoundations.HistoriesKent.contrary_inferences

-- Naimark dilation theorem (auxiliary operational theorem)
#print axioms QuantumFoundations.naimark

-- Wigner's theorem (infrastructural)
#print axioms QuantumFoundations.Wigner.wigner

-- Uhlhorn-type uniqueness (infrastructural)
#print axioms QuantumFoundations.Uhlhorn.uhlhorn_finite_dim
