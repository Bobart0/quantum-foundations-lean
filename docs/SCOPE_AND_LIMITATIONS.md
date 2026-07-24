# Scope and Limitations

This document states explicitly what the `v1.0-fop-companion` release does
not establish. It is intended to prevent overinterpretation of the formal
results summarized in `docs/FOP_THEOREM_MAP.md`.

## This release does not prove

- **Born weights from unitarity alone.** The Born-weight representation
  theorems (`grainCoherenceTheorem`, the Busch-based qubit theorem in
  `BornRule.EffectPerspectives`) all require explicit representation
  hypotheses (Grain/Norm/Pos/Null, or the effect-perspective analogues);
  none of them derives the Born rule from unitary dynamics alone.
- **Universal decoherence.** No theorem in this repository establishes
  that decoherence occurs universally, or characterizes the physical
  conditions under which record formation actually occurs.
- **An absolute or uniquely fundamental branch ontology.** The
  branch-decomposition results (Riedel's theorem and its C14 Born-weight
  connection) formalize a specific mathematical decomposition under stated
  hypotheses (redundancy, a commutation witness); they do not assert that
  this decomposition is the unique physically meaningful one, or that
  branches are ontologically fundamental.
- **Approximate uniqueness of branch decompositions.** No theorem
  establishes that branch decompositions remain unique, or approximately
  unique, under perturbed or approximate hypotheses.
- **Stability of C15 under approximate assumptions.** C15
  (`restricted_record_sector_born`) establishes exact uniqueness under
  exact saturation hypotheses on a restricted record sector. C17 and C17b
  establish that *projected-component proximity implies quantitative
  weight proximity*; they do not establish that the C15 uniqueness
  conclusion itself remains valid, even approximately, when the C15
  hypotheses hold only approximately.
- **Physical realization of binary saturation.** The saturation
  hypotheses underlying C15/C17/C17b are mathematical hypotheses on a
  scalar or operator model; no claim is made that any physical system
  realizes them exactly or approximately.
- **C16.** The C16 milestone (as referenced in `MILESTONES.md`) is not
  part of this release and remains open.
- **Infinite-dimensional or quantum-field-theoretic extensions.** Every
  theorem in this repository is stated and proved in finite dimension over
  ℂ. No claim, explicit or implicit, is made about infinite-dimensional
  Hilbert spaces or quantum field theory.
- **A decision-theoretic or normative derivation.** No theorem in this
  repository derives the Born rule, or any weight assignment, from a
  decision-theoretic, Bayesian, or normative-rationality argument. The
  effect-perspective development (`BornRule.EffectPerspectives`) states
  explicitly, in its own `README.md`, that its derived weights are not
  claimed to constitute rational credences in any decision-theoretic
  sense.
- **Minimality or uniqueness of every Naimark dilation.** The Naimark
  dilation theorem (`QuantumFoundations.naimark` and its corollaries)
  establishes that a projective realization of a given POVM exists; it
  does not establish that this realization is minimal or unique, nor that
  it is the physically implemented one.
- **Physical persistence of every record-sector selection.** The
  robustness and persistence theorems in `Complexity/` and
  `RestrictedRecordSectors/` are stated for explicit mathematical models
  of noise and evolution (approximate-record readout, simulated
  norm-preserving evolution); they do not establish that a physically
  selected record sector persists under arbitrary real dynamics.

## Additional clarifications

- **Priority.** No unrestricted historical priority claim is made for
  C17 or C17b; they are presented as the first quantitative
  weight-stability results *within this formal development*. Known
  results reused in this repository (Gleason, Busch, Naimark, Riedel,
  Kent, Wigner, Uhlhorn-type uniqueness, and Lela's restricted-sector
  uniqueness theorem underlying C15) are attributed to their original
  authors; this repository formalizes, adapts, or integrates them, and
  does not claim their original discovery. See `docs/FOP_THEOREM_MAP.md`
  for the exact status of every theorem.
- **HistoriesKent.** The Kent contrary-inferences formalization is
  presented as a conceptual contrast to the branch-theoretic development,
  illustrating a limitation of naive consistent-histories reasoning. It is
  not used as a premise anywhere in the `BranchesRiedel`/`BornRule` chain.
- **Wigner and the full Uhlhorn theorem.** These are formalized and
  available in this repository, but they are not invoked as substantive
  premises of the manuscript's central Born-weight argument. Specific
  internal lemmas from the Uhlhorn development are reused by `BornRule`
  (see `docs/FOP_THEOREM_MAP.md`); the assembled Uhlhorn theorem itself is
  not.

## Résumé en français

Cette version ne prouve pas : les poids de Born à partir de la seule
unitarité ; une décohérence universelle ; une ontologie de branches
absolue ou uniquement fondamentale ; l'unicité approximative des
décompositions en branches ; la stabilité de C15 sous hypothèses
approximatives ; la réalisation physique de la saturation binaire ; C16 ;
des extensions en dimension infinie ou en théorie quantique des champs ;
une dérivation décision-théorique ou normative ; la minimalité ou
l'unicité de toute dilatation de Naimark ; ni la persistance physique de
toute sélection de secteur de records. Aucune revendication de priorité
historique non restreinte n'est formulée pour C17/C17b ; les résultats
connus réutilisés (Gleason, Busch, Naimark, Riedel, Kent, Wigner, unicité
de type Uhlhorn, unicité sur les secteurs restreints de Lela) sont
attribués à leurs auteurs d'origine.
