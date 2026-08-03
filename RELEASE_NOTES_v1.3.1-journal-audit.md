# Release notes — v1.3.1-journal-audit

This corrective release strengthens the full context-independence theorem.

- `QuantumFoundations.BornRule.Perspective.eq_of_cells` proves that a
  perspective is determined by its cell set; the remaining structure fields
  are propositions and close by proof irrelevance.
- `QuantumFoundations.BornRule.lemma4_noncontextual_grain_only` proves full
  context independence, including the whole-space cell, from `AxGrain` alone.
  In the `c = ⊤` branch, both perspectives have the singleton cell set `{⊤}`
  and are therefore equal.
- `lemma4_noncontextual` retains its historical `AxNorm` argument as a source
  compatibility wrapper; that argument is not used by the proof.
- Normalization remains required downstream for normalized projective weights
  and the condition `μ ⊤ = 1`.

No unrelated theorem body, dependency pin, Gleason repository, or protected
scientific directory is changed.

Starting QF release: `v1.3.0-journal-audit` at
`747d8f441b5cd7beaa579662a535366030efe322`.
Upstream Gleason remains pinned to
`5c5bc40d2e4a31a0d1b3112fcc9a3e92b2000ec5`.

The release tag is created only after local validation, clean-clone
validation, and hosted CI have succeeded.
