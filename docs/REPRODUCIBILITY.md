# Reproducibility

Clean-clone build and publication-facing audit for release `v1.4.3`.

## Pinned environment

- Lean: `leanprover/lean4:v4.32.0-rc1`
- Mathlib: `8bba4200986270d3b30be2bb2f8840af47a7854f`
- Gleason: `v1.1.2`, commit
  `6156219f606c6ac22690c84147ba2771d4cb18f3`

## Build

```sh
git clone https://github.com/Bobart0/quantum-foundations-lean.git
cd quantum-foundations-lean
git checkout v1.4.3
lake exe cache get
lake build QuantumFoundations
```

## Theorem audit

```sh
lake env lean QuantumFoundations/Audit/PublicationCore.lean
```

Expected trust base: `[propext, Classical.choice, Quot.sound]`.

## Source guard

```sh
bash scripts/guard.sh
```

Expected summary: `AXIOM_HITS=0`, `NATIVE_DECIDE_HITS=0`,
`SORRY_COUNT=0`, `GUARD_RESULT=PASS`.

## One-command verification

```sh
bash scripts/verify_publication.sh
```

Historical audit entry points remain only for compatibility.
