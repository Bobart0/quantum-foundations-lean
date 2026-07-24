# Reproducibility

This document gives exact, copy-pasteable commands to build the
repository from a clean clone, run the consolidated axiom audit, and
reproduce the source guard used to enforce the no-`sorry`,
no-`native_decide`, no-project-specific-`axiom` discipline of this
repository.

## Exact toolchain and dependency revisions

- Lean toolchain (from `lean-toolchain`): `leanprover/lean4:v4.32.0-rc1`
- `mathlib` (from `lake-manifest.json`): `8bba4200986270d3b30be2bb2f8840af47a7854f`
- `gleason` (`gleason-theorem-lean`, from `lake-manifest.json`):
  `876aa7390b5d831cd81415d55493a1c0c3bae31e` (tag `v1.0-gleason`)

Transitive dependencies (`plausible`, `LeanSearchClient`, `importGraph`,
`proofwidgets`, `aesop`, `Qq`, `batteries`, and others) are pinned in full
in `lake-manifest.json`; `lake` resolves them automatically from that file.

## Clean-clone build

POSIX shell:

```sh
git clone https://github.com/Bobart0/quantum-foundations-lean.git
cd quantum-foundations-lean
git checkout v1.0-fop-companion
lake exe cache get
lake build QuantumFoundations
```

Windows PowerShell:

```powershell
git clone https://github.com/Bobart0/quantum-foundations-lean.git
Set-Location quantum-foundations-lean
git checkout v1.0-fop-companion
lake exe cache get
lake build QuantumFoundations
```

`lake exe cache get` downloads prebuilt Mathlib `.olean` files, avoiding a
from-scratch Mathlib build. A full rebuild from a clean state can also be
reproduced with:

```sh
lake clean
lake exe cache get
lake build
lake build QuantumFoundations
```

## Consolidated axiom audit

```sh
lake env lean QuantumFoundations/Audit/FoP.lean
```

This runs `#print axioms` on the principal manuscript-facing
declarations listed in `docs/FOP_THEOREM_MAP.md`. Every one is expected to
depend only on the standard Lean/Mathlib kernel trio:

```text
[propext, Classical.choice, Quot.sound]
```

Scattered subsystem-level `#print axioms` commands also remain in several
`Nonvacuity.lean` and assembly files throughout the repository, where they
were originally used to audit each milestone at the time it closed; the
consolidated module above is the single entry point for the release-wide
audit.

## Source guard

The repository enforces, by construction, that no file under
`QuantumFoundations/` contains an `axiom` declaration, a `native_decide`
call, or an unresolved `sorry`.

POSIX shell / Git Bash (`scripts/guard.sh`):

```sh
bash scripts/guard.sh
```

Expected output: a confirmation that no axiom and no `native_decide`
occurrence were found, together with a `sorry` count of `0`.

PowerShell-equivalent reproduction (used interchangeably with the shell
script; some environments provide a WSL-launcher `bash.exe` stub with no
functioning Bash, in which case this is the reference guard):

```powershell
$files = Get-ChildItem -Recurse -Path QuantumFoundations -Filter *.lean
$axiomHits = 0
$nativeDecideHits = 0
$sorryCount = 0
foreach ($f in $files) {
    $content = Get-Content $f.FullName -Raw
    $axiomHits += ([regex]::Matches($content, '(^|[^A-Za-z0-9_])axiom\s')).Count
    $nativeDecideHits += ([regex]::Matches($content, 'native_decide')).Count
    $sorryCount += ([regex]::Matches($content, '\bsorry\b')).Count
}
Write-Output "AXIOM_HITS=$axiomHits"
Write-Output "NATIVE_DECIDE_HITS=$nativeDecideHits"
Write-Output "SORRY_COUNT=$sorryCount"
if ($axiomHits -eq 0 -and $nativeDecideHits -eq 0 -and $sorryCount -eq 0) {
    Write-Output "GUARD_RESULT=PASS"
} else {
    Write-Output "GUARD_RESULT=FAIL"
}
```

Expected output: `AXIOM_HITS=0`, `NATIVE_DECIDE_HITS=0`,
`SORRY_COUNT=0`, `GUARD_RESULT=PASS`.

## Additional editorial and integrity checks

These were run at the release commit and can be reproduced identically:

```sh
git diff --check
git status --short
git grep -n "TODO\|FIXME\|TBD\|PLACEHOLDER"
git grep -n "native_decide"
git grep -n -E '(^|[^A-Za-z0-9_])axiom[[:space:]]'
git grep -n -E '\bsorry\b'
```

Each of these is expected to return no output (the `axiom`/`sorry` greps
may legitimately match prose discussing the audit itself, e.g. in
`docs/FOP_THEOREM_MAP.md` or this file; they must never match inside a
`.lean` source file's actual declarations).

## Expected results

- Zero project-specific `axiom` declarations anywhere in
  `QuantumFoundations/`.
- Zero `sorry`.
- Zero `native_decide`.
- Every principal manuscript-facing theorem depends only on
  `[propext, Classical.choice, Quot.sound]`.
- `lake build QuantumFoundations` completes with no build failure.
