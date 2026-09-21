#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

echo "[AFM] fetching pinned Mathlib cache"
lake exe cache get

echo "[AFM] building QuantumFoundations"
lake build QuantumFoundations

echo "[AFM] running exact manuscript axiom audit"
lake env lean QuantumFoundations/Audit/AFM.lean

echo "[AFM] running source guard"
bash scripts/guard.sh

echo "[AFM] checking whitespace/diff hygiene"
git diff --check

echo "[AFM] PASS"
