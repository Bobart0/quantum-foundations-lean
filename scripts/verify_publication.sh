#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
echo "[publication] fetching pinned Mathlib cache"
lake exe cache get
echo "[publication] building QuantumFoundations"
lake build QuantumFoundations
echo "[publication] running theorem axiom audit"
lake env lean QuantumFoundations/Audit/PublicationCore.lean
echo "[publication] running source guard"
bash scripts/guard.sh
echo "[publication] checking whitespace/diff hygiene"
git diff --check
echo "[publication] PASS"
