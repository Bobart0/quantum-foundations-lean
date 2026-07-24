#!/usr/bin/env bash
# **FR.** Garde-fou anti-régression : compte les axiomes, les `native_decide`
# et les `sorry` non résolus dans l'arbre source intégré (`QuantumFoundations`
# et `QuantumFoundations.lean`). La leçon du fichier legacy (128k lignes,
# incohérent) : un seul `axiom` mal quantifié suffit à rendre tout le
# développement réfutable.
#
# **EN.** Anti-regression guard: counts axioms, `native_decide` calls, and
# unresolved `sorry`s in the integrated source tree (`QuantumFoundations`
# and `QuantumFoundations.lean`). The lesson from the legacy file (128k
# lines, inconsistent): a single ill-quantified `axiom` is enough to make
# the entire development refutable.
set -euo pipefail
cd "$(dirname "$0")/.."

# **FR.** Chaque comptage est protégé par `|| true` : sous `pipefail`, un
# `grep` sans correspondance (code de sortie 1) ne doit jamais interrompre
# le script avant l'affichage du résultat final.
# **EN.** Each count is guarded with `|| true`: under `pipefail`, a `grep`
# with no match (exit code 1) must never abort the script before the final
# result is printed.
AXIOM_HITS=$(grep -rnE '(^|[^[:alnum:]_])axiom[[:space:]]' QuantumFoundations QuantumFoundations.lean 2>/dev/null | wc -l | tr -d ' ' || true)
NATIVE_DECIDE_HITS=$(grep -rn 'native_decide' QuantumFoundations QuantumFoundations.lean 2>/dev/null | wc -l | tr -d ' ' || true)
SORRY_COUNT=$(grep -rno '\bsorry\b' QuantumFoundations QuantumFoundations.lean 2>/dev/null | wc -l | tr -d ' ' || true)

echo "AXIOM_HITS=${AXIOM_HITS}"
echo "NATIVE_DECIDE_HITS=${NATIVE_DECIDE_HITS}"
echo "SORRY_COUNT=${SORRY_COUNT}"

if [ "${AXIOM_HITS}" -eq 0 ] && [ "${NATIVE_DECIDE_HITS}" -eq 0 ] && [ "${SORRY_COUNT}" -eq 0 ]; then
  echo "GUARD_RESULT=PASS"
  exit 0
else
  echo "GUARD_RESULT=FAIL"
  exit 1
fi
