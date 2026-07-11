#!/usr/bin/env bash
# Installation initiale. À lancer UNE FOIS après clonage.
#
# IMPORTANT : ce projet épingle une révision Mathlib précise (lakefile.toml,
# lake-manifest.json) pour rester reproductible. On NE resynchronise PAS la
# toolchain sur Mathlib master et on n'appelle PAS `lake update` ici : cela
# ferait dériver le build hors de l'état vérifié/tagué. `elan` installe
# automatiquement la toolchain épinglée dans lean-toolchain au premier appel
# de `lake`/`lean`. Pour bumper Mathlib intentionnellement, faites-le à part
# (`lake update mathlib`) puis re-vérifiez `lake build` avant de commiter.
set -euo pipefail
cd "$(dirname "$0")"

# 1. Télécharger le cache Mathlib précompilé pour la révision épinglée
#    (INDISPENSABLE : sinon plusieurs heures de compilation).
lake exe cache get

# 2. Construire le projet (versions figées par lakefile.toml / lake-manifest.json)
lake build
