# SORRIES.md — quantum-foundations-lean

Suivi de l'avancement, sur le modèle de gleason-theorem-lean. Coché = `lake build`
vert, 0 axiome (guard.sh), commit + push fait. Sources : Watrous *TQI* Thm 2.42
(cœur), Paris §3.2 Thm 4 (contexte physique, N5 optionnel).

Compte total attendu (Naimark, hors N5) : **13 sorry** au sortir de N0.

---

## N0 — Squelette (Defs, SqrtOp, DilSpace, Main, Nonvacuity)
- [x] Étape 0 validée : signatures spectrales, racines carrées existantes,
      choix d'espace de dilatation (K₁ PiLp imbriqué vs K₂ plat) tranché.
      Décisions : (b) pas de raccourci `CFC.sqrt` retenu — construction spectrale
      maison (`eigenvectorBasis` + `rankOne`), fidèle à la convention `LinearMap` du
      projet et au calque interne de `ContinuousLinearMap.isPositive_iff_eq_sum_rankOne`.
      (d) K₂ := `EuclideanSpace ℂ (Fin m × Fin n)` retenu sur K₁ (friction de preuve
      égale, mais index plat unique, moins de couches `WithLp`/`.ofLp`).
- [x] `POVM n m` défini (réutilise `IsPositiveOp` de gleason)
- [x] Nonvacuity : POVM uniforme (n=2, m=2) prouvée habitée
- [x] Squelette compile, 13 sorry, 0 axiome, CI/guard.sh adaptés au nouveau nom

## N1 — `sqrtOp` (le seul contenu mathématique neuf)
- [ ] `sqrtOp_isPositive : IsPositiveOp T → IsPositiveOp (sqrtOp T)`
- [ ] `sqrtOp_mul_self : IsPositiveOp T → sqrtOp T ∘ₗ sqrtOp T = T`

## N2 — Briques de l'espace dilaté `K`
- [ ] `inner_singleL : ⟪singleL i x, w⟫ = ⟪x, coordL i w⟫`
- [ ] `adjoint_singleL : adjoint (singleL i) = coordL i`
- [ ] `coordL_singleL : coordL i ∘ₗ singleL j = if i = j then id else 0`
- [ ] `dilProj_isSymmetric`
- [ ] `dilProj_idempotent`
- [ ] `dilProj_orthogonal : i ≠ j → dilProj i ∘ₗ dilProj j = 0`
- [ ] `dilProj_sum_eq_one : ∑ i, dilProj i = 1`

## N3 — La dilation (Watrous Thm 2.42)
- [ ] `dilV_isometry : adjoint (dilV P) ∘ₗ dilV P = LinearMap.id`
- [ ] `naimark_dilation : ∀ i, adjoint (dilV P) ∘ₗ dilProj i ∘ₗ dilV P = P.E i`
- [ ] `theorem naimark` (assemblage des deux précédents)
- [ ] `naimark_born` (corollaire statistique : les probabilités coïncident)

## N4 — Clôture
- [ ] SORRIES.md à jour, `#print axioms naimark` vérifié (propext/choice/sound
      uniquement)
- [ ] README : énoncé, écart documenté vs Watrous (somme directe vs ⊗),
      mention explicite de l'assistance IA
- [ ] `git tag v1.0-naimark`, push --tags

## N5 — OPTIONNEL : version unitaire/ancilla (Paris Thm 4 / Watrous Cor. 2.43)
Nécessite un lemme non trivial et absent à ce jour : extension d'une isométrie
partielle `H n →ₗ K` en un unitaire global de `K`. L'esquisse de Paris
("identité sur l'orthogonal de ω_B") est insuffisante telle quelle — voir
CLAUDE.md. Bon candidat Mathlib si prouvé proprement.
- [ ] `exists_unitary_extension` (lemme général, isométries partielles dim finie)
- [ ] `naimark_projective_form` (Px, unitaire U, %B — la forme "ancilla" complète)

---

## Wigner — plan détaillé à venir une fois Naimark clos
(section à remplir)