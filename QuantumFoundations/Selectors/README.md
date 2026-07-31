# Selectors — unitary covariance, null succession, and single-effect classification

**FR.** Sous-module interprétativement neutre : rien d'everettien n'entre
ici. Il étudie les **sélecteurs** — applications état pur ↦ opérateur
densité — sous deux angles indépendants : (1) ce que la seule covariance
unitaire laisse survivre, et une prémisse-pont qui la réduit à la règle de
Born ; (2) une classification complète des contraintes portant sur un seul
effet qui suffiraient, à elles seules, à sélectionner un état pur unique.

**EN.** Interpretively neutral submodule: nothing Everettian enters here.
It studies **selectors** — pure-state ↦ density-operator maps — from two
independent angles: (1) what unitary covariance alone leaves standing, and
a bridge premise that reduces it to the Born rule; (2) a complete
classification of single-effect constraints that would, on their own,
suffice to select a unique pure state.

## File-by-file map

| File | Milestone | Content |
|---|---|---|
| `Defs.lean` | S1 | `Selector`, `IsCovariant`, the candidate family `tDensity`/`tSelector` (isotropic/depolarizing), `bornSelector`, `NSNC1`; public reusable facts `projL_add_projL_compl`, `tDensity_apply_self`, `bornValue_add_bornValue_compl` |
| `Unitaries.lean` | S3 support | Sign reflections `reflIso` and basis transpositions `swapIso` fixing a chosen unit vector; unitary transitivity `exists_isometry_apply_eq` |
| `Covariance.lean` | S2 | `bornSelector_isCovariant`, `tSelector_isCovariant` (the whole one-parameter family is covariant — covariance alone does not isolate Born), `tDensity_conj` |
| `Classification.lean` | S3 | `covariant_iff_tSelector` — the classification theorem: `IsCovariant σ ↔ σ` belongs to the `tDensity` family, via the stabilizer of the vector `ψ` (reflections + transpositions), no Schur's lemma |
| `Pinning.lean` | S4/S5 | `nsnc1_iff_born` (NSNC-1 ⟺ Born, without covariance), `tSelector_nsnc1_iff_t_eq_one` (NSNC-1 pins `t = 1` on the candidate family), `covariant_and_nsnc1_iff_born` (closing assembly); `apply_eq_zero_of_quadratic_eq_zero` (public, reused by S6) |
| `Nonvacuity.lean` | — | `Selector n`, `IsCovariant`, `NSNC1` inhabited; the witness that matters: `tSelector 2 _ (1/2) _ _` is covariant but does not satisfy NSNC-1 |
| `SingleEffect.lean` | S6 | Proposition 2: `single_effect_selector_iff`, the extremal-eigenpair classification of single-effect constraints, plus corollaries |

## Two independent results, not one

The covariance classification (S2/S3) and the single-effect classification
(S6) answer different questions and share no premise:

- **Covariance** (`Classification.lean`): among selectors covariant under
  the full unitary group, which ones exist? Answer: exactly the isotropic
  family `tDensity`, one real parameter `t ∈ [0,1]`.
- **Null succession** (`Pinning.lean`): among covariant selectors, `NSNC1`
  picks out exactly `t = 1`, the Born rule.
- **Single effect** (`SingleEffect.lean`): dropping covariance entirely,
  which constraints of the form `Re tr(ρE₀) = c`, on a single fixed
  effect `E₀`, force `ρ` to be a specific pure state, for *every* density
  `ρ`? Answer: exactly when `(ψ, c)` is a simple extremal eigenpair of
  `E₀`. `NSNC1` itself is recovered as the special case
  `E₀ = P_{ψ⊥}`, `c = 0` (`nsnc1_iff_born_from_proposition_two`).

Neither classification is used to prove the other. `tDensity` is not the
generic object appearing in Proposition 2's convex mixtures (those use
plain two-term convex combinations of pure projectors, built ad hoc for
the straddling argument); the coincidence at `E₀ = P_{ψ⊥}` is a genuine,
separately-proved corollary, not a reformulation.

## Proposition 2 in one paragraph

**FR.** Pour un effet `E₀`, un état unitaire `ψ`, et un réel `c` : la
contrainte `Re tr(ρE₀) = c` force `ρ = |ψ⟩⟨ψ|` pour toute matrice densité
`ρ` si et seulement si `ψ` engendre l'espace propre **simple** (dimension
exactement 1) d'une valeur propre **extrémale** (minimale ou maximale, au
sens du quotient de Rayleigh sur toute la sphère unité) de `E₀`, et `c` est
cette valeur propre. C'est un résultat de géométrie convexe/spectrale : il
décrit exhaustivement les contraintes à effet unique qui *suffiraient* à
isoler un état pur ; il ne prétend pas qu'une telle contrainte doive être
acceptée comme principe de chance.

**EN.** For an effect `E₀`, a unit state `ψ`, and a real `c`: the
constraint `Re tr(ρE₀) = c` forces `ρ = |ψ⟩⟨ψ|` for every density matrix
`ρ` if and only if `ψ` spans the **simple** (exactly one-dimensional)
eigenspace of an **extremal** (minimal or maximal, in the Rayleigh-quotient
sense over the whole unit sphere) eigenvalue of `E₀`, and `c` is that
eigenvalue. This is a convex/spectral geometry result: it exhaustively
describes the single-effect constraints that *would suffice* to isolate a
pure state; it does not claim that any such constraint must be accepted as
a principle of chance.

Both halves of the extremality/simplicity hypothesis are necessary and are
witnessed by explicit non-selecting counter-models:

- **`P_{ψ⊥}`, `c = 0`** (`orthogonal_complement_projection_single_effect_selector`):
  the simple null minimum. Connects to S4 via
  `nsnc1_iff_born_from_proposition_two`.
- **`P_ψ`, `c = 1`** (`pure_state_projection_single_effect_selector`): the
  simple unit maximum.
- **A non-extremal (interior) value never selects**
  (`no_single_effect_selector_of_straddled`, instantiated concretely at
  `n = 2` in `interior_value_does_not_select`): if `c` lies strictly
  between the quadratic-form values attained at two unit vectors, no
  density — pure or mixed — is uniquely picked out.
- **A degenerate (non-simple) extremal eigenspace never selects either**
  (`identity_degenerate_extremum_does_not_select`): the identity operator
  attains its (trivially extremal) eigenvalue `1` on the whole space, not
  on a single line, for `n ≥ 2`.

## Proof architecture of `single_effect_selector_iff`

**Extremal ⟹ selects** reuses the general spectral-support lemma
`density_supported_on_kernel_of_extremal_trace`: for a *positive* operator
`A` and a density `ρ` with `Re tr(ρA) = 0`, expanding the trace on `A`'s
own eigenbasis (`LinearMap.IsSymmetric.eigenvectorBasis`) as a sum of
nonnegative real terms forces `ρ` to vanish outside `ker A`. Applied to
`A := E₀ - cI` (minimum case) or `A := cI - E₀` (maximum case), and
combined with `ker A = ℂ∙ψ` (simplicity), this pins `ρ = |ψ⟩⟨ψ|` via the
existing `QuantumFoundations.BornRule.eq_projL_of_vanishes_on_orthogonal`.
This direction builds directly on `apply_eq_zero_of_quadratic_eq_zero`
(S4), not reproved here.

**Selects ⟹ extremal** does *not* use a purity argument
(`tr(ρ²) < 1`) — deliberately avoided, since it would require a cross-trace
overlap formula between pure projectors and a strict Cauchy–Schwarz
inequality neither present nor needed elsewhere in this repository.
Instead: if `q(x) := Re⟪E₀x,x⟩` straddles `c` at two unit vectors `x, y`,
build the explicit convex density `ρ = t·P_x + (1-t)·P_y` matching the
constraint, and distinguish it from `P_ψ` using a *direct orthogonal
witness* `z := (ℂ∙ψ)ᗮ.starProjection x`: `⟪x,z⟩ = ⟪z,z⟩ = ‖z‖² > 0` purely
from the orthogonal decomposition `x = (x-z) + z`, no Cauchy–Schwarz. A
pure order dichotomy then upgrades "no straddling" to a one-sided global
bound, quadratic homogeneity extends it from the unit sphere to all
vectors, and the eigenequation (again via
`apply_eq_zero_of_quadratic_eq_zero`) plus a one-vector uniqueness
argument close the loop.

## What is not claimed

- The `tDensity` family of S2/S3 is the well-known isotropic/depolarizing
  family in quantum information; the contribution, if any, is in the
  assembly (the classification theorem and the pinning by `NSNC1`), not in
  the pieces.
- Covariance itself is never derived — it is a hypothesis studied, not
  established from anything more primitive.
- Nothing here is stated or proved in infinite dimension.
- Proposition 2 is a statement about which mathematical constraints
  *would* select a pure state; it takes no position on whether any
  specific effect/value pair is physically realized, privileged, or
  should be adopted as a probability postulate.
