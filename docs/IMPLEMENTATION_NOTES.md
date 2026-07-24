# Implementation Notes

This document preserves information useful to anyone extending or
re-implementing parts of this formalization: representation choices,
performance-sensitive proof architecture, dependency boundaries, Mathlib
API conventions, and known elaboration constraints. It intentionally does
not preserve a chronological narrative of how the project was developed;
that history remains in `MILESTONES.md` and `ARCHITECTURE_NOTES.md` for
readers who want it.

## Representation choices

- **Flat direct sum over nested `PiLp` or `TensorProduct`.** The Naimark
  dilation space is represented as `DilSpace n m := EuclideanSpace ℂ
  (Fin m × Fin n)` (a single flat index) rather than as
  `PiLp 2 (fun _ : Fin m => H n)` (a nested nested indexing) or an abstract
  `TensorProduct`. Both flat and nested versions were viable at equal proof
  cost; the flat version was chosen because its single index type
  `Fin m × Fin n` avoids extra `WithLp`/`.ofLp` coercion layers in the
  isometry and projection-family proofs. The same choice (a flat
  `EuclideanSpace ℂ ((Fin N) → Fin d)` multi-site model, rather than an
  abstract tensor product) is reused in `BranchesRiedel/Local.lean` for
  consistency.
- **Total definitions with junk values, rather than proof-carrying
  arguments.** Definitions whose natural domain of validity depends on a
  hypothesis (for instance, a construction that is only meaningful for
  `n ≥ 1`) are defined as total functions with an explicit junk value
  outside their intended domain (following the pattern of `Real.sqrt`),
  with separate specification lemmas stated under the relevant hypothesis.
  A proof is never taken as an argument to a definition where a total
  definition is available; this keeps definitional unfolding predictable
  and avoids threading proof terms through unrelated code.
- **Subtype effects, not a bespoke positivity predicate.** `Effect n` in
  `BornRule.EffectPerspectives` is a subtype of `Gleason.IsEffect`, reusing
  the pinned dependency's own positivity notion (`IsPositiveOp`,
  `IsEffect := IsPositiveOp T ∧ IsPositiveOp (1 - T)`) rather than
  redefining positivity locally.

## Performance-sensitive proof architecture

- **Generalize large rewritten expressions under an opaque name before
  further rewriting.** When a `rw` substitutes a large expression (for
  instance an indexed sum) that subsequent rewrites must traverse, the
  large expression is generalized under an opaque local name immediately,
  rather than left inline, to keep later rewrites fast and their goals
  legible.
- **Isolate heavy lemma compositions in a minimal-context private lemma.**
  Assembling several already-proved lemmas directly at the call site,
  especially when Lean must infer several metavariables simultaneously,
  can be dramatically slower than isolating the same composition as a
  standalone private lemma stated with minimal ambient context, then
  applying that lemma as an ordinary function at each call site. One
  recorded instance of this pattern reduced an assembly step from 307
  seconds to 29 seconds by extracting a minimal-context private lemma
  (referred to elsewhere in this repository's history as the
  `riesz_rep_assembly` lesson); the same pattern was applied again in the
  Naimark unitary-extension development (`Naimark/Unitary.lean`), where
  composing
  `(orthonormal_family ...).exists_orthonormalBasis_extension_of_card_eq`
  inline inside an `obtain` triggered a deterministic timeout at `whnf`,
  resolved by isolating the combined statement
  (`orthonormalBasisExtension`) as its own private lemma and then applying
  it as a function to each concrete case.
- **`maxHeartbeats` is set to a finite, locally scoped value only, never to
  `0`.** Exceeding a bounded heartbeat limit is treated as a signal to
  restructure the proof (extract a private lemma, `generalize` a subterm),
  not as a reason to disable the limit.
- **Constrain `simp` explicitly.** Assemblies use `simp only [...]` with an
  explicit lemma list; a bare `simp [mul_comm]` (or similarly unconstrained
  call including a commutativity lemma) is avoided because it is a known
  source of simp-set loops.

## Dependency boundaries

- The pinned `gleason-theorem-lean` dependency is reused at different
  depths in different subsystems: `Naimark` reuses only
  `Gleason.IsPositiveOp`, a plain `Prop`; `Uhlhorn` and `BornRule` invoke
  `Gleason.gleason` itself, along with substantial internal machinery
  (`Gleason.positive_inner_self_eq_zero`, `Gleason.cframe_sum_invariant`,
  `Gleason.ProjMeasure`/`bornValue`/`projL`,
  `Submodule.starProjection_isSymmetric`); `BornRule.EffectPerspectives`
  additionally reuses `Gleason.Busch.Effects`/`Gleason.Busch.Main`
  (`Gleason.IsEffect`, `Gleason.EffectMeasure`,
  `Gleason.busch`/`Gleason.busch_born_rule`). In every case the dependency
  is invoked, never reproduced; `#print axioms` on every downstream
  theorem confirms no additional axiom is introduced by this broader
  reuse.
- Within `H n →ₗ[ℂ] H n`, proofs remain in terms of `LinearMap.IsSymmetric`
  and `LinearMap.adjoint` rather than `ContinuousLinearMap`/`star`, which
  is legitimate because every space involved is finite-dimensional; the
  continuous/star API is used only where a specific Mathlib lemma requires
  it.

## Mathlib API conventions worth checking before use

- The direction of `LinearMap.adjoint_inner_left`/`_right` and the
  linearity convention of `⟪·,·⟫_ℂ` (conjugate-linear in which argument)
  are worth confirming directly against the installed Mathlib version
  before relying on them in a new proof, since both are easy to misapply
  from memory.
- `inner_conj_symm a b`'s convention was confirmed empirically (via
  compiler error messages showing the actual inferred types) to be
  `starRingEnd 𝕜 ⟪b, a⟫ = ⟪a, b⟫`, i.e. `conj ⟪b, a⟫ = ⟪a, b⟫`; the
  reversed direction is a natural but incorrect assumption.
- ℝ-vs-ℂ scalar casts recur throughout the inner-product developments;
  confirming the exact cast lemma needed (`Complex.ofReal_re`,
  `inner_self_eq_norm_sq_to_K`, `norm_cast`, and similar) against a small
  standalone goal before committing to a larger proof avoids repeated
  rework.

## Known elaboration constraints

- **`Fin (opaque-def).outcomes` numeral synthesis.** A bare numeral (`0`,
  `1`, `2`) used as an argument whose type is a `Fin k` derived from an
  opaque structure-field definition (for instance `Fin D.outcomes` for an
  abstract `D`) can fail `OfNat` instance synthesis, because Lean does not
  unfold plain `def`s during instance search even when the type is
  definitionally a concrete `Fin k`. This was encountered repeatedly in
  `BornRule.EffectPerspectives`. The stable fixes are: explicit type
  ascription (`(0 : Fin 2)`) in the statement of a theorem or `have`;
  `show`/`change` to force full-transparency defeq reduction of the goal
  before applying a lemma that needs to syntactically recognize a concrete
  `Fin k` (such as `Fin.sum_univ_two`/`_three`); and local private
  `finN_cases` helper lemmas (`x = 0 ∨ x = 1 ∨ ⋯`) used with
  `rcases ... with rfl | rfl | ⋯`, which substitute via `rfl` and yield
  clean `OfNat`-literal forms, rather than raw `fin_cases`, which produces
  `⟨0, ⋯⟩` (`Fin.mk`) terms that do not match `simp` lemmas stated for
  clean literals.
- **Big-operator sum-body over-capture.** `∑ k, BODY` notation greedily
  extends its body across a multi-line expression; an unparenthesized
  multi-line sum can accidentally absorb a trailing equality into its own
  body, producing a confusing type mismatch. Fully parenthesizing each
  multi-line sum expression avoids this.
- **`obtain`/`refine` composing several heavyweight lemmas with
  metavariables to infer can time out at `whnf`.** This is not necessarily
  a sign of proof difficulty; see "Performance-sensitive proof
  architecture" above for the standard remedy (isolate the composed
  statement as a private lemma, apply it as a function).
- **`trans MIDDLE`** is a robust way to split an `LHS = RHS` goal into two
  independently provable subgoals without needing an intermediate term to
  syntactically match an ambient, possibly opaque-typed, goal; it was used
  repeatedly in place of more fragile directional `rw` sequences throughout
  `BornRule.EffectPerspectives`.
