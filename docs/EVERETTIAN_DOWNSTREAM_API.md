# Everettian downstream API

This branch adds additive, audited import surfaces for downstream repositories.
The existing `QuantumFoundations.ProbabilityAPI` contract and all prior
scientific modules remain unchanged.

## Four facades

- `QuantumFoundations.ProbabilityAPI` keeps the historical conditional and
  Born-rule-facing declarations.
- `QuantumFoundations.FiniteTensorAPI` exposes finite coordinate spaces,
  supplied bipartite factorizations, product vectors, transported operators,
  partial traces, and reduced operators.
- `QuantumFoundations.SelectorBridgeAPI` exposes the selector bridges and the
  strict ancilla-neutrality and tensor-multiplicativity classifications.
- `QuantumFoundations.NaimarkImplementationAPI` exposes the binary
  implementation classification and residual-neutral valuation results.

The combined `QuantumFoundations.EverettianAPI` is only an additive import
facade. It does not flatten the namespaces or introduce a new theorem.

## Coordinates and factorization

The internal tensor convention is environment-first:

```text
BipartiteSpace system environment
  = EuclideanSpace ℂ (Fin environment × Fin system)
```

`SuppliedBipartiteFactorization ambient system environment` is an explicitly
provided linear isometric equivalence. It makes no existence, uniqueness, or
physical-preference claim. Consequently, generic reduced-operator statements
do not assume `ambient = system * environment` unless a conversion to the
older `TensorDecomposition` is being used.

`TensorDecomposition.toSuppliedFactorization` and
`SuppliedBipartiteFactorization.toTensorDecomposition` provide the transparent
round-trip at ambient dimension `system * environment`, together with product,
operator-transport, and reduced-operator compatibility lemmas.

## System-first adapter

`SystemEnvironmentSpace system environment` uses
`Fin system × Fin environment`. The explicit index swap and its unitary are
only convention adapters; all tensor and partial-trace implementation remains
environment-first. `SystemEnvironmentFactorization` converts to and from the
supplied environment-first factorization, and the round-trip laws are public.

The terminology aliases `EnvironmentPartialTrace` and
`partialTraceEnvironment` are synonyms for the existing environment partial
trace. No reduced probabilistic state, entanglement predicate, channel,
dynamics, or decoherence model is introduced by this API.

## Neutrality boundaries

Selector ancilla neutrality is a property of a supplied tensor decomposition
and a selector family. Naimark residual neutrality is a property of valuations
under event and complement residual extensions. The facades expose both
contracts while keeping them separate; neither is identified with the other,
and no preferred tensor factorization is inferred.

## Migration sequence

Downstream code can migrate incrementally:

1. keep the existing probability import and names;
2. replace direct finite-tensor implementation imports with
   `FiniteTensorAPI`;
3. use `SystemEnvironmentFactorization` when source code is system-first;
4. replace selector bridge implementation imports with `SelectorBridgeAPI`;
5. replace direct binary-implementation imports with
   `NaimarkImplementationAPI`;
6. use `EverettianAPI` only when all four surfaces are required.

Each contract file under `QuantumFoundations/Audit/` imports only the facade it
tests (or only the aggregate facade for the aggregate contract), and includes
the relevant `#print axioms` checks. No new dependency is required.

## Packaging and CI contract

The four public facades are declared explicitly in the `globs` of the Lake
library: `FiniteTensorAPI`, `SelectorBridgeAPI`,
`NaimarkImplementationAPI`, and `EverettianAPI`. The root
`QuantumFoundations.lean` imports the aggregate facade additively; no facade
imports the root.

The four leaf contracts are compiled individually in CI, and
`QuantumFoundations/Audit/EverettianDownstreamContracts.lean` provides one
aggregate audit target. An external Lake consumer smoke test compiles each
facade separately, once through a local path dependency and once through the
pushed Git SHA on push events. These checks validate package exposure without
changing the historical `ProbabilityAPI` contract.

Local commands:

```sh
python scripts/check_downstream_api_consumer.py --source-path .
```

The temporary consumer package is deleted by default. Pass `--keep-temp` to
retain it for diagnosis after a failure. This packaging pass migrates no
downstream repository; downstream migrations remain open.

For a published revision, the equivalent Git dependency check is:

```sh
python scripts/check_downstream_api_consumer.py \
  --git-url https://github.com/Bobart0/quantum-foundations-lean.git \
  --rev <published-sha>
```
