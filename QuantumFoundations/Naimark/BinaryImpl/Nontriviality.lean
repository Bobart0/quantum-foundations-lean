import QuantumFoundations.Naimark.BinaryImpl.Nonvacuity

/-!
**FR.** # Non-trivialité : les distinctions du Module C ne sont pas vides de sens

Non-vacuité (`Nonvacuity.lean`) montre que les définitions sont
satisfiables ; non-trivialité montre en plus qu'elles savent DISTINGUER
des objets réellement différents -- sans quoi `StrictIso` pourrait, par
exemple, se révéler être la relation totale.

- `StrictIso` n'est PAS la relation totale : `canonicalBinaryImpl` et
  `canonicalTernaryImpl` du même effet `E := 1 : H 1 →ₗ H 1` ne sont
  JAMAIS strictement isomorphes, même après adjonction d'une ancilla
  répliquée arbitraire des deux côtés
  (`canonicalBinaryImpl_canonicalTernaryImpl_not_strictIso_replicatedAncilla`,
  `TernaryFusion.lean`).
- `StrictIsoInvariant` n'implique PAS `ReplicatedAncillaNeutral` :
  `ambientDimValuation` satisfait la première mais pas la seconde
  (`ambientDimValuation_not_replicatedAncillaNeutral`, `Valuation.lean`).
  Les deux notions de neutralité du Module C sont donc réellement
  distinctes, pas des reformulations l'une de l'autre.

**EN.** # Nontriviality: Module C's distinctions are not empty of meaning

Nonvacuity (`Nonvacuity.lean`) shows the definitions are satisfiable;
nontriviality further shows they can actually DISTINGUISH genuinely
different objects -- without which `StrictIso`, for instance, could turn
out to be the total relation.

- `StrictIso` is NOT the total relation: `canonicalBinaryImpl` and
  `canonicalTernaryImpl` of the same effect `E := 1 : H 1 →ₗ H 1` are
  NEVER strictly isomorphic, even after adjoining an arbitrary replicated
  ancilla on both sides
  (`canonicalBinaryImpl_canonicalTernaryImpl_not_strictIso_replicatedAncilla`,
  `TernaryFusion.lean`).
- `StrictIsoInvariant` does NOT imply `ReplicatedAncillaNeutral`:
  `ambientDimValuation` satisfies the former but not the latter
  (`ambientDimValuation_not_replicatedAncillaNeutral`, `Valuation.lean`).
  Module C's two neutrality notions are therefore genuinely distinct, not
  restatements of one another.
-/

namespace QuantumFoundations.Naimark.BinaryImpl

open QuantumFoundations Gleason
open scoped InnerProductSpace

noncomputable section

/-- `StrictIso` is not the total relation: the canonical binary and
ternary implementations of the identity effect on `H 1` are never
strictly isomorphic, even after adjoining arbitrarily large replicated
ancillas on both sides. -/
theorem strictIso_not_total :
    ∃ (a b : ℕ) (a₀ : Fin a) (b₀ : Fin b),
      ¬ BinaryImpl.StrictIso
        (replicatedAncillaImpl (canonicalBinaryImpl (1 : H 1 →ₗ[ℂ] H 1) (one_isEffect 1)) a₀)
        (replicatedAncillaImpl (canonicalTernaryImpl (1 : H 1 →ₗ[ℂ] H 1) (one_isEffect 1)) b₀) :=
  ⟨1, 1, 0, 0, canonicalBinaryImpl_canonicalTernaryImpl_not_strictIso_replicatedAncilla
    (1 : H 1 →ₗ[ℂ] H 1) (one_isEffect 1) (by norm_num) 0 0⟩

/-- The two neutrality notions of `Valuation.lean` are genuinely distinct:
`StrictIsoInvariant` does not entail `ReplicatedAncillaNeutral`. -/
theorem strictIsoInvariant_not_le_replicatedAncillaNeutral :
    ∃ (n : ℕ) (E : H n →ₗ[ℂ] H n) (v : ImplValuation n E),
      StrictIsoInvariant v ∧ ¬ ReplicatedAncillaNeutral v :=
  ⟨1, (1 : H 1 →ₗ[ℂ] H 1), ambientDimValuation,
    ambientDimValuation_strictIsoInvariant, ambientDimValuation_not_replicatedAncillaNeutral⟩

end

end QuantumFoundations.Naimark.BinaryImpl
