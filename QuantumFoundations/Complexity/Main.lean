import QuantumFoundations.Complexity.Counting
import QuantumFoundations.Complexity.RecordInterference

/-!
# C2 — Redundant-record lower bound for interference circuits

The theorem in this file is exact and finite-dimensional.  It concerns a
finite number of sites, finite local dimension, exact records on pairwise
disjoint regions, exact gates supported on at most two sites, and an exact
nonzero cross amplitude.

It does not address approximate-record robustness, distinguishability-
complexity upper bounds, the full Taylor–McCulloch criterion, persistence
under Hamiltonian evolution, Brown–Susskind complexity growth, or canonical
uniqueness of branch decompositions.
-/

namespace QuantumFoundations.Complexity

open scoped InnerProductSpace

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/--
**Explicit 2-local interference-circuit lower bound.**

Let `R` exact records of the same labeled resolution be localized in
pairwise disjoint spatial regions.  If a circuit of exact 2-local gates has
a nonzero matrix element from recorded branch `i` to the distinct recorded
branch `j`, then `R ≤ 2 * C.length`.

The family uses the existing Riedel indexing convention `Fin R`; hence `R`
is exactly its cardinality.
-/
theorem regions_card_le_two_mul_circuit_length_of_cross_amplitude_ne_zero
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (C : Circuit N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K) (ψ : H (d ^ N))
    (hrec : IsRecordedOn ψ recs) (i j : Fin K) (hij : i ≠ j)
    (hlocal : ∀ r, IsLocalTo (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : ∀ r r', r ≠ r' → Disjoint (regions r) (regions r'))
    (hcross : ⟪branch recs ψ j, Circuit.evalOnH C e (branch recs ψ i)⟫_ℂ ≠ 0) :
    R ≤ 2 * Circuit.length C := by
  have htouched : ∀ r, ¬ Disjoint (Circuit.support C) (regions r) := by
    intro r
    exact touched_of_cross_amplitude_ne_zero
      e C recs ψ hrec r (regions r) i j hij (hlocal r) hcross
  have hregions : Fintype.card (Fin R) ≤ (Circuit.support C).card :=
    regions_card_le_support_card regions (Circuit.support C) hpairwise htouched
  rw [Fintype.card_fin] at hregions
  exact hregions.trans (Circuit.circuit_support_card_le C)

#print axioms Circuit.circuit_commute_of_disjoint
#print axioms cross_amplitude_eq_zero_of_untouched_record
#print axioms regions_card_le_two_mul_circuit_length_of_cross_amplitude_ne_zero

end

end QuantumFoundations.Complexity
