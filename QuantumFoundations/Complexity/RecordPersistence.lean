import QuantumFoundations.Complexity.Persistence
import QuantumFoundations.Complexity.BranchGap

/-!
# C7d — Redundant-record conditional persistence bounds

The exact redundant-record lower bound and supplied phase-readout upper bound
feed directly into the general reversible-evolution certificate.  This gives
a finite, conditional circuit-complexity persistence statement only; it says
nothing about approximate records or continuous-time dynamics.
-/

namespace QuantumFoundations.Complexity

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- Exact redundant-record proxy gaps persist through a finite reversible
evolution whenever the initial record budget covers twice the general
conjugation overhead. -/
theorem redundant_records_gap_persists_under_reversible_evolution
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K) (ψ : H (d ^ N))
    (hrec : IsRecordedOn ψ recs) (r₀ : Fin R) (i j : Fin K) (hij : i ≠ j)
    (hi : branch recs ψ i ≠ 0) (hj : branch recs ψ j ≠ 0)
    (hlocal_i : ∀ r, IsLocalTo (transportedRecordProj e (recs r) i) (regions r))
    (hlocal_j : ∀ r, IsLocalTo (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : ∀ r r', r ≠ r' → Disjoint (regions r) (regions r'))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (D : Circuit N d) (hD : ImplementsRecordPhaseFlip e D (recs r₀) j)
    (Evo : ReversibleCircuitEvolution N d) (g : ℕ)
    (hbudget : Circuit.length D + 2 * Evo.overhead + g ≤ ceilHalf R) :
    HasProxyGapAtLeast e
      (Circuit.evalOnH Evo.forward e (normalizedBranch recs ψ i))
      (Circuit.evalOnH Evo.forward e (normalizedBranch recs ψ j)) δ g := by
  have hI := redundant_records_give_interference_lower_bound
    e regions recs ψ hrec i j hij hi hj hlocal_i hlocal_j hpairwise δ hδ0
  have hDist := record_phase_flip_gives_distinguishability_upper_bound
    e recs ψ hrec r₀ i j hij hi hj δ hδ0.le hδ1 D hD
  exact proxy_gap_persists_of_explicit_bounds Evo e
    (normalizedBranch recs ψ i) (normalizedBranch recs ψ j) δ
    (ceilHalf R) (Circuit.length D) hI hDist g hbudget

/-- For canonical circuit evolution the backward circuit has equal length,
so `overhead = 2 * E.length` and the gap budget loses `4 * E.length`. -/
theorem redundant_records_gap_persists_under_circuit_evolution
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K) (ψ : H (d ^ N))
    (hrec : IsRecordedOn ψ recs) (r₀ : Fin R) (i j : Fin K) (hij : i ≠ j)
    (hi : branch recs ψ i ≠ 0) (hj : branch recs ψ j ≠ 0)
    (hlocal_i : ∀ r, IsLocalTo (transportedRecordProj e (recs r) i) (regions r))
    (hlocal_j : ∀ r, IsLocalTo (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : ∀ r r', r ≠ r' → Disjoint (regions r) (regions r'))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (D : Circuit N d) (hD : ImplementsRecordPhaseFlip e D (recs r₀) j)
    (E : Circuit N d) (g : ℕ)
    (hbudget : Circuit.length D + 4 * Circuit.length E + g ≤ ceilHalf R) :
    HasProxyGapAtLeast e
      (Circuit.evalOnH E e (normalizedBranch recs ψ i))
      (Circuit.evalOnH E e (normalizedBranch recs ψ j)) δ g := by
  let Evo := ReversibleCircuitEvolution.ofCircuit E
  have hbudget' : Circuit.length D + 2 * Evo.overhead + g ≤ ceilHalf R := by
    rw [show Evo.overhead = 2 * Circuit.length E from
      ReversibleCircuitEvolution.overhead_ofCircuit E]
    omega
  exact redundant_records_gap_persists_under_reversible_evolution
    e regions recs ψ hrec r₀ i j hij hi hj hlocal_i hlocal_j hpairwise
    δ hδ0 hδ1 D hD Evo g hbudget'

/-- Budgeting one surviving unit of proxy gap gives a nontrivial exact
separation certificate after canonical finite circuit evolution. -/
theorem redundant_records_remain_nontrivially_separated
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K) (ψ : H (d ^ N))
    (hrec : IsRecordedOn ψ recs) (r₀ : Fin R) (i j : Fin K) (hij : i ≠ j)
    (hi : branch recs ψ i ≠ 0) (hj : branch recs ψ j ≠ 0)
    (hlocal_i : ∀ r, IsLocalTo (transportedRecordProj e (recs r) i) (regions r))
    (hlocal_j : ∀ r, IsLocalTo (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : ∀ r r', r ≠ r' → Disjoint (regions r) (regions r'))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (D : Circuit N d) (hD : ImplementsRecordPhaseFlip e D (recs r₀) j)
    (E : Circuit N d)
    (hbudget : Circuit.length D + 4 * Circuit.length E + 1 ≤ ceilHalf R) :
    HasProxyGapAtLeast e
      (Circuit.evalOnH E e (normalizedBranch recs ψ i))
      (Circuit.evalOnH E e (normalizedBranch recs ψ j)) δ 1 :=
  redundant_records_gap_persists_under_circuit_evolution
    e regions recs ψ hrec r₀ i j hij hi hj hlocal_i hlocal_j hpairwise
    δ hδ0 hδ1 D hD E 1 hbudget

#print axioms redundant_records_gap_persists_under_reversible_evolution
#print axioms redundant_records_gap_persists_under_circuit_evolution

end

end QuantumFoundations.Complexity
