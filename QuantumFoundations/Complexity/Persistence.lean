import QuantumFoundations.Complexity.ProxyTransport
import QuantumFoundations.Complexity.ProxyCertificates

/-!
# C7c — Conditional transport of relational proxy certificates

These theorems are entirely subtraction-free.  A reversible conjugation adds
one `overhead` to a distinguishing witness and one `overhead` when an evolved
interference circuit is pulled back.  Consequently a certified proxy gap can
degrade by at most twice that overhead.
-/

namespace QuantumFoundations.Complexity

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- A distinguishing witness can be pushed forward at additive cost equal to
the reversible conjugation overhead. -/
theorem distinguishability_upper_bound_under_evolution
    (Evo : ReversibleCircuitEvolution N d)
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N))
    (δ : ℝ) (D : ℕ)
    (hD : HasDistinguishabilityUpperBound e a b δ D) :
    HasDistinguishabilityUpperBound e
      (Circuit.evalOnH Evo.forward e a)
      (Circuit.evalOnH Evo.forward e b) δ (D + Evo.overhead) := by
  obtain ⟨C, hlen, hC⟩ := hD
  refine ⟨Evo.pushForward C, ?_, ?_⟩
  · rw [Evo.pushForward_length_eq]
    omega
  · exact (Evo.distinguishesAt_pushForward_iff C e a b δ).mp hC

/-- Primitive subtraction-free interference transport: an evolved
interference circuit, plus the cost of pulling it back, satisfies the initial
lower bound. -/
theorem interference_lower_bound_transport
    (Evo : ReversibleCircuitEvolution N d)
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N))
    (δ : ℝ) (B : ℕ)
    (hI : HasInterferenceLowerBound e a b δ B)
    (C : Circuit N d)
    (hC : InterferesAt e
      (Circuit.evalOnH Evo.forward e a)
      (Circuit.evalOnH Evo.forward e b) δ C) :
    B ≤ Circuit.length C + Evo.overhead := by
  have hPull : InterferesAt e a b δ (Evo.pullBack C) :=
    (Evo.interferesAt_pullBack_iff C e a b δ).mp hC
  have hbound := hI (Evo.pullBack C) hPull
  rwa [Evo.pullBack_length_eq] at hbound

/-- If `B' + overhead ≤ B`, the initial lower bound `B` yields the evolved
lower bound `B'`. -/
theorem interference_lower_bound_under_evolution
    (Evo : ReversibleCircuitEvolution N d)
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N))
    (δ : ℝ) (B : ℕ)
    (hI : HasInterferenceLowerBound e a b δ B)
    (B' : ℕ) (hbudget : B' + Evo.overhead ≤ B) :
    HasInterferenceLowerBound e
      (Circuit.evalOnH Evo.forward e a)
      (Circuit.evalOnH Evo.forward e b) δ B' := by
  intro C hC
  have htransport := interference_lower_bound_transport
    Evo e a b δ B hI C hC
  omega

/-- Core persistence theorem from explicit initial lower and upper bounds.
The gap budget loses exactly two reversible-conjugation overheads. -/
theorem proxy_gap_persists_of_explicit_bounds
    (Evo : ReversibleCircuitEvolution N d)
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N))
    (δ : ℝ) (B D : ℕ)
    (hI : HasInterferenceLowerBound e a b δ B)
    (hD : HasDistinguishabilityUpperBound e a b δ D)
    (g : ℕ) (hbudget : D + 2 * Evo.overhead + g ≤ B) :
    HasProxyGapAtLeast e
      (Circuit.evalOnH Evo.forward e a)
      (Circuit.evalOnH Evo.forward e b) δ g := by
  let B' := D + Evo.overhead + g
  let D' := D + Evo.overhead
  refine ⟨B', D', ?_, ?_, ?_⟩
  · apply interference_lower_bound_under_evolution Evo e a b δ B hI B'
    dsimp [B']
    omega
  · exact distinguishability_upper_bound_under_evolution Evo e a b δ D hD
  · dsimp [B', D']
    omega

/-- A pre-existing gap certificate of size `g + 2 * overhead` transports to
a gap certificate of size `g` after the reversible evolution. -/
theorem proxy_gap_persists_under_reversible_evolution
    (Evo : ReversibleCircuitEvolution N d)
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N))
    (δ : ℝ) (g : ℕ)
    (hgap : HasProxyGapAtLeast e a b δ (g + 2 * Evo.overhead)) :
    HasProxyGapAtLeast e
      (Circuit.evalOnH Evo.forward e a)
      (Circuit.evalOnH Evo.forward e b) δ g := by
  obtain ⟨B, D, hI, hD, hbudget⟩ := hgap
  apply proxy_gap_persists_of_explicit_bounds Evo e a b δ B D hI hD g
  omega

#print axioms proxy_gap_persists_of_explicit_bounds
#print axioms proxy_gap_persists_under_reversible_evolution

end

end QuantumFoundations.Complexity
